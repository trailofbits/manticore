import ctypes
import logging
import os

from collections import defaultdict

import capstone as cs

from .x86 import AMD64Operand

from .abstractcpu import Cpu, RegisterFile, Operand, Syscall
from .cpufactory import CpuFactory
from ...core.cpu.disasm import BinjaILDisasm
from ..smtlib import Operators, BitVecConstant, operator
from ...utils.helpers import issymbolic
from functools import reduce

logger = logging.getLogger(__name__)
register_logger = logging.getLogger('{}.registers'.format(__name__))


class BinjaRegisterFile(RegisterFile):

    def __init__(self, arch, platform_regs):
        from binaryninja import Architecture
        self.arch = arch
        arch = Architecture[arch]
        self.reg_aliases = {
            'STACK': str(arch.stack_pointer),
            'PC': self.get_pc(),
            'CS': 'cs',
            'SS': 'ss',
            'DS': 'ds',
            'ES': 'es'
        }
        super(BinjaRegisterFile, self).__init__(aliases=self.reg_aliases)

        # Get "dummy" registers for flags. We append 'F' for consistency
        # with the X86 CPU
        f_regs = [f + "f" for f in arch.flags]
        # get (full width) architecture registers
        arch_regs = list(set([arch.regs[r].full_width_reg
                              for r in arch.regs.keys()]))

        self.pl2b_map, self.b2pl_map = binja_platform_regmap(arch_regs,
                                                             f_regs,
                                                             self.reg_aliases,
                                                             platform_regs)

        new_aliases = filter(lambda x: (x[0] not in self.reg_aliases.keys() and
                                        x[1] is not None and
                                        not isinstance(x[1], tuple)),
                             self.pl2b_map.items())
        self.reg_aliases.update(new_aliases)

        # all regs are: architecture, aliases and flags
        all_regs = arch_regs + self.reg_aliases.values() + f_regs
        self.registers = {reg: 0 for reg in all_regs}

        # FIXME get these from the platform!! they are already part of registers
        self.segment_registers = (['cs', 'ds', 'es', 'ss'] +
                                  ['fs', 'gs', 'fsbase', 'gsbase'])

    def write(self, reg, value):
        from binaryninja.enums import ImplicitRegisterExtend
        from binaryninja import Architecture

        arch = Architecture[self.arch]
        r = self._alias(str(reg))
        # if this is a custom register just write to the dictionary
        if r not in arch.regs:
            self.registers[r] = value
            return

        # get the ILRegister object from Architecture
        ilreg = arch.regs.get(r, None)
        if ilreg is None:
            raise NotImplementedError

        # full_width -> just write to it
        if ilreg.full_width_reg == r:
            self.registers[r] = value
            return

        ilreg_full = arch.regs[ilreg.full_width_reg]
        full_width_reg_value = self.registers[ilreg.full_width_reg]
        if ilreg.extend == ImplicitRegisterExtend.NoExtend:
            # mask off the value that will be replaced
            mask = (1 << ilreg.size * 8) - 1
            full_mask = (1 << ilreg_full.size * 8) - 1
            reg_bits = mask << (ilreg.offset * 8)
            full_width_reg_value &= full_mask ^ reg_bits
            full_width_reg_value |= value << ilreg.offset * 8
        elif ilreg.extend == ImplicitRegisterExtend.ZeroExtendToFullWidth:
            full_width_reg_value = value
        elif ilreg.extend == ImplicitRegisterExtend.SignExtendToFullWidth:
            full_width_reg_value = (
                (value ^ ((1 << ilreg.size * 8) - 1)) -
                ((1 << ilreg.size * 8) - 1) +
                (1 << ilreg_full.size * 8)
            )
        else:
            raise NotImplementedError

        self.registers[ilreg.full_width_reg] = full_width_reg_value
        # FIXME apply a mask here instead of doing it inside the instructions
        return full_width_reg_value

    def read(self, reg):
        from binaryninja import Architecture

        arch = Architecture[self.arch]
        r = self._alias(str(reg))
        if r in self.registers:
            return self.registers[r]

        reg_info = arch.regs.get(r)
        if reg_info is None:
            # don't raise here because we could be reading from a
            # temp register which won't be in the architecture registers
            return 0

        full_reg_value = self.registers[reg_info.full_width_reg]
        mask = (1 << reg_info.size * 8) - 1
        reg_bits = mask << (reg_info.offset * 8)
        reg_value = (full_reg_value & reg_bits) >> (reg_info.offset * 8)
        # FIXME apply a mask here instead of doing it inside the instructions
        return reg_value

    @property
    def all_registers(self):
        return tuple(self.registers.keys() + self._aliases.keys())

    @property
    def canonical_registers(self):
        return tuple(self.registers.keys())

    def __contains__(self, register):
        return register in self.all_registers

    def get_pc(self):
        if self.arch == 'x86':
            return 'eip'
        elif self.arch == 'x86_64':
            return 'rip'
        else:
            raise NotImplementedError


class BinjaOperand(Operand):
    def __init__(self, cpu, parent_il, op, **kwargs):
        self.llil = parent_il
        if hasattr(op, "operands"):
            op.operands = [BinjaOperand(cpu, op, x) for x in op.operands]
        super(BinjaOperand, self).__init__(cpu, op, **kwargs)

    @property
    def type(self):
        from binaryninja import lowlevelil as il
        type_map = {
            il.ILRegister: 'register',
            il.LowLevelILInstruction: 'instruction',
            il.ILFlag: 'flag',
        }

        try:
            t = type_map[type(self.op)]
        except KeyError as e:
            logger.error("ERROR IN type lookup " + str(type(self.op)))
            raise e
        return t

    @property
    def size(self):
        return self.op.info.size

    def read(self):
        import binaryninja.enums as enums

        cpu, op = self.cpu, self.op
        if self.type == 'register':
            return cpu.regfile.read(op.name)
        if self.type == 'flag':
            return cpu.regfile.registers[op.name + 'f']
        elif self.type == 'instruction':
            implementation = getattr(cpu, op.operation.name[len("LLIL_"):])
            return implementation(*op.operands)
        else:
            raise NotImplementedError("read_operand type", op.type)

    def write(self, value):
        cpu, op = self.cpu, self.op
        if self.type == 'register':
            return cpu.write_register(str(op), value)
        if self.type == 'flag':
            return cpu.write_register(op.name + 'f', value)
        elif self.type == 'instruction':
            implementation = getattr(cpu, op.operation.name[len("LLIL_"):])
            return implementation(*op.operands)
        else:
            raise NotImplementedError("write_operand type", op.type)

    def __getattr__(self, name):
        return getattr(self.op, name)


def _carry_ult(left, right):
    return Operators.ULT(left, right)


def _adjust_flag(result, left, right):
    return ((left ^ right) ^ result) & 0x10 != 0


def _zero_flag(res):
    return res == 0


def _sign_flag(res, size):
    mask = 1 << (size - 1)
    return (res & mask) != 0


def _parity_flag(v):
    return (v ^ v >> 1 ^ v >> 2 ^ v >> 3 ^ v >> 4 ^ v >> 5 ^ v >> 6 ^ v >> 7) & 1 == 0


def _overflow_flag(res, right, left, size):
    mask = 1 << (size - 1)
    sign_r = (right & mask) == mask
    sign_l = (left & mask) == mask
    sign_res = (res & mask) == mask
    return Operators.AND(sign_r ^ sign_l, sign_r ^ sign_res)


def binja_platform_regmap(binja_arch_regs, binja_arch_flags, binja_arch_aliases,
                          x86_cpu_regs):
    all_x86_regs = [r.lower() for r in x86_cpu_regs]

    # get all registers that are present already in the arch
    x86_to_binja = {r.upper(): r for r in all_x86_regs
                    if r in binja_arch_regs}

    # map flag registers
    for f in binja_arch_flags:
        x86_to_binja[f.upper()] = f
    x86_to_binja['IF'] = None

    x86_to_binja['RSP'] = binja_arch_aliases['STACK']
    x86_to_binja['RIP'] = binja_arch_aliases['PC']
    x86_to_binja['GS'] = 'gsbase'
    x86_to_binja['FS'] = 'fsbase'

    for f in set(x86_cpu_regs) - set(x86_to_binja.keys()):
        # no floating point or vector :/
        if f.startswith("YMM") or f.startswith("FP"):
            x86_to_binja[f.upper()] = None
        elif f[-1] == 'H':
            if f[:-1].lower() in binja_arch_regs:
                x86_to_binja[f] = (f[:-1].lower(), 'high')
            elif "r" + f[:-1].lower() in binja_arch_regs:
                x86_to_binja[f] = ("r" + f[:-1].lower(), 'high')
        elif f.upper() in binja_arch_aliases.keys():
            x86_to_binja[f.upper()] = f.upper()

    # still unmapped
    # x86_to_binja: ['EIP', 'IP', 'FRAME', 'EFLAGS', 'RFLAGS', 'TOP']
    # binja_to_x86: ['fs', 'gs', 'mmXX', 'stXX']
    binja_to_x86 = dict()
    binja_to_x86["high_mappings"] = []
    for x86_reg, binja_reg in x86_to_binja.items():
        if isinstance(binja_reg, tuple):
            binja_to_x86["high_mappings"].append(binja_reg[0])
        elif isinstance(binja_reg, str):
            binja_to_x86[binja_reg] = x86_reg

    return x86_to_binja, binja_to_x86


class BinjaCpu(Cpu):
    '''
    A Virtual CPU model for Binary Ninja's IL
    '''

    def __init__(self, memory):
        '''
        Builds a CPU model.
        :param arch: BinaryNinja arch.
        '''
        from binaryninja import Architecture

        # FIXME implement a generic architecture selector
        arch = Architecture['x86_64']
        if not hasattr(self, "platform_cpu"):
            # get a platform specific CPU
            # and mark it as non-virtual so as to not increment the PC in the
            # @instruction decorator
            self.platform_cpu = CpuFactory.get_cpu(memory, 'amd64')
            self.platform_cpu.real_cpu = False
        platform_regs = self.platform_cpu.all_registers
        self.max_instr_width = arch.max_instr_length
        self.address_bit_size = 8 * arch.address_size
        self.machine = self.platform_cpu.machine
        self.mode = self.platform_cpu.mode
        self.arch = arch
        self.program_path = None
        self.view = None
        self._segments = {}

        # initialize the memory and register files
        super(BinjaCpu, self).__init__(BinjaRegisterFile('x86_64',
                                                         platform_regs),
                                       memory,
                                       disasm="binja-il")

    def initialize_disassembler(self, program_path):
        import binaryninja as bn
        from binaryninja import BinaryView as bview
        from .disasm import BinjaILDisasm
        # see if we have cached the db
        db_name = "." + os.path.basename(program_path) + ".bnfm"
        dbpath = os.path.join(os.path.dirname(program_path), db_name)
        if not os.path.isfile(dbpath):
            bv = bn.binaryview.BinaryViewType.get_view_of_file(program_path)
            bv.update_analysis_and_wait()
            # cache for later
            bv.create_database(dbpath)
        else:
            fm = bn.FileMetadata()
            db = fm.open_existing_database(dbpath)
            vtypes = filter(lambda x: x.name != "Raw",
                            bview.open(program_path).available_view_types)
            bv = db.get_view_of_type(vtypes[0].name)
            bv.update_analysis_and_wait()
        self.program_path = program_path
        self.view = bv
        self.disasm = BinjaILDisasm(bv)

    def decode_instruction(self, pc):
        '''
        This will decode an instruction from memory pointed by `pc`

        :param int pc: address of the instruction
        '''
        text = ''
        # Read Instruction from memory
        for address in xrange(pc, pc + self.max_instr_width):
            # This reads a byte from memory ignoring permissions
            # and concretize it if symbolic
            if not self.memory.access_ok(address, 'x'):
                break

            c = self.memory[address]

            if issymbolic(c):
                assert isinstance(c, BitVec) and c.size == 8
                if isinstance(c, Constant):
                    c = chr(c.value)
                else:
                    logger.error('Concretize executable memory %r %r', c, text)
                    raise ConcretizeMemory(self.memory,
                                           address=pc,
                                           size=8 * self.max_instr_width,
                                           policy='INSTRUCTION')
            text += c

        # Pad potentially incomplete instruction with zeroes

        code = text.ljust(self.max_instr_width, '\x00')

        try:
            # decode the instruction from code
            insn = self.disasm.disassemble_instruction(code, pc)
        except StopIteration as e:
            raise DecodeException(pc, code)

        # Check that the decoded instruction is contained in executable memory
        if not self.memory.access_ok(slice(pc, pc + insn.size), 'x'):
            logger.info("Trying to execute instructions from non-executable memory")
            raise InvalidMemoryAccess(pc, 'x')

        # if we are executing Binja-IL but need to fallback to capstone,
        # bring all registers up to state, because they might be needed
        # during the creation of operands in wrap_operands
        if (isinstance(self.disasm, BinjaILDisasm) and
                isinstance(insn, cs.CsInsn)):
            self.update_platform_cpu_regs()

        insn.operands = self._wrap_operands(insn.operands)
        return insn

    def execute(self):
        '''
        Decode, and execute one instruction pointed by register PC
        '''
        if issymbolic(self.PC):
            raise ConcretizeRegister(self, 'PC', policy='ALL')

        if not self.memory.access_ok(self.PC, 'x'):
            raise InvalidMemoryAccess(self.PC, 'x')

        self._publish('will_decode_instruction', self.PC)

        insn = self.decode_instruction(self.PC)
        self._last_pc = self.PC

        self._publish('will_execute_instruction', insn)

        # FIXME (theo) why just return here?
        if insn.address != self.PC:
            return

        name = self.canonicalize_instruction_name(insn)

        def fallback_to_emulate(*operands):
            if (isinstance(self.disasm, BinjaILDisasm) and
                    isinstance(insn, cs.CsInsn)):
                # if we got a capstone instruction using BinjaILDisasm, it means
                # this instruction is not implemented. Fallback to Capstone
                self.FALLBACK(name, *operands)
                # XXX after this point self.PC != self._last_pc but that is
                # OK because we will update the PC  properly
            else:
                text_bytes = ' '.join('%02x' % x for x in insn.bytes)
                logger.info("Unimplemented instruction: 0x%016x:\t%s\t%s\t%s",
                            insn.address, text_bytes, insn.mnemonic, insn.op_str)

                self._publish('will_emulate_instruction', insn)
                self.emulate(insn)
                self._publish('did_emulate_instruction', insn)

        implementation = getattr(self, name, fallback_to_emulate)

        if logger.level == logging.DEBUG:
            logger.debug(self.render_instruction(insn))
            for l in self.render_registers():
                register_logger.debug(l)

        assert (self.PC == self._last_pc or
                (isinstance(insn, BinjaILDisasm.BinjaILInstruction) and
                 insn.sets_pc))

        implementation(*insn.operands)

        # In case we are executing IL instructions, we could iteratively
        # invoke multiple instructions due to the tree form, thus we only
        # want to increment the PC once, based on its previous position
        # for CALLS and JUMPS the PC should have been set automatically
        # so no need to do anything. Also, if there are pending instruction
        if not isinstance(self.disasm, BinjaILDisasm):
            return

        # don't bump the PC if we are in an LLIL that has set it,
        # or if there are pending IL insn in the queue. This is because
        # for cases where we have other il instructions in the queue,
        # such as when we get a divu insn, the PC + size will point
        # to the next assembly instruction and not the next LLIL
        #
        # we might be executing a Capstone instruction at this point
        # if we context-switched, so check the sets_pc attr
        if not (isinstance(insn, BinjaILDisasm.BinjaILInstruction) and
                (insn.sets_pc or self.disasm.il_queue)):
            self.PC = self._last_pc + insn.size

        self._icount += 1
        self._publish('did_execute_instruction', insn)

    def update_platform_cpu_regs(self):
        for pl_reg, binja_reg in self.regfile.pl2b_map.items():
            if isinstance(binja_reg, tuple) or binja_reg is None:
                continue
            self.platform_cpu.write_register(pl_reg,
                                             self.regfile.read(binja_reg))

    def render_instruction(self, insn=None):
        try:
            if (insn is None or
                    not isinstance(insn, BinjaILDisasm.BinjaILInstruction)):
                insn = self.instruction
                return "INSTRUCTION: 0x%016x:\t%s\t%s" % (insn.address,
                                                          insn.mnemonic,
                                                          insn.op_str)
            else:
                return str(insn)
        except Exception as e:
            return "{can't decode instruction}"

    @property
    def function_hooks(self):
        return dict(self._function_hooks)

    @property
    def instr_hooks(self):
        return defaultdict(list, self._instr_hooks)

    def __getstate__(self):
        state = super(BinjaCpu, self).__getstate__()
        state['segments'] = self._segments
        state['view_program_path'] = self.program_path

        state['max_instr_width'] = self.max_instr_width
        state['address_bit_size'] = self.address_bit_size
        state['machine'] = self.machine
        state['mode'] = self.mode
        # FIXME
        state['arch'] = 'x86_64'
        return state

    def __setstate__(self, state):
        from binaryninja import Architecture

        self._segments = state['segments']
        self.max_instr_width = state['max_instr_width']
        self.address_bit_size = state['address_bit_size']
        self.machine = state['machine']
        self.mode = state['mode']
        self.arch = Architecture[state['arch']]
        self.initialize_disassembler(state['view_program_path'])

        self.platform_cpu = CpuFactory.get_cpu(state['memory'], 'amd64')
        self.platform_cpu.real_cpu = False
        super(BinjaCpu, self).__setstate__(state)

    def canonicalize_instruction_name(self, insn):
        if isinstance(insn, BinjaILDisasm.BinjaILInstruction):
            return insn.name
        # fallback
        return self.platform_cpu.canonicalize_instruction_name(insn)

    def set_descriptor(self, selector, base, limit, perms):
        assert selector > 0 and selector < 0xffff
        assert base >= 0 and base < (1 << self.address_bit_size)
        assert limit >= 0 and limit < 0xffff or limit & 0xfff == 0
        self._segments[selector] = (base, limit, perms)

    def get_descriptor(self, selector):
        return self._segments.setdefault(selector, (0, 0xfffff000, 'rwx'))

    def _wrap_operands(self, operands):
        import binaryninja.enums as enums

        # if we don't support this, fallback to default platform :( :(
        # we will be using capstone anyhow, as we need to move on..
        o = self.disasm.disasm_il.operation
        if (o == enums.LowLevelILOperation.LLIL_UNIMPL or
                o == enums.LowLevelILOperation.LLIL_UNIMPL_MEM):
            return [AMD64Operand(self.platform_cpu, op) for op in operands]

        return [BinjaOperand(self, self.disasm.disasm_il, op)
                for op in operands]

    # XXX this is currently not active because a bunch of flag-setting
    # LLIL are not implemented by Binja :(
    def update_flags_from_il(cpu, il):
        # FIXME what about get_flag_condition_low_level_il
        from binaryninja.lowlevelil import LowLevelILInstruction
        flags = cpu.arch.flags_written_by_flag_write_type.get(il.flags)
        if flags is None:
            return
        func = cpu.disasm.current_llil_func

        # FIXME normally we would pass il.operands but binja has a bug here
        operands = [i for i, _ in enumerate(il.operands)]
        for f in flags:
            expr = cpu.arch.get_flag_write_low_level_il(il.operation,
                                                        il.size,
                                                        il.flags,
                                                        f,
                                                        operands,
                                                        func.low_level_il)
            flag_il = LowLevelILInstruction(func, expr.index)
            # FIXME properly invoke the implementation
            op_name = str(flag_il.operation).split(".")[1][len("LLIL_"):]
            if op_name == "UNIMPL":
                continue
            implementation = getattr(cpu, op_name)
            # flag_il.operands have indexes, involving the original operands.
            # E.g., for xor.d{*}(eax, eax), invoking `print flag_il.operands`
            # we get [<il: 0 ^ 1>, <il: 0>]
            # where 0 and 1 are the indexes. We need the operands to be
            # 'eax'. 'eax'
            flop = []
            for i, o in enumerate(flag_il.operands):
                for j, x in enumerate(o.operands):
                    x = il.operands[int(str(x))].op
                    o.operands[j] = x
                flop.append(o)
            flag_il.operands = [BinjaOperand(cpu, flag_il, x)
                                for x in flag_il.operands]
            res = implementation(*flag_il.operands)

    def update_flags(cpu, flags=None):
        mod_flags = insn_flags(cpu)
        if not mod_flags or not flags:
            return

        common = set(mod_flags).intersection(set(flags.keys()))
        to_update = {f: flags[f] for f in common}
        for f, val in to_update.items():
            cpu.regfile.write(f + "f", val)

    def push(cpu, value, size):
        '''
        Writes a value in the stack.

        :param value: the value to put in the stack.
        :param size: the size of the value.
        '''
        cpu.STACK -= size / 8
        base, _, _ = cpu.get_descriptor(cpu.ss)
        address = cpu.STACK + base
        cpu.write_int(address, value, size)

    def pop(cpu, size):
        '''
        Gets a value from the stack.

        :rtype: int
        :param size: the size of the value to consume from the stack.
        :return: the value from the stack.
        '''
        base, _, _ = cpu.get_descriptor(cpu.ss)
        address = cpu.STACK + base
        value = cpu.read_int(address, size)
        cpu.STACK += size / 8
        return value

    def ADC(cpu, left, right):
        return x86_add(cpu, left, right, True)

    def ADD(cpu, left, right):
        return x86_add(cpu, left, right)

    def ADD_OVERFLOW(cpu, left, right):
        # FIXME is this proper?
        return x86_add(cpu, left, right) < left.read() + right.read()

    def AND(cpu, left, right):
        res = left.read() & right.read()
        x86_update_logic_flags(cpu, res, right.llil.size * 8)
        return res

    def ASR(cpu, reg, shift):
        return reg.read() >> shift.read()

    def BOOL_TO_INT(cpu, src_expr):
        raise NotImplementedError

    def BP(cpu):
        raise NotImplementedError

    def CALL(cpu, expr):
        import binaryninja.enums as enums
        f = cpu.disasm.current_llil_func
        il = cpu.disasm.disasm_il

        next_addr = cpu.disasm.current_pc + cpu.disasm.disasm_insn_size
        cpu.push(next_addr, cpu.address_bit_size)

        # go for it
        new_pc = expr.read() + cpu.disasm.entry_point_diff
        cpu.PC = new_pc

    def CMP_E(cpu, left, right):
        return left.read() == right.read()

    def CMP_NE(cpu, left, right):
        return left.read() != right.read()

    def CMP_SGE(cpu, left, right):
        return (ctypes.c_int64(left.read()).value >=
                ctypes.c_int64(right.read()).value)

    def CMP_SGT(cpu, left, right):
        return (ctypes.c_int64(left.read()).value >
                ctypes.c_int64(right.read()).value)

    def CMP_SLE(cpu, left, right):
        return (ctypes.c_int64(left.read()).value <=
                ctypes.c_int64(right.read()).value)

    def CMP_SLT(cpu, left, right):
        return (ctypes.c_int64(left.read()).value <
                ctypes.c_int64(right.read()).value)

    def CMP_UGE(cpu, left, right):
        return left.read() >= right.read()

    def CMP_UGT(cpu, left, right):
        return left.read() > right.read()

    def CMP_ULE(cpu, left, right):
        return left.read() <= right.read()

    def CMP_ULT(cpu, left, right):
        return left.read() < right.read()

    def CONST(cpu, const_int):
        return const_int.op

    def CONST_PTR(cpu, const_int):
        return const_int.op + cpu.disasm.entry_point_diff

    def DIVS(cpu, dividend_h, dividend_l, divisor):
        raise NotImplementedError

    def DIVS_DP(cpu, dividend_h, dividend_l, divisor):
        size = divisor.size * 8
        dividend = Operators.CONCAT(size * 2,
                                    dividend_h.read(),
                                    dividend_l.read())

        divisor = divisor.read()
        dst_size = size * 2

        divisor = Operators.SEXTEND(divisor, size, dst_size)
        mask = (1 << dst_size) - 1
        sign_mask = 1 << (dst_size - 1)

        dividend_sign = (dividend & sign_mask) != 0
        divisor_sign = (divisor & sign_mask) != 0

        if isinstance(divisor, (int, long)):
            if divisor_sign:
                divisor = ((~divisor) + 1) & mask
                divisor = -divisor

        if isinstance(dividend, (int, long)):
            if dividend_sign:
                dividend = ((~dividend) + 1) & mask
                dividend = -dividend

        quotient = Operators.SDIV(dividend, divisor)
        return Operators.EXTRACT(quotient, 0, size)

    def DIVU(cpu, left_expr, right_expr):
        raise NotImplementedError

    def DIVU_DP(cpu, dividend_h, dividend_l, divisor):
        # XXX (theo) at least for x86, divu returns the quotient in a
        # temp register, modu will return the mod
        size = divisor.size * 8

        dividend = Operators.CONCAT(size * 2,
                                    dividend_h.read(),
                                    dividend_l.read())
        divisor = Operators.ZEXTEND(divisor.read(), size * 2)
        quotient = Operators.UDIV(dividend, divisor)
        return Operators.EXTRACT(quotient, 0, size)

    def FLAG(cpu, src_flag):
        return src_flag.read()

    def FLAG_BIT(cpu, src_flag, bit_int):
        raise NotImplementedError

    def FLAG_COND(cpu, condition):
        return condition.op

    def GOTO(cpu, expr):
        # FIXME
        try:
            if isinstance(expr.op, long):
                addr = cpu.disasm.current_llil_func[expr.op].address
            else:
                raise NotImplementedError
        except IndexError:
            addr = cpu.disasm.current_pc + cpu.disasm.disasm_insn_size

        cpu.PC = addr + cpu.disasm.entry_point_diff
        # return a value since this will be used by an IF ending in a GOTO
        return cpu.PC

    def IF(cpu, condition, true, false):
        import binaryninja.enums as enums
        from binaryninja.lowlevelil import LowLevelILInstruction

        il = cpu.disasm.disasm_il
        cond = condition.op.operands[0].op
        exp = cpu.arch.get_default_flag_condition_low_level_il(cond,
                                                               il.function)
        cond_il = LowLevelILInstruction(cpu.disasm.current_llil_func,
                                        exp.index)
        implementation = getattr(cpu, cond_il.operation.name[len("LLIL_"):])
        cond_il.operands = [BinjaOperand(cpu, cond_il, x)
                            for x in cond_il.operands]
        res = implementation(*cond_il.operands)
        idx = true.op if res else false.op
        assert isinstance(idx, long)

        try:
            next_il = cpu.disasm.current_llil_func[idx]
        except IndexError as e:
            # If we got an index error this means that we have the true
            # branch executing one insn followed by a GOTO, and the false
            # branch is outside the current_llil_func and is a JUMP
            # FIXME verify that this is true
            cpu.PC += cpu.disasm.disasm_insn_size
            return

        # if we have a (real) instruction from the IF family, the next
        # instruction should have an address different than the current PC
        if next_il.address != cpu.disasm.current_pc:
            cpu.PC = next_il.address + cpu.disasm.entry_point_diff
            return

        # The next IL instruction has the same PC. Probably a real assembly
        # instruction was resolved into multiple IL instructions. Clear the
        # queue and execute them here
        last_op_in_queue = cpu.disasm.il_queue[-1][1].operation
        assert (last_op_in_queue == enums.LowLevelILOperation.LLIL_GOTO or
                last_op_in_queue == enums.LowLevelILOperation.LLIL_JUMP or
                last_op_in_queue == enums.LowLevelILOperation.LLIL_JUMP_TO)
        del cpu.disasm.il_queue[:]

        # the sequence of instructions sharing the same PC includes both the
        # True and False branches. If we start executing at the True branch,
        # make sure we don't also execute on the False branch
        break_idx = true.op if not res else false.op

        while idx != break_idx and next_il.address == cpu.disasm.current_pc:
            goto_addr = None
            implementation = getattr(cpu, next_il.operation.name[len("LLIL_"):])
            next_il.operands = [BinjaOperand(cpu, next_il, x)
                                for x in next_il.operands]
            cpu.disasm.insn_size = next_il.size
            goto_addr = implementation(*next_il.operands)
            try:
                idx += 1
                next_il = cpu.disasm.current_llil_func[idx]
            except IndexError as e:
                break
        assert goto_addr is not None
        cpu.PC = goto_addr

    def JUMP(cpu, expr):
        addr = expr.read()
        cpu.PC = addr
        return addr

    def JUMP_TO(cpu, expr, target_indexes):
        """ Jump table construct handling
        """
        addr = expr.read()
        cpu.PC = addr
        return addr

    def LOAD(cpu, src_expr):
        # FIXME hack until push qword is fixed in binja
        if str(cpu.disasm.disasm_il).startswith("push(zx.q"):
            return cpu.read_int(src_expr.read(), 8 * 8)
        return cpu.read_int(src_expr.read(), src_expr.llil.size * 8)

    def LOW_PART(cpu, expr):
        mask = (1 << expr.llil.size * 8) - 1
        return expr.read() & mask

    def LSL(cpu, reg, shift):
        rsize = reg.llil.size * 8
        count = shift.read()
        value = reg.read()
        countMask = {8: 0x1f,
                     16: 0x1f,
                     32: 0x1f,
                     64: 0x3f}[rsize]
        temp = Operators.ZEXTEND(count & countMask, rsize)

        tempD = value = reg.read()
        res = value << count

        # Should not modify flags if temp == 0
        cf = Operators.OR(Operators.AND(temp == 0,
                                        cpu.regfile.registers['cf']),
                          Operators.AND(temp != 0,
                                        tempD & (1 << (rsize - temp)) != 0))
        of = Operators.ITE(temp != 0,
                           (cpu.regfile.registers['cf'] ^
                            (((res >> (rsize - 1)) & 0x1) == 1)),
                           cpu.regfile.registers['of'])

        SIGN_MASK = 1 << (rsize - 1)
        sf = Operators.OR(Operators.AND(temp == 0, cpu.regfile.registers['sf']),
                          Operators.AND(temp != 0, (res & SIGN_MASK) != 0))

        zf = Operators.OR(Operators.AND(temp == 0, cpu.regfile.registers['zf']),
                          Operators.AND(temp != 0, res == 0))

        pf = Operators.OR(Operators.AND(temp == 0, cpu.regfile.registers['pf']),
                          Operators.AND(temp != 0, _parity_flag(res)))
        flags = {
            'c': cf,
            'p': pf,
            'z': zf,
            's': sf,
            'o': of
        }
        cpu.update_flags(flags)
        return res

    def LSR(cpu, reg, shift):
        rsize = reg.llil.size * 8
        value = reg.read()
        count = Operators.ZEXTEND(shift.read() & (rsize - 1), rsize)
        res = value >> count

        SIGN_MASK = 1 << (rsize - 1)

        # carry flag
        if count != 0:
            cf = Operators.EXTRACT(value, count - 1, 1) != 0
        else:
            cf = cpu.regfile.registers['cf']

        zf = Operators.ITE(count != 0, res == 0, cpu.regfile.registers['zf'])
        sf = Operators.ITE(count != 0,
                           (res & SIGN_MASK) != 0,
                           cpu.regfile.registers['sf'])
        of = Operators.ITE(count != 0,
                           ((value >> (rsize - 1)) & 0x1) == 1,
                           cpu.regfile.registers['of'])
        pf = Operators.ITE(count != 0,
                           _parity_flag(res),
                           cpu.regfile.registers['pf'])

        flags = {
            'c': cf,
            'p': pf,
            'z': zf,
            's': sf,
            'o': of
        }
        cpu.update_flags(flags)
        return res

    def MODS(cpu, left_expr, right_expr):
        raise NotImplementedError

    def MODS_DP(cpu, dividend_h, dividend_l, divisor):
        size = divisor.size * 8
        dividend = Operators.CONCAT(size * 2,
                                    dividend_h.read(),
                                    dividend_l.read())

        divisor = divisor.read()
        dst_size = size * 2

        divisor = Operators.SEXTEND(divisor, size, dst_size)
        mask = (1 << dst_size) - 1
        sign_mask = 1 << (dst_size - 1)

        dividend_sign = (dividend & sign_mask) != 0
        divisor_sign = (divisor & sign_mask) != 0

        if isinstance(divisor, (int, long)):
            if divisor_sign:
                divisor = ((~divisor) + 1) & mask
                divisor = -divisor

        if isinstance(dividend, (int, long)):
            if dividend_sign:
                dividend = ((~dividend) + 1) & mask
                dividend = -dividend

        quotient = Operators.SDIV(dividend, divisor)
        if (isinstance(dividend, (int, long)) and
                isinstance(dividend, (int, long))):
            remainder = dividend - (quotient * divisor)
        else:
            remainder = Operators.SREM(dividend, divisor)
        remainder = Operators.SREM(dividend, divisor)
        return Operators.EXTRACT(remainder, 0, size)

    def MODU(cpu, left_expr, right_expr):
        raise NotImplementedError

    def MODU_DP(cpu, dividend_h, dividend_l, divisor):
        size = divisor.size
        dividend = Operators.CONCAT(size * 2,
                                    dividend_h.read(),
                                    dividend_l.read())
        divisor = Operators.ZEXTEND(divisor.read(), size * 2)
        remainder = Operators.UREM(dividend, divisor)
        return Operators.EXTRACT(remainder, 0, size)

    def MUL(cpu, left, right):
        size = left.llil.size * 8
        arg0 = left.read()
        arg1 = right.read()

        arg1 = Operators.SEXTEND(arg1, size, size * 2)
        temp = Operators.SEXTEND(arg0, size, size * 2) * arg1
        temp = temp & ((1 << (size * 2)) - 1)
        res = Operators.EXTRACT(temp, 0, size)
        cf = Operators.SEXTEND(res, size, size * 2) != temp

        cpu.regfile.write('cf', cf)
        cpu.regfile.write('of', cf)
        return res

    def MULS_DP(cpu, low_expr, high_expr):
        # XXX SET_REG_SPLIT will be called afterwards, taking care of the
        # result splitting into registers
        size = high_expr.llil.size * 8
        arg0 = high_expr.read()
        arg1 = low_expr.read()
        temp = (Operators.SEXTEND(arg0, size, size * 2) *
                Operators.SEXTEND(arg1, size, size * 2))
        res = temp & ((1 << (size * 2)) - 1)
        normres = Operators.EXTRACT(res, 0, size)

        cf = Operators.SEXTEND(normres, size, size * 2) != res
        cpu.regfile.write('cf', cf)
        cpu.regfile.write('of', cf)
        return res

    def MULU_DP(cpu, low_expr, high_expr):
        # XXX SET_REG_SPLIT will be called afterwards, taking care of the
        # result splitting into registers
        size = high_expr.llil.size * 8
        res = (Operators.ZEXTEND(low_expr.read(), 256) *
               Operators.ZEXTEND(high_expr.read(), 256))
        of = Operators.EXTRACT(res, size, size) != 0
        cpu.regfile.write('of', of)
        cpu.regfile.write('cf', of)
        return res

    def NEG(cpu, expr):
        src = expr.read()
        mask = (1 << expr.llil.size * 8) - 1
        res = -src & mask
        x86_update_logic_flags(cpu, res, expr.llil.size * 8)
        cpu.regfile.write('cf', src != 0)
        cpu.regfile.write('af', (res & 0x0f) != 0x0)
        return res

    def NOP(cpu):
        return

    def NORET(cpu):
        raise NotImplementedError

    def NOT(cpu, expr):
        return not expr.read()

    def OR(cpu, left, right):
        if left.llil.operands[0].operands[0].type == "flag":
            # don't apply a mask if this is used for flag computation
            res = left.read() | right.read()
        else:
            mask = (1 << left.llil.size * 8) - 1
            res = (left.read() | right.read()) & mask
        x86_update_logic_flags(cpu, res, left.llil.size * 8)
        return res

    def POP(cpu):
        return cpu.pop(cpu.address_bit_size)

    def PUSH(cpu, src_expr):
        # in bytes already so no need to multiply
        cpu.push(src_expr.read(), cpu.address_bit_size)

    def REG(cpu, src_reg):
        if str(src_reg.op) in cpu.regfile.segment_registers:
            base, _, _ = cpu.get_descriptor(cpu.regfile.read(src_reg.op))
            reg = base
        else:
            reg = cpu.regfile.read(src_reg.op)
        return reg

    def RET(cpu, expr):
        cpu.PC = cpu.pop(cpu.address_bit_size)

    def RLC(cpu, left_expr, right_expr, carry_expr):
        raise NotImplementedError

    def ROL(cpu, left_expr, right_expr):
        size = left_expr.llil.size * 8
        count = right_expr.read()
        countMask = {
            8: 0x1f,
            16: 0x1f,
            32: 0x1f,
            64: 0x3f
        }[size]
        tempCount = Operators.ZEXTEND((count & countMask) % (size), size)
        value = left_expr.read()
        res = (value << tempCount) | (value >> (size - tempCount))

        cpu.regfile.write('cf',
                          Operators.ITE(tempCount != 0,
                                        (res & 1) == 1,
                                        cpu.regfile.read('cf')))
        s_MSB = ((res >> (size - 1)) & 0x1) == 1
        cpu.regfile.write('of',
                          Operators.ITE(tempCount == 1,
                                        s_MSB ^ cpu.regfile.read('cf'),
                                        cpu.regfile.read('of')))
        return res

    def ROR(cpu, left_expr, right_expr):
        # FIXME refactor ROL, ROR
        size = left_expr.llil.size * 8
        count = right_expr.read()
        countMask = {8: 0x1f,
                     16: 0x1f,
                     32: 0x1f,
                     64: 0x3f}[size]
        tempCount = Operators.ZEXTEND((count & countMask) % (size), size)

        value = left_expr.read()

        res = (value >> tempCount) | (value << (size - tempCount))

        cpu.regfile.write('cf',
                          Operators.ITE(tempCount != 0,
                                        ((res >> (size - 1)) & 0x1) == 1,
                                        cpu.regfile.read('cf')))
        s_MSB = ((res >> (size - 1)) & 0x1) == 1
        s_MSB2 = ((res >> (size - 2)) & 0x1) == 1
        cpu.regfile.write('of',
                          Operators.ITE(tempCount == 1,
                                        s_MSB ^ s_MSB2,
                                        cpu.regfile.read('of')))
        return res

    def RRC(cpu, left_expr, right_expr, carry_expr):
        raise NotImplementedError

    def SBB(cpu, left_expr, right_expr, carry_expr):
        # FIXME refactor with SUB
        size = left_expr.llil.size * 8
        left_v = left_expr.read()
        if right_expr.llil.size < left_expr.llil.size:
            right_v = Operators.SEXTEND(right_expr.read(),
                                        right_expr.llil.size * 8,
                                        left_expr.llil.size * 8)
        else:
            right_v = right_expr.read()

        # add if carry
        right_v += Operators.ITEBV(size, carry_expr.read(), 1, 0)

        res = (left_v - right_v) & ((1 << size) - 1)

        x86_calculate_cmp_flags(cpu, size, res, left_v, right_v)
        return res

    def SET_FLAG(cpu, dest_flag, src_expr):
        raise NotImplementedError

    def SET_REG(cpu, dest_reg, src_expr):
        dest_reg.write(src_expr.read())

    def SET_REG_SPLIT(cpu, high_reg, low_reg, src_expr):
        res = src_expr.read()
        size = src_expr.llil.size * 8
        cpu.regfile.write(str(low_reg.op), Operators.EXTRACT(res, 0, size))
        cpu.regfile.write(str(high_reg.op), Operators.EXTRACT(res, size, size))

    def STORE(cpu, dest_expr, src_expr):
        cpu.write_int(dest_expr.read(),
                      src_expr.read(),
                      dest_expr.llil.size * 8)

    def SUB(cpu, left, right):
        size = left.llil.size * 8
        left_v = left.read()
        if right.llil.size < left.llil.size:
            right_v = Operators.SEXTEND(right.read(),
                                        right.llil.size * 8,
                                        left.llil.size * 8)
        else:
            right_v = right.read()
        res = (left_v - right_v) & ((1 << size) - 1)

        x86_calculate_cmp_flags(cpu, size, res, left_v, right_v)
        return res

    def SX(cpu, expr):
        return Operators.SEXTEND(expr.read(), expr.size * 8, expr.llil.size * 8)

    def SYSCALL(cpu):
        # FIXME arch-specific. for AMD64, 2 'syscall' is 2 bytes
        # bump the PC to the next instruction
        cpu.PC += 2

        cpu.write_register('PC', cpu.PC)
        cpu.write_register('rcx', cpu.regfile.registers['rip'])
        cpu.write_register('r11', x86_get_eflags(cpu, 'RFLAGS'))
        raise Syscall()

    def TEST_BIT(cpu, left_expr, right_expr):
        raise NotImplementedError

    def TRAP(cpu, vector_int):
        raise NotImplementedError

    def UNDEF(cpu):
        raise NotImplementedError

    def UNIMPL(cpu):
        raise NotImplementedError

    def UNIMPL_MEM(cpu, expr):
        raise NotImplementedError

    def XOR(cpu, left, right):
        if left.llil.operands[0].operands[0].type == "flag":
            # don't apply a mask if this is used for flag computation
            res = left.read() | right.read()
        else:
            mask = (1 << left.llil.size * 8) - 1
            res = (left.read() ^ right.read()) & mask
        x86_update_logic_flags(cpu, res, left.llil.size * 8)
        return res

    def ZX(cpu, expr):
        return Operators.ZEXTEND(expr.read(), expr.llil.size * 8)

    def FALLBACK(cpu, name, *operands):
        """Fallback for unimplemented instructions
        """
        logger.warning('%s: Fallback to concrete cpu for instruction %s',
                       hex(cpu.disasm.current_pc),
                       name)
        # update registers
        for pl_reg, binja_reg in cpu.regfile.pl2b_map.items():
            if isinstance(binja_reg, tuple) or binja_reg is None:
                continue
            cpu.platform_cpu.write_register(pl_reg, cpu.regfile.read(binja_reg))

        # as well as all the required attributes
        cpu.platform_cpu._icount = cpu._icount

        # do the actual call
        implementation = getattr(cpu.platform_cpu, name)
        implementation(*operands)

        # restore registers to BinjaCpu
        for pl_reg, binja_reg in cpu.regfile.pl2b_map.items():
            if isinstance(binja_reg, tuple) or binja_reg is None:
                continue
            cpu.regfile.write(binja_reg, cpu.platform_cpu.read_register(pl_reg))

#
#
# ARCH-SPECIFIC INSNs
#
#


def x86_get_eflags(cpu, reg):
    def make_symbolic(flag_expr):
        register_size = 32 if reg == 'EFLAGS' else 64
        value, offset = flag_expr
        return Operators.ITEBV(register_size, value,
                               BitVecConstant(register_size, 1 << offset),
                               BitVecConstant(register_size, 0))
    x86_flags = {
        'cf': 0,
        'pf': 2,
        'af': 4,
        'zf': 6,
        'sf': 7,
        'if': 9,
        'df': 10,
        'of': 11
    }

    flags = []
    for flag, offset in x86_flags.iteritems():
        flags.append((cpu.regfile.registers.get(flag, 0), offset))

    if any(issymbolic(flag) for flag, offset in flags):
        res = reduce(operator.or_, map(make_symbolic, flags))
    else:
        res = 0
        for flag, offset in flags:
            res += flag << offset
    return res


def insn_flags(cpu):
    # FIXME temporary hack due to binja issue with flags
    f = cpu.disasm.current_func
    il = f.get_lifted_il_at(cpu.disasm.disasm_il.address)
    mod_flags = f.get_flags_written_by_lifted_il_instruction(il.instr_index)
    #  il2 = cpu.disasm.disasm_il
    #  mod_flags2 = cpu.arch.flags_written_by_flag_write_type.get(il2.flags)
    #  assert mod_flags2 == mod_flags
    return mod_flags


def x86_calculate_cmp_flags(cpu, size, res, left_v, right_v):
    mod_flags = insn_flags(cpu)
    if not mod_flags:
        return

    flags = {
        'c': _carry_ult(left_v, right_v),
        'p': _parity_flag(res),
        'a': _adjust_flag(res, left_v, right_v),
        'z': res == 0,
        's': _sign_flag(res, size),
        'o': _overflow_flag(res, right_v, left_v, size)
    }

    cpu.update_flags(flags)


def x86_update_logic_flags(cpu, result, size):
    mod_flags = insn_flags(cpu)
    if not mod_flags:
        return
    flags = {
        'c': False,
        'p': _parity_flag(result),
        'a': False,
        'z': result == 0,
        's': _sign_flag(result, size),
        'o': False
    }
    cpu.update_flags(flags)


def x86_add(cpu, dest, src, carry=False):
    size = dest.llil.size * 8
    MASK = (1 << size) - 1
    SIGN_MASK = 1 << (size - 1)
    dest_v = dest.read()
    if src.size < dest.size:
        src_v = Operators.SEXTEND(src.read(), src.size * 8, size)
    else:
        src_v = src.read()

    to_add = src_v
    if carry:
        cv = Operators.ITEBV(size, cpu.CF, 1, 0)
        to_add = src_v + cv

    res = (dest_v + to_add) & MASK
    # Affected flags: oszapc
    tempCF = Operators.OR(_carry_ult(res, dest_v & MASK),
                          _carry_ult(res, src_v & MASK))
    if carry:
        # case of 0xFFFFFFFF + 0xFFFFFFFF + CF(1)
        tempCF = Operators.OR(tempCF,
                              Operators.AND(res == MASK,
                                            cpu.regfile.registers['cf']))
    flags = {
        'c': tempCF,
        'a': _adjust_flag(res, dest_v, src_v),
        'z': res == 0,
        's': _sign_flag(res, size),
        'o': (((dest_v ^ src_v ^ SIGN_MASK) & (res ^ src_v)) & SIGN_MASK) != 0,
        'p': _parity_flag(res)
    }
    cpu.update_flags(flags)
    return res
