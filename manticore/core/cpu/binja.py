import logging
from collections import defaultdict

from .abstractcpu import (
    Abi, SyscallAbi, Cpu, RegisterFile, Operand, instruction,
    ConcretizeRegister, ConcretizeRegister, ConcretizeArgument, Interruption,
    Syscall
)

from ..smtlib import Operators
from ...core.memory import SMemory32, SMemory64
from ...core.cpu.disasm import BinjaILDisasm

logger = logging.getLogger("CPU")


# FIXME replace cpu.disasm_size, with the size in each subexpression
# that should be part of the operand!!

class BinjaRegisterFile(RegisterFile):

    def __init__(self, view):
        '''
        ARM Register file abstraction. GPRs use ints for read/write. APSR
        flags allow writes of bool/{1, 0} but always read bools.
        '''
        # XXX we do not use view as part of the class, because then
        # we need to do a lot more work to pickle the object
        self.arch = self._get_arch(view)
        self.reg_aliases = {
            'STACK' : str(view.arch.stack_pointer),
            'PC' : self._get_pc(),
        }
        super(BinjaRegisterFile, self).__init__(aliases=self.reg_aliases)

        # Get "dummy" registers for flags. We append 'F' for consistency
        # with the X86 CPU
        f_regs = [f + "f" for f in view.arch.flags]
        # get (full width) architecture registers
        arch_regs = list(set([view.arch.regs[r].full_width_reg
                              for r in view.arch.regs.keys()]))

        # all regs are: architecture, aliases and flags
        all_regs = arch_regs + self.reg_aliases.values() + f_regs
        self.registers = {reg : 0 for reg in all_regs}

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
        ilreg = arch.regs[r]

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
        return full_width_reg_value

    def read(self, reg):
        from binaryninja import Architecture

        arch = Architecture[self.arch]

        r = self._alias(str(reg))
        if r in self.registers:
            return self.registers[r]

        reg_info = arch.regs[r]
        full_reg_value = self.registers[reg_info.full_width_reg]
        mask = (1 << reg_info.size * 8) - 1
        reg_bits = mask << (reg_info.offset * 8)
        reg_value = (full_reg_value & reg_bits) >> (reg_info.offset * 8)
        return reg_value

    @property
    def all_registers(self):
        return tuple(self.registers.keys() + self._aliases.keys())

    @property
    def canonical_registers(self):
        return tuple(self.registers.keys())

    def __contains__(self, register):
        return register in self.all_registers

    def _get_pc(self):
        if self.arch == 'x86':
            return 'eip'
        elif self.arch == 'x86_64':
            return 'rip'
        else:
            raise NotImplementedError

    def _get_arch(self, view):
        from binaryninja import Architecture

        if view.arch == Architecture['x86']:
            return 'x86'
        elif view.arch == Architecture['x86_64']:
            return 'x86_64'
        else:
            raise NotImplementedError

class BinjaOperand(Operand):
    def __init__(self, cpu, parent_il, op, **kwargs):
        self.llil = parent_il
        if hasattr(op, "operands") and op.operands:
            op.operands = [BinjaOperand(cpu, op, x) for x in op.operands]
        super(BinjaOperand, self).__init__(cpu, op, **kwargs)

    @property
    def type(self):
        from binaryninja import lowlevelil as il
        type_map = {
            il.ILRegister: 'register',
            il.LowLevelILInstruction: 'instruction',
        }

        try:
            t = type_map.get(type(self.op), None)
        except Exception as e:
            print "ERROR IN type lookup " + str(type(self.op))
            raise e
        return t

    @property
    def size(self):
        # FIXME (does this assert need to be here? we could be reading memory)
        #  assert self.type == 'register'
        return self.op.info.size

    def read(self):
        import binaryninja.enums as enums

        cpu, op = self.cpu, self.op
        if self.type == 'register':
            return cpu.read_register(self.op)
        elif self.type == 'instruction':
            implementation = getattr(cpu, op.operation.name[len("LLIL_"):])
            return implementation(*op.operands)
        else:
            raise NotImplementedError("write_operand type", op.type)

    def write(self, value):
        cpu, op = self.cpu, self.op
        if self.type == 'register':
            return cpu.write_register(str(op), value)
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

def _direction_flag(args):
    pass

def _parity_flag(v):
    return (v ^ v >> 1 ^ v >> 2 ^ v >> 3 ^ v >> 4 ^ v >> 5 ^ v >> 6 ^ v >> 7) & 1 == 0

def _overflow_flag(res, right, left, size):
    mask = 1 << (size - 1)
    sign_r = (right & mask) == mask
    sign_l = (left & mask) == mask
    sign_res = (res & mask) == mask
    return Operators.AND(sign_r ^ sign_l, sign_r ^ sign_res)

class BinjaCpu(Cpu):
    '''
    A Virtual CPU model for Binary Ninja's IL
    '''

    # Will be initialized based on the underlying Binja Architecture
    max_instr_width = None
    address_bit_size = None
    machine = 'binja_il'
    arch = None
    mode = None
    disasm = None
    view = None
    instr_ptr = None
    stack_ptr = None
    # Keep a virtual stack
    stack = []

    def __init__(self, view, memory):
        '''
        Builds a CPU model.
        :param view: BinaryNinja view.
        '''
        self.__class__.view = view
        self.__class__.max_instr_width = view.arch.max_instr_length
        self.__class__.address_bit_size = 8 * view.arch.address_size
        self.__class__.arch = view.arch
        self.__class__.disasm = BinjaILDisasm(view)
        self._segments = {}
        # initialize the memory and register files
        super(BinjaCpu, self).__init__(BinjaRegisterFile(view), memory)

    @property
    def function_hooks(self):
        return dict(self._function_hooks)

    @property
    def instr_hooks(self):
        return defaultdict(list, self._instr_hooks)

    def __getstate__(self):
        state = super(BinjaCpu, self).__getstate__()
        state['segments'] = self._segments
        return state

    def __setstate__(self, state):
        self._segments = state['segments']
        super(BinjaCpu, self).__setstate__(state)

    # FIXME (theo) that should no longer be necessary once we move everything
    # to using manticore Instruction()
    def canonicalize_instruction_name(self, insn):
        return insn.name

    def set_descriptor(self, selector, base, limit, perms):
        assert selector > 0 and selector < 0xffff
        assert base >= 0 and base < (1 << self.address_bit_size)
        assert limit >= 0 and limit < 0xffff or limit & 0xfff == 0
        self._segments[selector] = (base, limit, perms)

    def get_descriptor(self, selector):
        return self._segments.setdefault(selector, (0, 0xfffff000, 'rwx'))

    def _wrap_operands(self, operands):
        return [BinjaOperand(self, self.disasm.disasm_il, op) for op in operands]

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

    def update_flags(cpu, flags=None, args=None):
        f = cpu.disasm.current_func
        i = cpu.disasm.disasm_il

        # if the original instruction does not modify flags, don't set anything
        # (we could be here because of a STORE involving an ADD)
        mod_flags = f.get_flags_written_by_lifted_il_instruction(i.instr_index)
        if not mod_flags:
            return

        if flags is None:
            assert args is not None
            flags = mod_flags
            handlers = {
                'c': _carry_ult(args["left"], args["right"]),
                'p': _parity_flag(args["res"]),
                'a': _adjust_flag(args["res"], args["left"], args["right"]),
                'z': _zero_flag(args["res"]),
                's': _sign_flag(args["res"], args["size"]),
                'd': _direction_flag,
                'o': _overflow_flag(args["res"],
                                    args["left"],
                                    args["right"],
                                    args["size"])
            }
            for f in flags:
                cpu.regfile.write(f + "f", handlers[f])
        else:
            for f, val in flags.items():
                cpu.regfile.write(f + "f", val)

    def ADC(cpu, left, right):
        return x86_add(cpu, left, right, True)

    def ADD(cpu, left, right):
        return x86_add(cpu, left, right)

    def ADD_OVERFLOW(cpu):
        raise NotImplementedError

    def AND(cpu, left, right):
        res = left.read() & right.read()
        x86_update_logic_flags(cpu, res, right.llil.size * 8)
        return res

    def ASR(cpu, reg, shift):
        return reg.read() >> shift.read()

    def BOOL_TO_INT(cpu):
        raise NotImplementedError

    def BP(cpu):
        raise NotImplementedError

    def CALL(cpu, expr):
        # FIXME size calculation
        f = cpu.disasm.current_func
        il = f.get_lifted_il_at(cpu.disasm.current_pc)
        next_il = f.lifted_il[il.instr_index + 1].address
        diff = next_il - il.address

        # push next PC into the stack
        cpu.push(cpu.__class__.PC + diff, cpu.address_bit_size)

        new_pc = expr.read() + cpu.disasm.entry_point_diff
        cpu.__class__.PC = new_pc
        cpu.regfile.write('PC', new_pc)
        cpu.disasm.current_func = cpu.view.get_function_at(new_pc)
        assert cpu.disasm.current_func is not None


    def CMP_E(cpu):
        raise NotImplementedError

    def CMP_NE(cpu):
        raise NotImplementedError

    def CMP_SGE(cpu):
        raise NotImplementedError

    def CMP_SGT(cpu):
        raise NotImplementedError

    def CMP_SLE(cpu):
        raise NotImplementedError

    def CMP_SLT(cpu):
        raise NotImplementedError

    def CMP_UGE(cpu):
        raise NotImplementedError

    def CMP_UGT(cpu):
        raise NotImplementedError

    def CMP_ULE(cpu):
        raise NotImplementedError

    def CMP_ULT(cpu):
        raise NotImplementedError

    def CONST(cpu, expr):
        return expr.op

    def CONST_PTR(cpu, expr):
        return expr.op + cpu.disasm.entry_point_diff

    def DIVS(cpu):
        raise NotImplementedError

    def DIVS_DP(cpu):
        raise NotImplementedError

    def DIVU(cpu):
        raise NotImplementedError

    def DIVU_DP(cpu):
        raise NotImplementedError

    def FLAG(cpu):
        raise NotImplementedError

    def FLAG_BIT(cpu):
        raise NotImplementedError

    def FLAG_COND(cpu, condition):
        return condition.op

    def GOTO(cpu, expr):
        if isinstance(expr.op, long):
            addr = cpu.disasm.current_func.lifted_il[expr.op].address
        else:
            raise NotImplementedError
        cpu.__class__.PC = addr + cpu.disasm.entry_point_diff
        # return a value since this will be used by an IF ending in a GOTO
        return cpu.__class__.PC

    def IF(cpu, condition, true, false):
        cond = condition.read()

        import binaryninja.enums as enums

        # FLAGS are ['c', 'p', 'a', 'z', 's', 'd', 'o']
        # FIXME make this call the arch-specific flags
        if cond == enums.LowLevelILFlagCondition.LLFC_E:
            res = cpu.regfile.registers['zf']
        elif cond == enums.LowLevelILFlagCondition.LLFC_NE:
            res = cpu.regfile.registers['zf'] == 0
        elif cond == enums.LowLevelILFlagCondition.LLFC_NEG:
            print cond
            print hex(cpu.disasm.current_pc)
            raise NotImplementedError
        elif cond == enums.LowLevelILFlagCondition.LLFC_NO:
            print cond
            print hex(cpu.disasm.current_pc)
            raise NotImplementedError
            res = cpu.regfile.registers['of']
        elif cond == enums.LowLevelILFlagCondition.LLFC_O:
            print cond
            print hex(cpu.disasm.current_pc)
            raise NotImplementedError
            res = cpu.regfile.registers['of']
        elif cond == enums.LowLevelILFlagCondition.LLFC_POS:
            print cond
            print hex(cpu.disasm.current_pc)
            raise NotImplementedError
        elif cond == enums.LowLevelILFlagCondition.LLFC_SGE:
            print cond
            print hex(cpu.disasm.current_pc)
            raise NotImplementedError
        elif cond == enums.LowLevelILFlagCondition.LLFC_SGT:
            print cond
            print hex(cpu.disasm.current_pc)
            raise NotImplementedError
        elif cond == enums.LowLevelILFlagCondition.LLFC_SLE:
            res = Operators.OR(cpu.regfile.registers['zf'],
                               (cpu.regfile.registers['sf'] !=
                                cpu.regfile.registers['of']))
        elif cond == enums.LowLevelILFlagCondition.LLFC_SLT:
            print cond
            print hex(cpu.disasm.current_pc)
            raise NotImplementedError
        elif cond == enums.LowLevelILFlagCondition.LLFC_UGE:
            print cond
            print hex(cpu.disasm.current_pc)
            raise NotImplementedError
        elif cond == enums.LowLevelILFlagCondition.LLFC_UGT:
            res = Operators.AND(cpu.regfile.registers['cf'] == 0,
                                cpu.regfile.registers['zf'] == 0)
        elif cond == enums.LowLevelILFlagCondition.LLFC_ULE:
            res = Operators.OR(cpu.regfile.registers['zf'],
                               cpu.regfile.registers['cf'])
        elif cond == enums.LowLevelILFlagCondition.LLFC_ULT:
            print cond
            print hex(cpu.disasm.current_pc)
            raise NotImplementedError
        else:
            print cond
            raise NotImplementedError

        idx = true.op if res else false.op
        assert isinstance(idx, long)

        # if we have a (real) instruction from the IF family, the next
        # instruction should have an address different than the current PC
        next_il = cpu.disasm.current_func.lifted_il[idx]
        if next_il.address != cpu.disasm.current_pc:
            cpu.__class__.PC = next_il.address + cpu.disasm.entry_point_diff
            return

        # The next IL instruction has the same PC. Probably a real assembly
        # instruction was resolved into multiple IL instructions. Clear the
        # queue and execute them here
        assert (cpu.disasm.il_queue[-1][1].operation ==
                enums.LowLevelILOperation.LLIL_GOTO)
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
            cpu._icount += 1
            goto_addr = implementation(*next_il.operands)

            #  if logger.level == logging.DEBUG:
                #  logger.debug(str(next_il))
                #  for l in cpu.render_registers():
                    #  register_logger = logging.getLogger("REGISTERS")
                    #  register_logger.debug(l)

            idx += 1
            next_il = cpu.disasm.current_func.lifted_il[idx]
        assert goto_addr is not None
        cpu.__class__.PC = goto_addr


    def JUMP(cpu, expr):
        addr = expr.read()
        cpu.regfile.write('PC', addr)
        cpu.__class__.PC = addr
        cpu.disasm.current_func = cpu.view.get_function_at(addr)
        assert cpu.disasm.current_func is not None


    def JUMP_TO(cpu):
        raise NotImplementedError


    def LOAD(cpu, expr):
        return cpu.read_int(expr.read(), expr.llil.size * 8)


    def LOW_PART(cpu, expr):
        # FIXME account for the size this is currently wrong. should
        # read() handle this or not?
        raise NotImplementedError
        return expr.read()


    def LSL(cpu, reg, shift):
        rsize = reg.llil.size * 8
        count = shift.read()
        value = reg.read()
        countMask = {8 : 0x1f,
                     16: 0x1f,
                     32: 0x1f,
                     64: 0x3f }[rsize]
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

    def MODS(cpu):
        raise NotImplementedError

    def MODS_DP(cpu):
        raise NotImplementedError

    def MODU(cpu):
        raise NotImplementedError

    def MODU_DP(cpu):
        raise NotImplementedError

    def MUL(cpu, left, right):
        raise NotImplementedError
        return left.read() * right.read()

    def MULS_DP(cpu):
        raise NotImplementedError

    def MULU_DP(cpu):
        raise NotImplementedError

    def NEG(cpu):
        raise NotImplementedError

    def NOP(cpu):
        return

    def NORET(cpu):
        raise NotImplementedError

    def NOT(cpu):
        raise NotImplementedError

    def OR(cpu, left, right):
        res = left.read() | right.read()
        x86_update_logic_flags(cpu, res, left.llil.size * 8)
        return res

    def POP(cpu):
        return cpu.pop(cpu.address_bit_size)

    def PUSH(cpu, src):
        # in bytes already so no need to multiply
        cpu.push(src.read(), cpu.address_bit_size)

    def REG(cpu, expr):
        return cpu.regfile.read(expr.op)

    def RET(cpu, expr):
        cpu.__class__.PC = cpu.pop(cpu.address_bit_size)

    def RLC(cpu):
        raise NotImplementedError

    def ROL(cpu):
        raise NotImplementedError

    def ROR(cpu):
        raise NotImplementedError

    def RRC(cpu):
        raise NotImplementedError

    def SBB(cpu):
        raise NotImplementedError

    def SET_FLAG(cpu):
        raise NotImplementedError

    def SET_REG(cpu, dest, src):
        dest.write(src.read())

    def SET_REG_SPLIT(cpu):
        raise NotImplementedError

    def STORE(cpu, dest, src):
        cpu.write_int(dest.read(), src.read(), dest.llil.size * 8)

    def SUB(cpu, left, right):
        size = right.llil.size * 8
        right_v = right.read()
        left_v = left.read()
        res = left_v - right_v

        # FIXME arch-specific flags
        flags = {
            'c': _carry_ult(left_v, right_v),
            'p': _parity_flag(res),
            'a': _adjust_flag(res, left_v, right_v),
            'z': res == 0,
            's': _sign_flag(res, size),
            'o': _overflow_flag(res, right_v, left_v, size)
        }
        cpu.update_flags(flags)
        return res

    def SX(cpu, expr):
        return Operators.SEXTEND(expr.read(), expr.size, expr.llil.size)

    def SYSCALL(cpu):
        raise NotImplementedError

    def TEST_BIT(cpu):
        raise NotImplementedError

    def TRAP(cpu):
        raise NotImplementedError

    def UNDEF(cpu):
        raise NotImplementedError

    def UNIMPL(cpu):
        # FIXME invoke platform-specific CPU here
        disasm = cpu.view.get_disassembly(cpu.disasm.current_pc)
        if disasm == "rdtsc":
            x86_rdtsc(cpu)
        elif disasm == "cpuid":
            x86_cpuid(cpu)
        elif disasm == "xgetbv":
            x86_xgetbv(cpu)
        else:
            print disasm
            print hex(cpu.disasm.current_pc)
            raise NotImplementedError

    def UNIMPL_MEM(cpu):
        raise NotImplementedError

    def XOR(cpu, left, right):
        res = left.read() ^ right.read()
        x86_update_logic_flags(cpu, res, left.llil.size * 8)
        return res

    def ZX(cpu, expr):
        return Operators.ZEXTEND(expr.read(), expr.llil.size * 8)

#
#
# ARCH-SPECIFIC INSNS
#
#


def x86_xgetbv(cpu):
    cpu.write_register('eax', 7)
    cpu.write_register('edx', 0)

def x86_update_logic_flags(cpu, result, size):
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


    # FIXME ignore this for now, we will deal with it if we are to
    # store the register properly.
    #  res = dest.write((dest_v + to_add) & MASK)
    res = dest_v + to_add
    #Affected flags: oszapc
    tempCF = Operators.OR(_carry_ult(res, dest_v & MASK),
                          _carry_ult(res, src_v & MASK))
    if carry:
        # case of 0xFFFFFFFF + 0xFFFFFFFF + CF(1)
        tempCF = Operators.OR(tempCF,
                              Operators.AND(res == MASK,
                                            cpu.regfile.registers['cf']))
    flags = {
        'c' : tempCF,
        'a' : _adjust_flag(res, dest_v, src_v),
        'z' : res == 0,
        's' : _sign_flag(res, size),
        'o' : (((dest_v ^ src_v ^ SIGN_MASK) & (res ^ src_v)) & SIGN_MASK) != 0,
        'p' : _parity_flag(res)
    }
    cpu.update_flags(flags)
    return res


def x86_rdtsc(cpu):
    val = cpu.icount
    cpu.regfile.write('rax', val & 0xffffffff)
    cpu.regfile.write('rdx', (val >> 32) & 0xffffffff)

def x86_cpuid(cpu):
    '''
    CPUID instruction.

    The ID flag (bit 21) in the EFLAGS register indicates support for the
    CPUID instruction.  If a software procedure can set and clear this
    flag, the processor executing the procedure supports the CPUID
    instruction. This instruction operates the same in non-64-bit modes and
    64-bit mode.  CPUID returns processor identification and feature
    information in the EAX, EBX, ECX, and EDX registers.

    The instruction's output is dependent on the contents of the EAX
    register upon execution.

    :param cpu: current CPU.
    '''
    conf = {   0x0:        (0x0000000d, 0x756e6547, 0x6c65746e, 0x49656e69),
               0x1:        (0x000306c3, 0x05100800, 0x7ffafbff, 0xbfebfbff),
               0x2:        (0x76035a01, 0x00f0b5ff, 0x00000000, 0x00c10000),
               0x4: { 0x0: (0x1c004121, 0x01c0003f, 0x0000003f, 0x00000000),
                      0x1: (0x1c004122, 0x01c0003f, 0x0000003f, 0x00000000),
                      0x2: (0x1c004143, 0x01c0003f, 0x000001ff, 0x00000000),
                      0x3: (0x1c03c163, 0x03c0003f, 0x00000fff, 0x00000006)},
               0x7:        (0x00000000, 0x00000000, 0x00000000, 0x00000000),
               0x8:        (0x00000000, 0x00000000, 0x00000000, 0x00000000),
               0xb: { 0x0: (0x00000001, 0x00000002, 0x00000100, 0x00000005),
                      0x1: (0x00000004, 0x00000004, 0x00000201, 0x00000003)},
               0xd: { 0x0: (0x00000000, 0x00000000, 0x00000000, 0x00000000),
                      0x1: (0x00000000, 0x00000000, 0x00000000, 0x00000000)},
              }

    if cpu.regfile.read('eax') not in conf:
        logger.warning('CPUID with EAX=%x not implemented @ %x',
                       cpu.regfile.read('rax'), cpu.__class__.PC)
        cpu.write_register('eax', 0)
        cpu.write_register('ebx', 0)
        cpu.write_register('ecx', 0)
        cpu.write_register('edx', 0)
        return

    if isinstance(conf[cpu.regfile.read('eax')], tuple):
        v = conf[cpu.regfile.read('rax')]
        cpu.write_register('eax', v[0])
        cpu.write_register('ebx', v[1])
        cpu.write_register('ecx', v[2])
        cpu.write_register('edx', v[3])
        return

    if cpu.regfile.read('ecx') not in conf[cpu.regfile.read('eax')]:
        logger.warning('CPUID with EAX=%x ECX=%x not implemented',
                       cpu.regfile.read('rax'),
                       cpu.regfile.read('rcx'))
        cpu.write_register('eax', 0)
        cpu.write_register('ebx', 0)
        cpu.write_register('ecx', 0)
        cpu.write_register('edx', 0)
        return

    v = conf[cpu.regfile.read('eax')][cpu.regfile.read('ecx')]
    cpu.write_register('eax', v[0])
    cpu.write_register('ebx', v[1])
    cpu.write_register('ecx', v[2])
    cpu.write_register('edx', v[3])
