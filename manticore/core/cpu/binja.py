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

class BinjaRegisterFile(RegisterFile):

    def __init__(self, view):
        '''
        ARM Register file abstraction. GPRs use ints for read/write. APSR
        flags allow writes of bool/{1, 0} but always read bools.
        '''
        self.reg_aliases = {
            'STACK' : str(view.arch.stack_pointer),
            'PC' : self._get_pc(view),
        }

        super(BinjaRegisterFile, self).__init__(aliases=self.reg_aliases)

        # Initialize register values, cache and side-effects
        self._cache = dict()
        self.flags = {f : 0 for f in view.arch.flags}
        all_regs = view.arch.regs.keys() + self.reg_aliases.values()
        self.registers = {reg : 0 for reg in all_regs}
        # FIXME (theo) get side effects

    def write(self, reg, value):
        # FIXME account for sizes
        #
        reg = self._alias(str(reg))
        # FIXME we will need to be calling the appropriate setters as in x86
        self._update_cache(reg, value)
        return value

    def read(self, reg):
        reg = self._alias(str(reg))
        if reg in self._cache:
            return self._cache[reg]

        # FIXME we will need to be calling the appropriate getters as in x86
        value = self.registers[reg]
        # FIXME we should read via get_register
        self._cache[reg] = value
        return value

    def _update_cache(self, reg, value):
        reg = self._alias(str(reg))
        self._cache[reg] = value

    @property
    def all_registers(self):
        return tuple(self.registers.keys() + self._aliases.keys())

    @property
    def canonical_registers(self):
        return tuple(self.registers.keys())

    def __contains__(self, register):
        return register in self.all_registers

    def _get_pc(self, view):
        from binaryninja import Architecture

        if view.arch == Architecture['x86']:
            return 'eip'
        elif view.arch == Architecture['x86_64']:
            return 'rip'
        else:
            raise NotImplementedError

class BinjaOperand(Operand):
    def __init__(self, cpu, op, **kwargs):
        if hasattr(op, "operands") and op.operands:
            op.operands = [BinjaOperand(cpu, x) for x in op.operands]
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
            value = cpu.read_register(self.op)
            return value
        elif self.type == 'instruction':
            if op.operation == enums.LowLevelILOperation.LLIL_CONST:
                # FIXME ugly hack to see if  CONST is a CONST_PTR
                # It is always the source that might be a const pointer, but
                # this information seems to only be present in LowLevelIL?
                llil = cpu.disasm.current_func.get_low_level_il_at(op.address)
                if (hasattr(llil, 'src') and
                        llil.src.operation == enums.LowLevelILOperation.LLIL_CONST_PTR):
                    implementation = getattr(cpu, "CONST_PTR")
                    return implementation(*op.operands)

            implementation = getattr(cpu, op.operation.name[len("LLIL_"):])
            #  print "Calling " + op.operation.name
            if op.operation == enums.LowLevelILOperation.LLIL_LOAD:
                return implementation(*op.operands, expr_size=op.size)
            return implementation(*op.operands)

    def write(self, value):
        cpu, op = self.cpu, self.op
        if self.type == 'register':
            cpu.write_register(str(op), value)
        else:
            raise NotImplementedError("write_operand type", o.type)
        return value & ((1 << self.size) - 1)

    def __getattr__(self, name):
        return getattr(self.op, name)

def _carry_flag(args):
    return Operators.ULT(args["left"], args["right"])

def _adjust_flag(args):
    return ((args["left"] ^ args["right"]) ^ args["result"]) & 0x10 != 0

def _zero_flag(args):
    return args["result"] == 0

def _sign_flag(args):
    mask = 1 << (args["size"] - 1)
    return (args["result"] & mask) != 0

def _direction_flag(args):
    pass

def _parity_flag(args):
    v = args["result"]
    return (v ^ v >> 1 ^ v >> 2 ^ v >> 3 ^ v >> 4 ^ v >> 5 ^ v >> 6 ^ v >> 7) & 1 == 0

def _overflow_flag(args):
    mask = 1 << (args["size"] - 1)
    sign_l = (args["left"] & mask) == mask
    sign_r = (args["right"] & mask) == mask
    sign_res = (args["result"] & mask) == mask
    return Operators.AND(sign_l ^ sign_r, sign_l ^ sign_res)

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
        return [BinjaOperand(self, op) for op in operands]

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

    def _update_flags(cpu, args, flags=None):
        if not flags:
            f = cpu.disasm.current_func
            i = f.get_lifted_il_at(cpu.disasm.current_pc)
            flags = f.get_flags_written_by_lifted_il_instruction(i.instr_index)

        handlers = {
            'c': _carry_flag,
            'p': _parity_flag,
            'a': _adjust_flag,
            'z': _zero_flag,
            's': _sign_flag,
            'd': _direction_flag,
            'o': _overflow_flag
        }

        for f in flags:
            handlers[f](args)

    @instruction
    def ADC(cpu):
        raise NotImplementedError

    @instruction
    def ADD(cpu, left, right):
        left_v = left.read()
        right_v = right.read()
        result = left_v + right_v
        size = left.op.size
        print "SIZE " + str(size)
        args = {
            "result" : result,
            "size" : size,
            "left" : left_v,
            "right" : right_v
        }

        cpu._update_flags(args, ['c', 'p', 'a', 'z', 's', 'o'])
        return result

    @instruction
    def ADD_OVERFLOW(cpu):
        raise NotImplementedError

    @instruction
    def AND(cpu, left, right):
        left_v = left.read()
        right_v = right.read()
        result = left_v & right_v
        size = left.op.size

        print "SIZE " + str(size)
        args = {
            "result" : result,
            "size" : size,
            "left" : left_v,
            "right" : right_v
        }

        cpu._update_flags(args, ['c', 'p', 'a', 'z', 's', 'o'])
        return result
        return value

    @instruction
    def ASR(cpu, reg, shift):
        return reg.read() >> shift.read()

    @instruction
    def BOOL_TO_INT(cpu):
        raise NotImplementedError
    @instruction
    def BP(cpu):
        raise NotImplementedError

    @instruction
    def CALL(cpu, expr):
        new_pc = long(str(expr.op), 16) + cpu.disasm.entry_point_diff
        cpu.regfile.write('PC', new_pc)
        cpu.__class__.PC = new_pc
        cpu.push(new_pc, cpu.address_bit_size)

    @instruction
    def CMP_E(cpu):
        raise NotImplementedError
    @instruction
    def CMP_NE(cpu):
        raise NotImplementedError
    @instruction
    def CMP_SGE(cpu):
        raise NotImplementedError
    @instruction
    def CMP_SGT(cpu):
        raise NotImplementedError
    @instruction
    def CMP_SLE(cpu):
        raise NotImplementedError
    @instruction
    def CMP_SLT(cpu):
        raise NotImplementedError
    @instruction
    def CMP_UGE(cpu):
        raise NotImplementedError
    @instruction
    def CMP_UGT(cpu):
        raise NotImplementedError
    @instruction
    def CMP_ULE(cpu):
        raise NotImplementedError
    @instruction
    def CMP_ULT(cpu):
        raise NotImplementedError

    @instruction
    def CONST(cpu, expr):
        return expr.op

    @instruction
    def CONST_PTR(cpu, expr):
        return expr.op + cpu.disasm.entry_point_diff

    @instruction
    def DIVS(cpu):
        raise NotImplementedError
    @instruction
    def DIVS_DP(cpu):
        raise NotImplementedError
    @instruction
    def DIVU(cpu):
        raise NotImplementedError
    @instruction
    def DIVU_DP(cpu):
        raise NotImplementedError
    @instruction
    def FLAG(cpu):
        raise NotImplementedError
    @instruction
    def FLAG_BIT(cpu):
        raise NotImplementedError

    @instruction
    def FLAG_COND(cpu, condition):
        return condition.op

    @instruction
    def GOTO(cpu, expr):
        if isinstance(expr.op, long):
            addr = cpu.disasm.current_func.lifted_il[expr.op].address
        else:
            raise NotImplementedError
        cpu.__class__.PC = addr + cpu.disasm.entry_point_diff

    @instruction
    def IF(cpu, condition, true, false):
        cond = condition.read()

        import binaryninja.enums as enums

        # FLAGS are ['c', 'p', 'a', 'z', 's', 'd', 'o']
        # FIXME check these for correctness. Probably buggy!!
        if cond == enums.LowLevelILFlagCondition.LLFC_E:
            res = cpu.regfile.flags['z'] == 1
        elif cond == enums.LowLevelILFlagCondition.LLFC_NE:
            res = cpu.regfile.flags['z'] == 0
        elif cond == enums.LowLevelILFlagCondition.LLFC_NEG:
            print cond
            raise NotImplementedError
        elif cond == enums.LowLevelILFlagCondition.LLFC_NO:
            res = cpu.regfile.flags['o'] == 0
        elif cond == enums.LowLevelILFlagCondition.LLFC_O:
            res = cpu.regfile.flags['o'] == 1
        elif cond == enums.LowLevelILFlagCondition.LLFC_POS:
            print cond
            raise NotImplementedError
        elif cond == enums.LowLevelILFlagCondition.LLFC_SGE:
            print cond
            raise NotImplementedError
        elif cond == enums.LowLevelILFlagCondition.LLFC_SGT:
            print cond
            raise NotImplementedError
        elif cond == enums.LowLevelILFlagCondition.LLFC_SLE:
            print cond
            raise NotImplementedError
        elif cond == enums.LowLevelILFlagCondition.LLFC_SLT:
            print cond
            raise NotImplementedError
        elif cond == enums.LowLevelILFlagCondition.LLFC_UGE:
            res = cpu.regfile.flags['c'] == 0
        elif cond == enums.LowLevelILFlagCondition.LLFC_UGT:
            res = (cpu.regfile.flags['z'] & cpu.regfile.flags['c']) == 0
        elif cond == enums.LowLevelILFlagCondition.LLFC_ULE:
            res = (cpu.regfile.flags['z'] | cpu.regfile.flags['c']) == 1
        elif cond == enums.LowLevelILFlagCondition.LLFC_ULT:
            res = cpu.regfile.flags['c'] == 1
        else:
            print cond
            raise NotImplementedError

        idx = true.op if res else false.op
        assert isinstance(idx, long)

        next_il = cpu.disasm.current_func.lifted_il[idx]
        # it could be that a single assembly instruction results in multiple
        # IL instructions involving an IF (e.g., `sete al {0,0} {0x1}`). In
        # case the next address is the same as the current instruction's, just
        # advance the index in the IL until we find a new address
        while next_il.address == cpu.disasm.current_pc:
            implementation = getattr(cpu, next_il.operation.name[len("LLIL_"):])
            next_il.operands = [BinjaOperand(cpu, x) for x in next_il.operands]
            implementation(*next_il.operands)
            idx += 1
            next_il = cpu.disasm.current_func.lifted_il[idx]
        else:
            addr = next_il.address + cpu.disasm.entry_point_diff
        cpu.__class__.PC = addr

    @instruction
    def JUMP(cpu, expr):
        addr = expr.read()
        cpu.regfile.write('PC', addr)
        cpu.__class__.PC = addr

    @instruction
    def JUMP_TO(cpu):
        raise NotImplementedError

    @instruction
    def LOAD(cpu, expr, expr_size=None):
        return cpu.read_int(expr.read(), expr_size * 8)

    @instruction
    def LOW_PART(cpu, expr):
        # FIXME account for the size this is currently wrong. should
        # read() handle this or not?
        return expr.read()

    @instruction
    def LSL(cpu, reg, shift):
        left_v = reg.read()
        right_v = shift.read()
        result = left_v << right_v
        size = reg.op.size
        print "SIZE " + str(size)

        args = {
            "result" : result,
            "size" : size,
            "left" : left_v,
            "right" : right_v
        }
        cpu._update_flags(args, ['c', 'p', 'a', 'z', 's', 'o'])
        return result

    @instruction
    def LSR(cpu):
        raise NotImplementedError
    @instruction
    def MODS(cpu):
        raise NotImplementedError
    @instruction
    def MODS_DP(cpu):
        raise NotImplementedError
    @instruction
    def MODU(cpu):
        raise NotImplementedError
    @instruction
    def MODU_DP(cpu):
        raise NotImplementedError

    @instruction
    def MUL(cpu, left, right):
        return left.read() * right.read()

    @instruction
    def MULS_DP(cpu):
        raise NotImplementedError
    @instruction
    def MULU_DP(cpu):
        raise NotImplementedError
    @instruction
    def NEG(cpu):
        raise NotImplementedError
    @instruction
    def NOP(cpu):
        return

    @instruction
    def NORET(cpu):
        raise NotImplementedError
    @instruction
    def NOT(cpu):
        raise NotImplementedError

    @instruction
    def OR(cpu, left, right):
        left_v = left.read()
        right_v = right.read()
        result = left_v | right_v
        size = left.op.size
        print "SIZE " + str(size)

        args = {
            "result" : result,
            "size" : size,
            "left" : left_v,
            "right" : right_v
        }
        cpu._update_flags(args, ['c', 'p', 'a', 'z', 's', 'o'])
        return result

    @instruction
    def POP(cpu):
        # FIXME this is wrong! get it from the destination register!
        return cpu.pop(cpu.address_bit_size)

    @instruction
    def PUSH(cpu, src):
        cpu.push(src.read(), src.op.size * 8)

    @instruction
    def REG(cpu, expr):
        return cpu.regfile.read(expr.op)

    @instruction
    def RET(cpu):
        raise NotImplementedError
    @instruction
    def RLC(cpu):
        raise NotImplementedError
    @instruction
    def ROL(cpu):
        raise NotImplementedError
    @instruction
    def ROR(cpu):
        raise NotImplementedError
    @instruction
    def RRC(cpu):
        raise NotImplementedError
    @instruction
    def SBB(cpu):
        raise NotImplementedError
    @instruction
    def SET_FLAG(cpu):
        raise NotImplementedError

    @instruction
    def SET_REG(cpu, dest, src):
        # FIXME
        #  if dest.op.size > src.op.size:
            #  dest.write(Operators.ZEXTEND(src.read(), src.op.size))
        #  else:
            #  dest.write(Operators.EXTRACT(src.read(), 0, src.op.size))
        dest.write(src.read())

    @instruction
    def SET_REG_SPLIT(cpu):
        raise NotImplementedError

    @instruction
    def STORE(cpu, dest, src):
        print "SIZE " + str(dest.op.size)
        cpu.write_int(dest.read(), src.read(), dest.op.size * 8)

    @instruction
    def SUB(cpu, left, right):
        left_v = left.read()
        right_v = right.read()
        result = left_v - right_v
        size = left.op.size
        print "SIZE " + str(size)

        args = {
            "result" : result,
            "size" : size,
            "left" : left_v,
            "right" : right_v
        }

        cpu._update_flags(args, ['c', 'p', 'a', 'z', 's', 'o'])
        return result


    @instruction
    def SX(cpu):
        raise NotImplementedError
    @instruction
    def SYSCALL(cpu):
        raise NotImplementedError
    @instruction
    def TEST_BIT(cpu):
        raise NotImplementedError
    @instruction
    def TRAP(cpu):
        raise NotImplementedError
    @instruction
    def UNDEF(cpu):
        raise NotImplementedError

    @instruction
    def UNIMPL(cpu):
        # FIXME invoke platform-specific CPU here
        disasm = cpu.view.get_disassembly(cpu.disasm.current_pc)
        if disasm == "rdtsc":
            x86_rdtsc(cpu)
        elif disasm == "cpuid":
            x86_cpuid(cpu)
        else:
            raise NotImplementedError

    @instruction
    def UNIMPL_MEM(cpu):
        raise NotImplementedError

    @instruction
    def XOR(cpu, left, right):
        left_v = left.read()
        right_v = right.read()
        result = left_v ^ right_v
        size = left.op.size
        print "SIZE " + str(size)

        args = {
            "result" : result,
            "size" : size,
            "left" : left_v,
            "right" : right_v
        }

        cpu._update_flags(args, ['c', 'p', 'a', 'z', 's', 'o'])
        return result

    @instruction
    def ZX(cpu, expr):
        # FIXME zero extension
        val = expr.read()
        return val

#
#
# ARCH-SPECIFIC INSNS
#
#

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

    if cpu.regfile.registers['eax'] not in conf:
        logger.warning('CPUID with EAX=%x not implemented @ %x',
                       cpu.regfile.registers['eax'], cpu.__class__.PC)
        cpu.write_register('eax', 0)
        cpu.write_register('ebx', 0)
        cpu.write_register('ecx', 0)
        cpu.write_register('edx', 0)
        return

    if isinstance(conf[cpu.regfile.registers['eax']], tuple):
        v = conf[cpu.regfile.registers['eax']]
        cpu.write_register('eax', v[0])
        cpu.write_register('ebx', v[1])
        cpu.write_register('ecx', v[2])
        cpu.write_register('edx', v[3])
        return

    if cpu.regfile.registers['ecx'] not in conf[cpu.regfile.registers['eax']]:
        logger.warning('CPUID with EAX=%x ECX=%x not implemented',
                       cpu.regfile.registers['eax'],
                       cpu.regfile.registers['ecx'])
        cpu.write_register('eax', 0)
        cpu.write_register('ebx', 0)
        cpu.write_register('ecx', 0)
        cpu.write_register('edx', 0)
        return

    v = conf[cpu.regfile.registers['eax']][cpu.regfile.registers['ecx']]
    cpu.write_register('eax', v[0])
    cpu.write_register('ebx', v[1])
    cpu.write_register('ecx', v[2])
    cpu.write_register('edx', v[3])
