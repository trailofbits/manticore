import logging
from collections import defaultdict

from .abstractcpu import (
    Abi, SyscallAbi, Cpu, RegisterFile, Operand, instruction,
    ConcretizeRegister, ConcretizeRegister, ConcretizeArgument, Interruption,
    Syscall
)

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
        all_regs = view.arch.regs.keys() + self.reg_aliases.values()
        self._registers = {reg : 0 for reg in all_regs}
        # FIXME (theo) get side effects

    def write(self, reg, value):
        reg = self._alias(str(reg))
        # FIXME we will need to be calling the appropriate setters as in x86
        self._update_cache(reg, value)
        return value

    def read(self, reg):
        reg = self._alias(str(reg))
        if reg in self._cache:
            return self._cache[reg]

        # FIXME we will need to be calling the appropriate getters as in x86
        value = self._registers[reg]
        # FIXME we should read via get_register
        self._cache[reg] = value
        return value

    def _update_cache(self, reg, value):
        reg = self._alias(str(reg))
        self._cache[reg] = value

    @property
    def all_registers(self):
        return tuple(self._registers.keys() + self._aliases.keys())

    @property
    def canonical_registers(self):
        return tuple(self._registers.keys())

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
        if hasattr(op, "operands"):
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
        assert self.type == 'register'
        return self.op.info.size

    def read(self):
        cpu, op = self.cpu, self.op
        if self.type == 'register':
            value = cpu.read_register(self.op)
            print("Reading %d from %s" % (value, op))
            return value
        elif self.type == 'instruction':
            # FIXME (theo) what if this is symbolic? should this be getting
            # called here?
            implementation = getattr(cpu, op.operation.name[len("LLIL_"):])
            #  print "Calling " + str(implementation) + " with " + str(op.operands)
            return implementation(*op.operands)

    def write(self, value):
        cpu, op = self.cpu, self.op
        if self.type == 'register':
            print("Writing %d to %s" % (value, op))
            cpu.write_register(str(op), value)
        else:
            raise NotImplementedError("write_operand type", o.type)
        return value & ((1 << self.size) - 1)

    def __getattr__(self, name):
        return getattr(self.op, name)

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
        return state

    def __setstate__(self, state):
        super(BinjaCpu, self).__setstate__(state)

    # FIXME (theo) that should no longer be necessary once we move everything
    # to using manticore Instruction()
    def canonicalize_instruction_name(self, insn):
        return insn.name

    def _wrap_operands(self, operands):
        #  print [type(op) for op in operands]
        return [BinjaOperand(self, op) for op in operands]

    def get_register_value(self, register):
        from binaryninja import LLIL_REG_IS_TEMP, LLIL_GET_TEMP_REG_INDEX, ILRegister
        if (isinstance(register, int) and
                LLIL_REG_IS_TEMP(register)):
            reg_value = self.regfile._registers.get(register)

            if reg_value is None:
                raise SystemExit("whaaat")
                #  raise errors.UndefinedError(
                    #  'Register {} not defined'.format(
                        #  LLIL_GET_TEMP_REG_INDEX(register)
                    #  )
                #  )

            return reg_value

        if isinstance(register, ILRegister):
            register = register.name

        # FIXME
        reg_info = self.view.arch.regs[register]

        full_reg_value = self.regfile._registers.get(reg_info.full_width_reg)

        if full_reg_value is None:
            raise SystemExit("whaaat")
            #  raise errors.UndefinedError(
                #  'Register {} not defined'.format(
                    #  register
                #  )
            #  )

        if register == reg_info.full_width_reg:
            return full_reg_value

        mask = (1 << reg_info.size * 8) - 1
        reg_bits = mask << (reg_info.offset * 8)

        reg_value = (full_reg_value & reg_bits) >> (reg_info.offset * 8)

        return reg_value

    def set_register_value(self, register, value):
        # If it's a temp register, just set the value no matter what.
        # Maybe this will be an issue  eventually, maybe not.
        from binaryninja import LLIL_REG_IS_TEMP, LLIL_GET_TEMP_REG_INDEX, ILRegister
        if (isinstance(register, (int, long)) and
                LLIL_REG_IS_TEMP(register)):
            self.regfile._registers[register] = value

        if isinstance(register, ILRegister):
            register = register.name

        reg_info = self.view.arch.regs[register]

        # normalize value to be unsigned
        if value < 0:
            value = value + (1 << reg_info.size * 8)

        if 0 > value >= (1 << reg_info.size * 8):
            raise ValueError('value is out of range')

        if register == reg_info.full_width_reg:
            self.regfile._registers[register] = value
            return value

        full_width_reg_info = self.view.arch.regs[reg_info.full_width_reg]
        full_width_reg_value = self.regfile._registers.get(full_width_reg_info.full_width_reg)

        # XXX: The RegisterInfo.extend field currently holds a string for
        #      for built-in Architectures.
        if (full_width_reg_value is None and
                (reg_info.extend == 'NoExtend' or
                 reg_info.offset != 0)):
            raise SystemExit("AH OH")

        if reg_info.extend == 'ZeroExtendToFullWidth':
            full_width_reg_value = value

        elif reg_info.extend == 'SignExtendToFullWidth':
            full_width_reg_value = (
                (value ^ ((1 << reg_info.size * 8) - 1)) -
                ((1 << reg_info.size * 8) - 1) +
                (1 << full_width_reg_info.size * 8)
            )

        elif reg_info.extend == 'NoExtend':
            # mask off the value that will be replaced
            mask = (1 << reg_info.size * 8) - 1
            full_mask = (1 << full_width_reg_info.size * 8) - 1
            reg_bits = mask << (reg_info.offset * 8)

            full_width_reg_value &= full_mask ^ reg_bits
            full_width_reg_value |= value << reg_info.offset * 8

        self.regfile._registers[full_width_reg_info.full_width_reg] = full_width_reg_value

        return full_width_reg_value

    @instruction
    def ADC(cpu):
        raise NotImplementedError

    @instruction
    def ADD(cpu):
        raise NotImplementedError

    @instruction
    def ADD_OVERFLOW(cpu):
        raise NotImplementedError
    @instruction
    def AND(cpu):
        raise NotImplementedError
    @instruction
    def ASR(cpu):
        raise NotImplementedError
    @instruction
    def BOOL_TO_INT(cpu):
        raise NotImplementedError
    @instruction
    def BP(cpu):
        raise NotImplementedError
    @instruction
    def CALL(cpu):
        raise NotImplementedError
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
    def CONST(cpu):
        raise NotImplementedError
    @instruction
    def CONST_PTR(cpu):
        raise NotImplementedError
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
    def FLAG_COND(cpu):
        raise NotImplementedError
    @instruction
    def GOTO(cpu, dest):
        raise NotImplementedError
    @instruction
    def IF(cpu):
        raise NotImplementedError
    @instruction
    def JUMP(cpu):
        raise NotImplementedError
    @instruction
    def JUMP_TO(cpu):
        raise NotImplementedError
    @instruction
    def LOAD(cpu):
        raise NotImplementedError
    @instruction
    def LOW_PART(cpu):
        raise NotImplementedError
    @instruction
    def LSL(cpu):
        raise NotImplementedError
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
    def MUL(cpu):
        raise NotImplementedError
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
        raise NotImplementedError
    @instruction
    def NORET(cpu):
        raise NotImplementedError
    @instruction
    def NOT(cpu):
        raise NotImplementedError
    @instruction
    def OR(cpu):
        raise NotImplementedError

    @instruction
    def POP(cpu, dest):
        raise NotImplementedError
        cpu.pop(dest)

    @instruction
    def PUSH(cpu, src):
        raise NotImplementedError
        cpu.push(src)

    @instruction
    def REG(cpu, expr):
        return cpu.get_register_value(expr.op)
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
        value = src.read()
        dest.write(src.read())

    @instruction
    def SET_REG_SPLIT(cpu):
        raise NotImplementedError

    @instruction
    def STORE(cpu):
        raise NotImplementedError
    @instruction
    def SUB(cpu):
        raise NotImplementedError
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
        raise NotImplementedError
    @instruction
    def UNIMPL_MEM(cpu):
        raise NotImplementedError

    @instruction
    def XOR(cpu, left, right):
        # FIXME Flags?
        return left.read() ^ right.read()
        #  if str(dest) == str(src):
            #  #if the operands are the same write zero
            #  return 0
        #  else:
            #  res = dest.write(dest.read() ^ src.read())
    @instruction
    def ZX(cpu):
        raise NotImplementedError
