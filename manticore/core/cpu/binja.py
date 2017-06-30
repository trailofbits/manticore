from collections import defaultdict

from .abstractcpu import (
    Abi, SyscallAbi, Cpu, RegisterFile, Operand, instruction,
    ConcretizeRegister, ConcretizeRegister, ConcretizeArgument, Interruption,
    Syscall
)

from ...core.memory import SMemory32, SMemory64
from ...core.cpu.disasm import BinjaILDisasm

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
        self._affects = {reg : set() for reg in all_regs}

    def write(self, reg, value):
        reg = self._alias(reg)
        # FIXME we will need to be calling the appropriate setters as in x86
        self._update_cache(reg, value)
        return value

    def read(self, reg):
        reg = self._alias(reg)
        if reg in self._cache:
            return self._cache[reg]

        # FIXME we will need to be calling the appropriate getters as in x86
        value = self._registers[reg]
        self._cache[reg] = value
        return value

    def _update_cache(self, reg, value):
        reg = self._alias(reg)
        self._cache[reg] = value
        for affected in self._affects[reg]:
            assert affected != reg
            self._cache.pop(affected, None)

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
        super(BinjaOperand, self).__init__(cpu, op, **kwargs)

    @property
    def type(self):
        from binaryninja import LowLevelILOperation as Op
        type_map = {
            Op.LLIL_REG: 'register',
            Op.LLIL_CONST_PTR: 'memory',
            Op.LLIL_CONST: 'immediate'
        }

        return type_map[self.op.type]

    @property
    def size(self):
        assert self.type == 'register'
        return self.op.info.size

    def read(self, nbits=None, withCarry=False):
        raise NotImplementedError

    def write(self, value, nbits=None):
        raise NotImplementedError

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

    instr_ptr = None
    stack_ptr = None

    def __init__(self, view, memory):
        '''
        Builds a CPU model.
        :param view: BinaryNinja view.
        '''
        self.view = view
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
        return [BinjaOperand(self, op) for op in operands]

    # Adopt handlers similar from Josh Watson's 'emilator'
    class Handlers(object):
        _handlers = defaultdict(
            lambda: lambda i,j: (_ for _ in ()).throw(NotImplementedError(i.operation))
        )

        def __init__(self, cpu):
            self.cpu = cpu

        @classmethod
        def add(cls, operation):
            def add_decorator(handler):
                cls._handlers[operation] = handler
                return handler
            return add_decorator

        def __getitem__(self, op):
            hooks = self.cpu.instr_hooks[op]
            handler = self._handlers[op]

            def call_hooks(expr):
                for hook in hooks:
                    hook(expr, self.cpu)
                try:
                    return handler(expr, self.cpu)
                except NotImplementedError:
                    if not hooks:
                        raise

            return call_hooks


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
        cpu.instr_ptr = dest.value

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
        cpu.pop(dest)

    @instruction
    def PUSH(cpu, src):
        cpu.push(src)

    @instruction
    def REG(cpu):
        raise NotImplementedError
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
        print(dest)
        print(src)
        #  dest.value = src.value

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
    def XOR(cpu):
        raise NotImplementedError
    @instruction
    def ZX(cpu):
        raise NotImplementedError
