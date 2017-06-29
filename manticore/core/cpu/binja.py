from collections import defaultdict

from .abstractcpu import (
    Abi, SyscallAbi, Cpu, RegisterFile, Operand, instruction,
    ConcretizeRegister, ConcretizeRegister, ConcretizeArgument, Interruption,
    Syscall
)

from .x86 import AMD64RegFile

class BinjaRegisterFile(RegisterFile):
    def __init__(self):
        '''
        ARM Register file abstraction. GPRs use ints for read/write. APSR
        flags allow writes of bool/{1, 0} but always read bools.
        '''
        super(BinjaRegisterFile, self).__init__({})
        self._regs = {}

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
        # FIXME (theo)
        return 64

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
    # FIXME (theo) copying settings from AMD64
    # We want this to be dynamic so we should be loading this info directly
    # from binary ninja's view (probably setting them to None then setting
    # them inside the Platform?)
    max_instr_width = 15
    address_bit_size = 64
    machine = 'binja_il'

    arch = None
    mode = None
    disasm = None

    instr_ptr = None
    stack_ptr = None

    def __init__(self, memory):
        '''
        Builds a CPU model.
        :param regfile: regfile object for this CPU.
        :param memory: memory object for this CPU.
        '''
        # FIXME (theo) automatically fetch appropriate AMD64RegFile from binary
        # ninja (through a thin translation layer?)
        super(BinjaCpu, self).__init__(AMD64RegFile(aliases={'PC' : 'RIP',
                                                             'STACK': 'RSP',
                                                             'FRAME': 'RBP'}),
                                       memory)
        # Binja segments
        self._segments = {}
        self._function_hooks = defaultdict(list)
        self._instr_hooks = defaultdict(list)
        self.handlers = self.Handlers(self)

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

    def _wrap_operands(self, operands):
        return [BinjaOperand(self, op) for op in operands]

    # Adopt handlers similar from Josh Watson's 'emilator'
    class Handlers(object):
        _handlers = defaultdict(
            lambda: lambda i,j: (_ for _ in ()).throw(NotImplementedErrorError(i.operation))
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
                    hook(expr, self.emilator)

                try:
                    return handler(expr, self.emilator)
                except NotImplementedErrorError:
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
        raise NotImplementedError
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
