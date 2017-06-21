from .abstractcpu import (
    Abi, SyscallAbi, Cpu, RegisterFile, Operand, instruction,
    Interruption, Sysenter, Syscall, ConcretizeRegister, ConcretizeArgument
)

from binaryninja import LowLevelILOperation as Op

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
        pass

    def write(self, value, nbits=None):
        pass

class BinjaCpu(Cpu):
    '''
    A Virtual CPU model for Binary Ninja's IL
    '''
    def __init__(self, memory):
        '''
        Builds a CPU model.
        :param regfile: regfile object for this CPU.
        :param memory: memory object for this CPU.
        '''
        super(BinjaCpu, self).__init__(memory)
        # Binja segments
        self._segments = {}
        for segment in self.cpu.bv.segments:
            self.mem.map(segment.start,
                         segment.length,
                         segment.flags,
                         self.cpu.bv.read(segment.start, segment.length))


    def __getstate__(self):
        state = super(BinjaCpu, self).__getstate__()
        state['segments'] = self._segments
        return state

    def __setstate__(self, state):
        self._segments = state['segments']
        super(BinjaCpu, self).__setstate__(state)

    def canonicalize_instruction_name(self, instruction):
        print("Canonicalizing instruction " + str(instruction))
        return "ADD"

    @instruction
    def ADC(cpu):
        pass
    @instruction
    def ADD(cpu):
        pass
    @instruction
    def ADD_OVERFLOW(cpu):
        pass
    @instruction
    def AND(cpu):
        pass
    @instruction
    def ASR(cpu):
        pass
    @instruction
    def BOOL_TO_INT(cpu):
        pass
    @instruction
    def BP(cpu):
        pass
    @instruction
    def CALL(cpu):
        pass
    @instruction
    def CMP_E(cpu):
        pass
    @instruction
    def CMP_NE(cpu):
        pass
    @instruction
    def CMP_SGE(cpu):
        pass
    @instruction
    def CMP_SGT(cpu):
        pass
    @instruction
    def CMP_SLE(cpu):
        pass
    @instruction
    def CMP_SLT(cpu):
        pass
    @instruction
    def CMP_UGE(cpu):
        pass
    @instruction
    def CMP_UGT(cpu):
        pass
    @instruction
    def CMP_ULE(cpu):
        pass
    @instruction
    def CMP_ULT(cpu):
        pass
    @instruction
    def CONST(cpu):
        pass
    @instruction
    def CONST_PTR(cpu):
        pass
    @instruction
    def DIVS(cpu):
        pass
    @instruction
    def DIVS_DP(cpu):
        pass
    @instruction
    def DIVU(cpu):
        pass
    @instruction
    def DIVU_DP(cpu):
        pass
    @instruction
    def FLAG(cpu):
        pass
    @instruction
    def FLAG_BIT(cpu):
        pass
    @instruction
    def FLAG_COND(cpu):
        pass
    @instruction
    def GOTO(cpu):
        pass
    @instruction
    def IF(cpu):
        pass
    @instruction
    def JUMP(cpu):
        pass
    @instruction
    def JUMP_TO(cpu):
        pass
    @instruction
    def LOAD(cpu):
        pass
    @instruction
    def LOW_PART(cpu):
        pass
    @instruction
    def LSL(cpu):
        pass
    @instruction
    def LSR(cpu):
        pass
    @instruction
    def MODS(cpu):
        pass
    @instruction
    def MODS_DP(cpu):
        pass
    @instruction
    def MODU(cpu):
        pass
    @instruction
    def MODU_DP(cpu):
        pass
    @instruction
    def MUL(cpu):
        pass
    @instruction
    def MULS_DP(cpu):
        pass
    @instruction
    def MULU_DP(cpu):
        pass
    @instruction
    def NEG(cpu):
        pass
    @instruction
    def NOP(cpu):
        pass
    @instruction
    def NORET(cpu):
        pass
    @instruction
    def NOT(cpu):
        pass
    @instruction
    def OR(cpu):
        pass
    @instruction
    def POP(cpu):
        pass
    @instruction
    def PUSH(cpu):
        pass
    @instruction
    def REG(cpu):
        pass
    @instruction
    def RET(cpu):
        pass
    @instruction
    def RLC(cpu):
        pass
    @instruction
    def ROL(cpu):
        pass
    @instruction
    def ROR(cpu):
        pass
    @instruction
    def RRC(cpu):
        pass
    @instruction
    def SBB(cpu):
        pass
    @instruction
    def SET_FLAG(cpu):
        pass
    @instruction
    def SET_REG(cpu):
        pass
    @instruction
    def SET_REG_SPLIT(cpu):
        pass
    @instruction
    def STORE(cpu):
        pass
    @instruction
    def SUB(cpu):
        pass
    @instruction
    def SX(cpu):
        pass
    @instruction
    def SYSCALL(cpu):
        pass
    @instruction
    def TEST_BIT(cpu):
        pass
    @instruction
    def TRAP(cpu):
        pass
    @instruction
    def UNDEF(cpu):
        pass
    @instruction
    def UNIMPL(cpu):
        pass
    @instruction
    def UNIMPL_MEM(cpu):
        pass
    @instruction
    def XOR(cpu):
        pass
    @instruction
    def ZX(cpu):
        pass
