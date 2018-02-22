import warnings

import capstone as cs

from .abstractcpu import Cpu, RegisterFile, Abi, SyscallAbi, Operand
from .register import Register


# TODO / FIXME / REVIEWME: This is probably missing a lot of instructions
# map different instructions to a single impl here
INSTRUCTION_MAPPINGS = {
    'MOVW': 'MOV'
}


class Aarch64RegisterFile(RegisterFile):
    _R_REGS = tuple('R%d' % i for i in range(31))  # R0-R30 31 general-purpose registers
    _V_REGS = tuple('V%d' % i for i in range(32))  # V0-V31 32 SIMD & FP registers

    def __init__(self):
        # TODO / FIXME: This is probably valid only for 'aarch32 state'
        alias_regs = {
            # 'SB': 'R9',
            # 'SL': 'R10',
            # 'FP': 'R11',
            # 'IP': 'R12',
            'STACK': 'R13',
            # 'SP': 'R13',
            # 'LR': 'R14',
            'PC': 'R15',
        }

        # Via ARM Architecture Reference Manual - ARMv8, for ARMv8-A architecture profile
        # B1.2.1 Registers in AArch64 state:
        #
        # In the AArch64 application level view, an ARM processing element has:
        # R0-R30 31 general-purpose registers, R0 to R30.
        #
        # Each register can be accessed as:
        # * A 64-bit general-purpose register named X0 to X30
        # * A 32-bit general-purpose register named W0 to W30.
        alias_regs.update(
            ('R%d' % i, 'X%d' % i) for i in range(len(self._R_REGS))
        )

        # V0-V31 32 SIMD&FP registers, V0 to V31.
        # Each of those can be accessed as 128-bit registers named Q0 to Q31.
        alias_regs.update(
            ('V%d' % i, 'Q%d' % i) for i in range(len(self._V_REGS))
        )

        super(Aarch64RegisterFile, self).__init__(alias_regs)

        self._regs = {}

        # 64 bit registers.
        for reg_name in self._R_REGS:
            self._regs[reg_name] = Register(64)

        # 128 bit SIMD registers.
        for reg_name in self._V_REGS:
            self._regs[reg_name] = Register(128)

        self._all_registers = super(Aarch64RegisterFile, self).all_registers + self._R_REGS + self._V_REGS

    def read(self, register):
        register = self._alias(register)
        return self._regs[register].read()

    def write(self, register, value):
        register = self._alias(register)
        self._regs[register].write(value)

    @property
    def canonical_registers(self):
        return self._R_REGS

    @property
    def all_registers(self):
        return self._all_registers


class Aarch64Cpu(Cpu):
    """
    Cpu specialization handling the ARM64 architecture.
    """
    address_bit_size = 64
    max_instr_width = 4
    machine = 'armv8'
    arch = cs.CS_ARCH_ARM64
    mode = cs.CS_MODE_ARM

    def __init__(self, memory):
        warnings.warn('Aarch64 support is experimental')
        super(Aarch64Cpu, self).__init__(Aarch64RegisterFile(), memory)

    def _wrap_operands(self, ops):
        return [Aarch64Operand(self, op) for op in ops]

    @staticmethod
    def canonicalize_instruction_name(instr):
        name = instr.insn_name().upper()
        # XXX bypass a capstone bug that incorrectly labels some insns as mov
        if name == 'MOV':
            if instr.mnemonic.startswith('lsr'):
                return 'LSR'
            elif instr.mnemonic.startswith('lsl'):
                return 'LSL'
            elif instr.mnemonic.startswith('asr'):
                return 'ASR'
        return INSTRUCTION_MAPPINGS.get(name, name)


class Aarch64CdeclAbi(Abi):
    """Aarch64/arm64 cdecl function call ABI"""

    def get_arguments(self):
        # TODO / FIXME: Is this valid? As this might be just lower part of X0-X7 = W0-W7

        # First eight arguments are passed via X0-X7 (or W0-W7 if they are 32bit), then on stack
        for reg in ('X0', 'X1', 'X2', 'X3', 'X4', 'X5', 'X6', 'X7'):
            yield reg

        for address in self.values_from(self._cpu.STACK):
            yield address

    def write_result(self, result):
        self._cpu.W0 = result

    def ret(self):
        self._cpu.PC = self._cpu.LR


class Aarch64LinuxSyscallAbi(SyscallAbi):
    """Aarch64/arm64 Linux system call ABI"""

    # EABI standards:
    #  syscall # is in X8
    #  arguments are passed in X0-R5
    #  retval is passed in R0
    def syscall_number(self):
        return self._cpu.X8

    def get_arguments(self):
        return ('X{}'.format(i) for i in range(6))

    def write_result(self, result):
        self._cpu.R0 = result


class Aarch64Operand(Operand):
    def __init__(self, cpu, op):
        super(Aarch64Operand, self).__init__(cpu, op)

    # TODO / FIXME : Implement this!
