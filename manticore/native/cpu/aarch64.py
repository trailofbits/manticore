import warnings

import capstone as cs

from .abstractcpu import Cpu, RegisterFile, Abi, SyscallAbi, Operand, instruction
from .arm import HighBit, Armv7Operand
from .register import Register


# Map different instructions to a single implementation.
# XXX: Avoiding this for now.
INSTRUCTION_MAPPINGS = {
    # 'MOVZ': 'MOV'
}


class Aarch64RegisterFile(RegisterFile):
    _X_REGS = tuple('X%d' % i for i in range(31))  # R0-R30 31 general-purpose registers (called X registers for 64bit)
    _V_REGS = tuple('V%d' % i for i in range(32))  # V0-V31 32 SIMD & FP registers

    def __init__(self):
        # TODO / FIXME: This is probably valid only for 'aarch32 state'
        alias_regs = {
            # 'SB': 'X9',
            # 'SL': 'X10',
            # 'FP': 'X11',
            # 'IP': 'X12',
            'STACK': 'SP',
            # 'SP': 'X13',
            # 'LR': 'X14',
            # 'PC': 'X15',
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

        # XXX: See '_table' in 'AMD64RegFile' for how to handle 32-bit
        # registers.
        # _table = {
        #     'RAX': Regspec('RAX', int, 0, 64, True),
        #     'RBX': Regspec('RBX', int, 0, 64, True),
        #     ...
        #     'EAX': Regspec('RAX', int, 0, 32, True),
        #     'EBX': Regspec('RBX', int, 0, 32, True),
        # }

        # XXX: Make sure that instructions like these work correctly:
        # movn x0, #0
        # mov  w0, #1
        # This should return 1 in X0.
        #
        # movn x0, #0
        # movk w0, #1
        # This should return 0xffff0001 in X0.
        #
        # movn x0, #0
        # movk x0, #1
        # This should return 0xffffffffffff0001 in X0.

        # V0-V31 32 SIMD&FP registers, V0 to V31.
        # Each of those can be accessed as 128-bit registers named Q0 to Q31.
        alias_regs.update(
            ('Q%d' % i, 'V%d' % i) for i in range(len(self._V_REGS))
        )

        super(Aarch64RegisterFile, self).__init__(alias_regs)

        self._regs = {}

        # 64 bit registers.
        for reg_name in self._X_REGS:
            self._regs[reg_name] = Register(64)

        # 128 bit SIMD registers.
        for reg_name in self._V_REGS:
            self._regs[reg_name] = Register(128)

        self._regs['SP'] = Register(64)
        self._regs['PC'] = Register(64)

        # Flags
        self._regs['APSR_N'] = Register(1)
        self._regs['APSR_Z'] = Register(1)
        self._regs['APSR_C'] = Register(1)
        self._regs['APSR_V'] = Register(1)
        self._regs['APSR_GE'] = Register(4)

        self._all_registers = super(Aarch64RegisterFile, self).all_registers + self._X_REGS + self._V_REGS + \
                              ('SP', 'PC')

    def read(self, register):
        register = self._alias(register)
        return self._regs[register].read()

    def write(self, register, value):
        register = self._alias(register)
        self._regs[register].write(value)

    @property
    def canonical_registers(self):
        return self._X_REGS + ('SP', 'PC')

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
    # Though there is no thumb mode in aarch64, we still have to set it as some other components may require it
    # see https://stackoverflow.com/questions/46086329/can-i-use-thumb-instructions-in-an-arm64-binary
    mode = cs.CS_ARCH_ARM

    def __init__(self, memory):
        warnings.warn('Aarch64 support is experimental')
        self._last_flags = {'C': 0, 'V': 0, 'N': 0, 'Z': 0, 'GE': 0}
        super(Aarch64Cpu, self).__init__(Aarch64RegisterFile(), memory)

    def __getstate__(self):
        state = super(Aarch64Cpu, self).__getstate__()
        state['_last_flags'] = self._last_flags
        # TODO / FIXME / REVIEWME: do we need those in aarch64? [copied from armv7]
        # state['at_symbolic_conditional'] = self._at_symbolic_conditional
        # state['_it_conditional'] = self._it_conditional
        return state

    def __setstate__(self, state):
        self._last_flags = state['_last_flags']
        # TODO / FIXME / REVIEWME: do we need those in aarch64? [copied from armv7]
        # self._at_symbolic_conditional = state['at_symbolic_conditional']
        # self._it_conditional = state['_it_conditional']
        super(Aarch64Cpu, self).__setstate__(state)

    def _wrap_operands(self, ops):
        return [Aarch64Operand(self, op) for op in ops]

    @instruction
    def MOV(cpu, dest, src):
        """
        Implement the MOV{S} instruction.

        Note: If src operand is PC, temporarily release our logical PC
        view and conform to the spec, which dictates PC = curr instr + 8

        :param Arm64Operand dest: The destination operand; register.
        :param Arm64Operand src: The source operand; register or immediate.
        """
        # XXX: Finish this.
        result = src.read()
        dest.write(result)
        # cpu.set_flags(C=carry_out, N=HighBit(result), Z=(result == 0))

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

    # Flags that are the result of arithmetic instructions. Unconditionally
    # set, but conditionally committed.
    #
    # Register file has the actual CPU flags
    def set_flags(self, **flags):
        # """
        # Note: For any unmodified flags, update _last_flags with the most recent
        # committed value. Otherwise, for example, this could happen:

        #     overflow=0
        #     instr1 computes overflow=1, updates _last_flags, doesn't commit
        #     instr2 updates all flags in _last_flags except overflow (overflow remains 1 in _last_flags)
        #     instr2 commits all in _last_flags
        #     now overflow=1 even though it should still be 0
        # """
        # unupdated_flags = self._last_flags.viewkeys() - flags.viewkeys()
        # for flag in unupdated_flags:
        #     flag_name = 'APSR_{}'.format(flag)
        #     self._last_flags[flag] = self.regfile.read(flag_name)
        # self._last_flags.update(flags)
        pass


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

    # From 'man 2 syscall':
    # arch/ABI:       arm64
    # instruction:    svc #0
    # syscall number: x8
    # arguments:      x0-x5 (arg1-arg6)
    # return value:   x0
    def syscall_number(self):
        return self._cpu.X8

    def get_arguments(self):
        return ('X{}'.format(i) for i in range(6))

    def write_result(self, result):
        self._cpu.X0 = result


class Aarch64Operand(Operand):
    def __init__(self, cpu, op, **kwargs):
        super(Aarch64Operand, self).__init__(cpu, op)

        assert self.op.type in (
            cs.arm64.ARM64_OP_REG,  # Register operand
            cs.arm64.ARM64_OP_MEM,  # Memory operand
            cs.arm64.ARM64_OP_IMM,  # Immediate operand
            cs.arm64.ARM64_OP_CIMM,  # C-Immediate
            cs.arm64.ARM64_OP_FP  # Floating-Point operand
        )

        self._type = self.op.type

    @property
    def type(self):
        return self._type

    def read(self, nbits=None, with_carry=False):
        # XXX: Finish this.
        assert nbits is None
        assert not with_carry

        if self.type == cs.arm64.ARM64_OP_REG:
            return self.cpu.regfile.read(self.reg)
        elif self.type == cs.arm64.ARM64_OP_IMM:
            return self.op.imm
        else:
            raise NotImplementedError(f"Unsupported operand type: '{self.type}'")

        # carry = self.cpu.regfile.read('APSR_C')
        # if self.type == cs.arm64.ARM64_OP_REG:
        #     value = self.cpu.regfile.read(self.reg)
        #     # PC in this case has to be set to the instruction after next. PC at this point
        #     # is already pointing to next instruction; we bump it one more.
        #     if self.reg in ('PC', 'R15'):
        #         value += self.cpu.instruction.size
        #     if self.is_shifted():
        #         shift = self.op.shift
        #         value, carry = self.cpu._shift(value, shift.type, shift.value, carry)
        #     if with_carry:
        #         return value, carry
        #     return value
        # elif self.type == cs.arm64.ARM64_OP_IMM:
        #     imm = self.op.imm
        #     if with_carry:
        #         return imm, self._get_expand_imm_carry(carry)
        #     return imm
        # elif self.type == 'coprocessor':
        #     imm = self.op.imm
        #     return imm
        # elif self.type == 'memory':
        #     val = self.cpu.read_int(self.address(), nbits)
        #     if with_carry:
        #         return val, carry
        #     return val
        # else:
        #     raise NotImplementedError("readOperand unknown type", self.op.type)

    def write(self, value, nbits=None):
        # XXX: Finish this.
        assert nbits is None

        if self.type == cs.arm64.ARM64_OP_REG:
            self.cpu.regfile.write(self.reg, value)
        else:
            raise NotImplementedError(f"Unsupported operand type: '{self.type}'")

        # if self.type == cs.arm64.ARM64_OP_REG:
        #     self.cpu.regfile.write(self.reg, value)
        # elif self.type == 'memory':
        #     raise NotImplementedError('need to impl arm store mem')
        # else:
        #     raise NotImplementedError("writeOperand unknown type", self.op.type)

    # def writeback(self, value):
    #     if self.type == cs.arm64.ARM64_OP_REG:
    #         self.write(value)
    #     elif self.type == 'memory':
    #         self.cpu.regfile.write(self.mem.base, value)
    #     else:
    #         raise NotImplementedError("writeback Operand unknown type", self.op.type)

    # def is_shifted(self):
    #     return self.op.shift.type != cs.arm.ARM_SFT_INVALID
