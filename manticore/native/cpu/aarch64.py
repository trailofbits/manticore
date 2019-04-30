import warnings

import capstone as cs
import collections
import re
import struct

from .abstractcpu import (
    Cpu, CpuException, Interruption, InstructionNotImplementedError,
    RegisterFile, Abi, SyscallAbi, Operand, instruction
)
from .arm import HighBit, Armv7Operand
from .bitwise import SInt, UInt, ASR, LSL, LSR, ROR, Mask, GetNBits
from .register import Register
from ...core.smtlib import Operators


# Unless stated otherwise, all references assume the ARM Architecture Reference
# Manual: ARMv8, for ARMv8-A architecture profile, 31 October 2018.
# ARM DDI 0487D.a, ID 103018.


class Aarch64InvalidInstruction(CpuException):
    pass


# Map different instructions to a single implementation.
OP_NAME_MAP = {
    # Make these go through 'MOV' to ensure that code path is reached.
    'MOVZ': 'MOV',
    'MOVN': 'MOV'
}


# See "C1.2.4 Condition code".
Condspec = collections.namedtuple('CondSpec', 'inverse func')
COND_MAP = {
    cs.arm64.ARM64_CC_EQ: Condspec(cs.arm64.ARM64_CC_NE, lambda n, z, c, v: z == 1),
    cs.arm64.ARM64_CC_NE: Condspec(cs.arm64.ARM64_CC_EQ, lambda n, z, c, v: z == 0),

    cs.arm64.ARM64_CC_HS: Condspec(cs.arm64.ARM64_CC_LO, lambda n, z, c, v: c == 1),
    cs.arm64.ARM64_CC_LO: Condspec(cs.arm64.ARM64_CC_HS, lambda n, z, c, v: c == 0),

    cs.arm64.ARM64_CC_MI: Condspec(cs.arm64.ARM64_CC_PL, lambda n, z, c, v: n == 1),
    cs.arm64.ARM64_CC_PL: Condspec(cs.arm64.ARM64_CC_MI, lambda n, z, c, v: n == 0),

    cs.arm64.ARM64_CC_VS: Condspec(cs.arm64.ARM64_CC_VC, lambda n, z, c, v: v == 1),
    cs.arm64.ARM64_CC_VC: Condspec(cs.arm64.ARM64_CC_VS, lambda n, z, c, v: v == 0),

    cs.arm64.ARM64_CC_HI: Condspec(cs.arm64.ARM64_CC_LS, lambda n, z, c, v: Operators.AND(c == 1, z == 0)),
    cs.arm64.ARM64_CC_LS: Condspec(cs.arm64.ARM64_CC_HI, lambda n, z, c, v: Operators.NOT(Operators.AND(c == 1, z == 0))),

    cs.arm64.ARM64_CC_GE: Condspec(cs.arm64.ARM64_CC_LT, lambda n, z, c, v: n == v),
    cs.arm64.ARM64_CC_LT: Condspec(cs.arm64.ARM64_CC_GE, lambda n, z, c, v: n != v),

    cs.arm64.ARM64_CC_GT: Condspec(cs.arm64.ARM64_CC_LE, lambda n, z, c, v: Operators.AND(z == 0, n == v)),
    cs.arm64.ARM64_CC_LE: Condspec(cs.arm64.ARM64_CC_GT, lambda n, z, c, v: Operators.NOT(Operators.AND(z == 0, n == v))),

    cs.arm64.ARM64_CC_AL: Condspec(None, lambda n, z, c, v: True),
    cs.arm64.ARM64_CC_NV: Condspec(None, lambda n, z, c, v: True)
}


# XXX: Support other system registers.
# System registers map.
SYS_REG_MAP = {
    0xc082: 'CPACR_EL1',
    0xd807: 'DCZID_EL0',
    0xde82: 'TPIDR_EL0'
}


class Aarch64RegisterFile(RegisterFile):
    Regspec = collections.namedtuple('RegSpec', 'parent size')

    # Register table.
    _table = {}

    # See "B1.2 Registers in AArch64 Execution state".

    # General-purpose registers.
    for i in range(31):
        _table[f'X{i}'] = Regspec(f'X{i}', 64)
        _table[f'W{i}'] = Regspec(f'X{i}', 32)

    # Stack pointer.
    # See "D1.8.2 SP alignment checking".
    _table['SP'] = Regspec('SP', 64)
    _table['WSP'] = Regspec('SP', 32)

    # Program counter.
    # See "D1.8.1 PC alignment checking".
    _table['PC'] = Regspec('PC', 64)

    # SIMD and FP registers.
    # See "A1.4 Supported data types".
    for i in range(32):
        _table[f'V{i}'] = Regspec(f'V{i}', 128)
        _table[f'Q{i}'] = Regspec(f'V{i}', 128)
        _table[f'D{i}'] = Regspec(f'V{i}', 64)
        _table[f'S{i}'] = Regspec(f'V{i}', 32)
        _table[f'H{i}'] = Regspec(f'V{i}', 16)
        _table[f'B{i}'] = Regspec(f'V{i}', 8)

    # SIMD and FP control and status registers.
    _table['FPCR'] = Regspec('FPCR', 64)
    _table['FPSR'] = Regspec('FPSR', 64)

    # Condition flags.
    # See "C5.2.9 NZCV, Condition Flags".
    _table['NZCV'] = Regspec('NZCV', 64)

    # Zero register.
    # See "C1.2.5 Register names".
    _table['XZR'] = Regspec('XZR', 64)
    _table['WZR'] = Regspec('XZR', 32)

    # XXX: Check the current exception level before reading from or writing to a
    # system register.
    # System registers.
    # See "D12.2 General system control registers".

    # See "D12.2.29 CPACR_EL1, Architectural Feature Access Control Register".
    _table['CPACR_EL1'] = Regspec('CPACR_EL1', 64)

    # See "D12.2.35 DCZID_EL0, Data Cache Zero ID register".
    _table['DCZID_EL0'] = Regspec('DCZID_EL0', 64)

    # See "D12.2.106 TPIDR_EL0, EL0 Read/Write Software Thread ID Register".
    _table['TPIDR_EL0'] = Regspec('TPIDR_EL0', 64)

    def __init__(self):
        # Register aliases.
        _aliases = {
            # This one is required by the 'Cpu' class.
            'STACK': 'SP',
            # See "5.1 Machine Registers" in the Procedure Call Standard for the ARM
            # 64-bit Architecture (AArch64), 22 May 2013.  ARM IHI 0055B.
            # Frame pointer.
            'FP': 'X29',
            # Intra-procedure-call temporary registers.
            'IP1': 'X17',
            'IP0': 'X16',
            # Link register.
            'LR': 'X30'
        }
        super().__init__(_aliases)

        # Used for validity checking.
        self._all_registers = set()

        # XXX: Used for 'UnicornEmulator._step'.
        self._parent_registers = set()

        # Initialize the register cache.
        # Only the full registers are stored here (called "parents").
        # If a smaller register is used, it must find its "parent" in order to
        # be stored here.
        self._registers = {}
        for name in self._table.keys():
            self._all_registers.add(name)

            parent, size = self._table[name]
            if name != parent:
                continue
            self._registers[name] = Register(size)
            self._parent_registers.add(name)

    def read(self, register):
        assert register in self
        name = self._alias(register)
        parent, size = self._table[name]
        value = self._registers[parent].read()

        # XXX: Prohibit the DC ZVA instruction until it's implemented.
        # XXX: Allow to set this when a register is declared.
        if parent == 'DCZID_EL0':
            return 0b10000

        if name != parent:
            _, parent_size = self._table[parent]
            if size < parent_size:
                value = Operators.EXTRACT(value, 0, size)

        return value

    def write(self, register, value):
        assert register in self
        name = self._alias(register)
        parent, size = self._table[name]
        if isinstance(value, int):
            assert value <= 2 ** size - 1
        else:
            assert value.size == size

        # DCZID_EL0 is read-only.
        # XXX: Allow to set this when a register is declared.
        if parent == 'DCZID_EL0':
            raise Aarch64InvalidInstruction

        # Ignore writes to the zero register.
        # XXX: Allow to set this when a register is declared.
        if parent != 'XZR':
            self._registers[parent].write(value)

    def size(self, register):
        assert register in self
        name = self._alias(register)
        return self._table[name].size

    @property
    def canonical_registers(self):
        # XXX: 'UnicornEmulator._step' goes over all registers returned from
        # here, reading from and writing to them as needed.  But 'read' and
        # 'write' methods of this class internally operate only on "parent"
        # registers.  So if '_step' reads a 32-bit register that internally
        # stores a 64-bit value, 'read' will truncate the result to 32 bits,
        # which is okay, but '_step' will then put the truncated value back in
        # the register.  So return only "parent" registers from here.
        #
        # XXX: And Unicorn doesn't support these:
        not_supported = set()
        not_supported.add('FPSR')
        not_supported.add('FPCR')

        # XXX: Unicorn doesn't allow to write to and read from system
        # registers directly (see 'arm64_reg_write' and 'arm64_reg_read').
        # The only way to propagate this information is via the MSR
        # (register) and MRS instructions, without resetting the emulator
        # state in between.
        # Note: in HEAD, this is fixed for some system registers, so revise
        # this after upgrading from 1.0.1.
        system = set(SYS_REG_MAP.values())

        return self._parent_registers - not_supported - system

    @property
    def all_registers(self):
        return self._all_registers

    # See "C5.2.9 NZCV, Condition Flags".
    @property
    def nzcv(self):
        nzcv = self.read('NZCV')
        n = Operators.EXTRACT(nzcv, 31, 1)
        z = Operators.EXTRACT(nzcv, 30, 1)
        c = Operators.EXTRACT(nzcv, 29, 1)
        v = Operators.EXTRACT(nzcv, 28, 1)
        return (n, z, c, v)

    @nzcv.setter
    def nzcv(self, value):
        for b in value:
            if isinstance(b, int):
                assert b in [0, 1]
            else:
                assert b.size == 1

        n, z, c, v = value

        n = LSL(n, 31, 64)
        z = LSL(z, 30, 64)
        c = LSL(c, 29, 64)
        v = LSL(v, 28, 64)

        result = n | z | c | v
        self.write('NZCV', result)


# XXX: Add more instructions.
class Aarch64Cpu(Cpu):
    """
    Cpu specialization handling the ARM64 architecture.
    """
    address_bit_size = 64
    max_instr_width = 4
    # XXX: Possible values: 'aarch64_be', 'aarch64', 'armv8b', 'armv8l'.
    # See 'UTS_MACHINE' and 'COMPAT_UTS_MACHINE' in the Linux kernel source.
    # https://stackoverflow.com/a/45125525
    machine = 'aarch64'
    arch = cs.CS_ARCH_ARM64
    # See "A1.3.2 The ARMv8 instruction sets".
    mode = cs.CS_ARCH_ARM

    def __init__(self, memory):
        super().__init__(Aarch64RegisterFile(), memory)

    def _wrap_operands(self, ops):
        return [Aarch64Operand(self, op) for op in ops]

    @staticmethod
    def canonicalize_instruction_name(insn):
        # Using 'mnemonic' rather than 'insn_name' because the latter doesn't
        # work for B.cond.  Instead of being set to something like 'b.eq',
        # it just returns 'b'.
        name = insn.mnemonic.upper()
        name = OP_NAME_MAP.get(name, name)
        ops = insn.operands
        name_list = name.split('.')

        # Make sure MOV (bitmask immediate) and MOV (register) go through 'MOV'.
        if (name == 'ORR' and len(ops) == 3 and
            ops[1].type == cs.arm64.ARM64_OP_REG and
            ops[1].reg in ['WZR', 'XZR'] and
            not ops[2].is_shifted()):
            name = 'MOV'
            insn._raw.mnemonic = name.lower().encode('ascii')
            del ops[1]

        # Map all B.cond variants to a single implementation.
        elif (len(name_list) == 2 and
              name_list[0] == 'B' and
              insn.cc != cs.arm64.ARM64_CC_INVALID):
            name = 'B_cond'

        # XXX: BFI is only valid when Rn != 11111:
        # https://github.com/aquynh/capstone/issues/1441
        elif (name == 'BFI' and len(ops) == 4 and
              ops[1].type == cs.arm64.ARM64_OP_REG and
              ops[1].reg in ['WZR', 'XZR']):
            name = 'BFC'
            insn._raw.mnemonic = name.lower().encode('ascii')
            del ops[1]

        # XXX: CMEQ incorrectly sets the type to 'ARM64_OP_FP' for
        # 'cmeq v0.16b, v1.16b, #0':
        # https://github.com/aquynh/capstone/issues/1443
        elif (name == 'CMEQ' and len(ops) == 3 and
              ops[2].type == cs.arm64.ARM64_OP_FP):
            ops[2]._type = cs.arm64.ARM64_OP_IMM

        return name

    @property
    def insn_bit_str(self):
        # XXX: Hardcoded endianness and instruction size.
        insn = struct.unpack("<I", self.instruction.bytes)[0]
        return f'{insn:032b}'

    def cond_holds(cpu, cond):
        return COND_MAP[cond].func(*cpu.regfile.nzcv)

    # XXX: If it becomes an issue, also invert the 'cond' field in the
    # instruction encoding.
    def invert_cond(cpu, cond):
        assert cond not in [cs.arm64.ARM64_CC_AL, cs.arm64.ARM64_CC_NV]
        return COND_MAP[cond].inverse


class Aarch64CdeclAbi(Abi):
    """Aarch64/arm64 cdecl function call ABI"""

    # XXX: Floating-point arguments are not supported.
    # For floats and doubles, the first 8 arguments are passed via registers
    # (S0-S7 for floats, D0-D7 for doubles), then on stack.
    # The result is returned in S0 for floats and D0 for doubles.

    def get_arguments(self):
        # First 8 arguments are passed via X0-X7 (or W0-W7 if they are 32-bit),
        # then on stack.

        for reg in ('X0', 'X1', 'X2', 'X3', 'X4', 'X5', 'X6', 'X7'):
            yield reg

        for address in self.values_from(self._cpu.STACK):
            yield address

    def write_result(self, result):
        self._cpu.X0 = result

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

        if self.op.type not in (
            cs.arm64.ARM64_OP_REG,
            cs.arm64.ARM64_OP_REG_MRS,
            cs.arm64.ARM64_OP_REG_MSR,
            cs.arm64.ARM64_OP_MEM,
            cs.arm64.ARM64_OP_IMM,
            cs.arm64.ARM64_OP_FP,
            cs.arm64.ARM64_OP_BARRIER
        ):
            raise NotImplementedError(
                f"Unsupported operand type: '{self.op.type}'"
            )

        self._type = self.op.type

    @classmethod
    def make_imm(cls, cpu, value):
        imm_op = cs.arm64.Arm64Op()
        imm_op.value.imm = value
        imm_op.type = cs.arm64.ARM64_OP_IMM
        imm_op = cls(cpu, imm_op)
        return imm_op

    @classmethod
    def make_reg(cls, cpu, value):
        reg_op = cs.arm64.Arm64Op()
        reg_op.value.reg = value
        reg_op.type = cs.arm64.ARM64_OP_REG
        reg_op = cls(cpu, reg_op)
        return reg_op

    @property
    def type(self):
        return self._type

    @property
    def size(self):
        # XXX: Support other operand types.
        assert self.type is cs.arm64.ARM64_OP_REG
        return self.cpu.regfile._table[self.reg].size

    def is_shifted(self):
        """
        :return: True if operand is shifted, otherwise False.
        """
        return self.op.shift.type != cs.arm64.ARM64_SFT_INVALID

    def is_extended(self):
        """
        :return: True if operand is extended, otherwise False.
        """
        return self.op.ext != cs.arm64.ARM64_EXT_INVALID

    def read(self):
        if self.type == cs.arm64.ARM64_OP_REG:
            return self.cpu.regfile.read(self.reg)
        elif self.type == cs.arm64.ARM64_OP_REG_MRS:
            name = SYS_REG_MAP.get(self.op.sys)
            if not name:
                raise NotImplementedError(
                    f"Unsupported system register: '0x{self.op.sys:x}'"
                )
            return self.cpu.regfile.read(name)
        elif self.type == cs.arm64.ARM64_OP_IMM:
            return self.op.imm
        else:
            raise NotImplementedError(f"Unsupported operand type: '{self.type}'")

    def write(self, value):
        if self.type == cs.arm64.ARM64_OP_REG:
            self.cpu.regfile.write(self.reg, value)
        elif self.type == cs.arm64.ARM64_OP_REG_MSR:
            name = SYS_REG_MAP.get(self.op.sys)
            if not name:
                raise NotImplementedError(
                    f"Unsupported system register: '0x{self.op.sys:x}'"
                )
            self.cpu.regfile.write(name, value)
        else:
            raise NotImplementedError(f"Unsupported operand type: '{self.type}'")
