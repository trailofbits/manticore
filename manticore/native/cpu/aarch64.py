import warnings

import capstone as cs
import collections
import re
import struct

from .abstractcpu import (
    Cpu,
    CpuException,
    Interruption,
    InstructionNotImplementedError,
    RegisterFile,
    Abi,
    SyscallAbi,
    Operand,
    instruction,
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
    "MOVZ": "MOV",
    "MOVN": "MOV",
}


# See "C1.2.4 Condition code".
Condspec = collections.namedtuple("CondSpec", "inverse func")
COND_MAP = {
    cs.arm64.ARM64_CC_EQ: Condspec(cs.arm64.ARM64_CC_NE, lambda n, z, c, v: z == 1),
    cs.arm64.ARM64_CC_NE: Condspec(cs.arm64.ARM64_CC_EQ, lambda n, z, c, v: z == 0),
    cs.arm64.ARM64_CC_HS: Condspec(cs.arm64.ARM64_CC_LO, lambda n, z, c, v: c == 1),
    cs.arm64.ARM64_CC_LO: Condspec(cs.arm64.ARM64_CC_HS, lambda n, z, c, v: c == 0),
    cs.arm64.ARM64_CC_MI: Condspec(cs.arm64.ARM64_CC_PL, lambda n, z, c, v: n == 1),
    cs.arm64.ARM64_CC_PL: Condspec(cs.arm64.ARM64_CC_MI, lambda n, z, c, v: n == 0),
    cs.arm64.ARM64_CC_VS: Condspec(cs.arm64.ARM64_CC_VC, lambda n, z, c, v: v == 1),
    cs.arm64.ARM64_CC_VC: Condspec(cs.arm64.ARM64_CC_VS, lambda n, z, c, v: v == 0),
    cs.arm64.ARM64_CC_HI: Condspec(
        cs.arm64.ARM64_CC_LS, lambda n, z, c, v: Operators.AND(c == 1, z == 0)
    ),
    cs.arm64.ARM64_CC_LS: Condspec(
        cs.arm64.ARM64_CC_HI, lambda n, z, c, v: Operators.NOT(Operators.AND(c == 1, z == 0))
    ),
    cs.arm64.ARM64_CC_GE: Condspec(cs.arm64.ARM64_CC_LT, lambda n, z, c, v: n == v),
    cs.arm64.ARM64_CC_LT: Condspec(cs.arm64.ARM64_CC_GE, lambda n, z, c, v: n != v),
    cs.arm64.ARM64_CC_GT: Condspec(
        cs.arm64.ARM64_CC_LE, lambda n, z, c, v: Operators.AND(z == 0, n == v)
    ),
    cs.arm64.ARM64_CC_LE: Condspec(
        cs.arm64.ARM64_CC_GT, lambda n, z, c, v: Operators.NOT(Operators.AND(z == 0, n == v))
    ),
    cs.arm64.ARM64_CC_AL: Condspec(None, lambda n, z, c, v: True),
    cs.arm64.ARM64_CC_NV: Condspec(None, lambda n, z, c, v: True),
}


# XXX: Support other system registers.
# System registers map.
SYS_REG_MAP = {0xC082: "CPACR_EL1", 0xD807: "DCZID_EL0", 0xDE82: "TPIDR_EL0"}


class Aarch64RegisterFile(RegisterFile):
    Regspec = collections.namedtuple("RegSpec", "parent size")

    # Register table.
    _table = {}

    # See "B1.2 Registers in AArch64 Execution state".

    # General-purpose registers.
    for i in range(31):
        _table[f"X{i}"] = Regspec(f"X{i}", 64)
        _table[f"W{i}"] = Regspec(f"X{i}", 32)

    # Stack pointer.
    # See "D1.8.2 SP alignment checking".
    _table["SP"] = Regspec("SP", 64)
    _table["WSP"] = Regspec("SP", 32)

    # Program counter.
    # See "D1.8.1 PC alignment checking".
    _table["PC"] = Regspec("PC", 64)

    # SIMD and FP registers.
    # See "A1.4 Supported data types".
    for i in range(32):
        _table[f"V{i}"] = Regspec(f"V{i}", 128)
        _table[f"Q{i}"] = Regspec(f"V{i}", 128)
        _table[f"D{i}"] = Regspec(f"V{i}", 64)
        _table[f"S{i}"] = Regspec(f"V{i}", 32)
        _table[f"H{i}"] = Regspec(f"V{i}", 16)
        _table[f"B{i}"] = Regspec(f"V{i}", 8)

    # SIMD and FP control and status registers.
    _table["FPCR"] = Regspec("FPCR", 64)
    _table["FPSR"] = Regspec("FPSR", 64)

    # Condition flags.
    # See "C5.2.9 NZCV, Condition Flags".
    _table["NZCV"] = Regspec("NZCV", 64)

    # Zero register.
    # See "C1.2.5 Register names".
    _table["XZR"] = Regspec("XZR", 64)
    _table["WZR"] = Regspec("XZR", 32)

    # XXX: Check the current exception level before reading from or writing to a
    # system register.
    # System registers.
    # See "D12.2 General system control registers".

    # See "D12.2.29 CPACR_EL1, Architectural Feature Access Control Register".
    _table["CPACR_EL1"] = Regspec("CPACR_EL1", 64)

    # See "D12.2.35 DCZID_EL0, Data Cache Zero ID register".
    _table["DCZID_EL0"] = Regspec("DCZID_EL0", 64)

    # See "D12.2.106 TPIDR_EL0, EL0 Read/Write Software Thread ID Register".
    _table["TPIDR_EL0"] = Regspec("TPIDR_EL0", 64)

    def __init__(self):
        # Register aliases.
        _aliases = {
            # This one is required by the 'Cpu' class.
            "STACK": "SP",
            # See "5.1 Machine Registers" in the Procedure Call Standard for the ARM
            # 64-bit Architecture (AArch64), 22 May 2013.  ARM IHI 0055B.
            # Frame pointer.
            "FP": "X29",
            # Intra-procedure-call temporary registers.
            "IP1": "X17",
            "IP0": "X16",
            # Link register.
            "LR": "X30",
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
        if parent == "DCZID_EL0":
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
        if parent == "DCZID_EL0":
            raise Aarch64InvalidInstruction

        # Ignore writes to the zero register.
        # XXX: Allow to set this when a register is declared.
        if parent != "XZR":
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
        not_supported.add("FPSR")
        not_supported.add("FPCR")

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
        nzcv = self.read("NZCV")
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
        self.write("NZCV", result)


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
    machine = "aarch64"
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
        name_list = name.split(".")

        # Make sure MOV (bitmask immediate) and MOV (register) go through 'MOV'.
        if (
            name == "ORR"
            and len(ops) == 3
            and ops[1].type == cs.arm64.ARM64_OP_REG
            and ops[1].reg in ["WZR", "XZR"]
            and not ops[2].is_shifted()
        ):
            name = "MOV"
            insn._raw.mnemonic = name.lower().encode("ascii")
            del ops[1]

        # Map all B.cond variants to a single implementation.
        elif len(name_list) == 2 and name_list[0] == "B" and insn.cc != cs.arm64.ARM64_CC_INVALID:
            name = "B_cond"

        # XXX: BFI is only valid when Rn != 11111:
        # https://github.com/aquynh/capstone/issues/1441
        elif (
            name == "BFI"
            and len(ops) == 4
            and ops[1].type == cs.arm64.ARM64_OP_REG
            and ops[1].reg in ["WZR", "XZR"]
        ):
            name = "BFC"
            insn._raw.mnemonic = name.lower().encode("ascii")
            del ops[1]

        # XXX: CMEQ incorrectly sets the type to 'ARM64_OP_FP' for
        # 'cmeq v0.16b, v1.16b, #0':
        # https://github.com/aquynh/capstone/issues/1443
        elif name == "CMEQ" and len(ops) == 3 and ops[2].type == cs.arm64.ARM64_OP_FP:
            ops[2]._type = cs.arm64.ARM64_OP_IMM

        return name

    @property
    def insn_bit_str(self):
        # XXX: Hardcoded endianness and instruction size.
        insn = struct.unpack("<I", self.instruction.bytes)[0]
        return f"{insn:032b}"

    def cond_holds(cpu, cond):
        return COND_MAP[cond].func(*cpu.regfile.nzcv)

    # XXX: If it becomes an issue, also invert the 'cond' field in the
    # instruction encoding.
    def invert_cond(cpu, cond):
        assert cond not in [cs.arm64.ARM64_CC_AL, cs.arm64.ARM64_CC_NV]
        return COND_MAP[cond].inverse

    # XXX: Use masking when writing to the destination register?  Avoiding this
    # for now, but the assert in the 'write' method should catch such cases.

    def _adds_subs_extended_register(cpu, res_op, reg_op1, reg_op2, mnem):
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG
        assert mnem in ("add", "adds", "sub", "subs")

        insn_rx = "[01]"  # sf
        if mnem in ("add", "adds"):
            insn_rx += "0"  # op
        else:
            insn_rx += "1"  # op
        if mnem in ("add", "sub"):
            insn_rx += "0"  # S
        else:
            insn_rx += "1"  # S
        insn_rx += "01011"
        insn_rx += "00"
        insn_rx += "1"
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "[01]{3}"  # option
        insn_rx += "[01]{3}"  # imm3
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg1 = reg_op1.read()
        reg2 = reg_op2.read()

        if reg_op2.is_extended():
            ext = reg_op2.op.ext

            if ext == cs.arm64.ARM64_EXT_UXTB:
                reg2 = Operators.EXTRACT(reg2, 0, 8)
                reg2 = Operators.ZEXTEND(reg2, res_op.size)

            elif ext == cs.arm64.ARM64_EXT_UXTH:
                reg2 = Operators.EXTRACT(reg2, 0, 16)
                reg2 = Operators.ZEXTEND(reg2, res_op.size)

            elif ext == cs.arm64.ARM64_EXT_UXTW:
                reg2 = Operators.EXTRACT(reg2, 0, 32)
                reg2 = Operators.ZEXTEND(reg2, res_op.size)

            elif ext == cs.arm64.ARM64_EXT_UXTX:
                size = min(res_op.size, 64)
                reg2 = Operators.EXTRACT(reg2, 0, size)
                reg2 = Operators.ZEXTEND(reg2, size)

            elif ext == cs.arm64.ARM64_EXT_SXTB:
                reg2 = Operators.EXTRACT(reg2, 0, 8)
                reg2 = Operators.SEXTEND(reg2, 8, res_op.size)

            elif ext == cs.arm64.ARM64_EXT_SXTH:
                reg2 = Operators.EXTRACT(reg2, 0, 16)
                reg2 = Operators.SEXTEND(reg2, 16, res_op.size)

            elif ext == cs.arm64.ARM64_EXT_SXTW:
                reg2 = Operators.EXTRACT(reg2, 0, 32)
                reg2 = Operators.SEXTEND(reg2, 32, res_op.size)

            elif ext == cs.arm64.ARM64_EXT_SXTX:
                size = min(res_op.size, 64)
                reg2 = Operators.EXTRACT(reg2, 0, size)
                reg2 = Operators.SEXTEND(reg2, size, size)

            else:
                raise Aarch64InvalidInstruction

        if reg_op2.is_shifted():
            shift = reg_op2.op.shift
            assert shift.type == cs.arm64.ARM64_SFT_LSL
            assert shift.value in range(5)
            reg2 = LSL(reg2, shift.value, res_op.size)

        if mnem in ("add", "adds"):
            result, nzcv = cpu._add_with_carry(res_op.size, reg1, reg2, 0)
        else:
            result, nzcv = cpu._add_with_carry(res_op.size, reg1, ~reg2, 1)
        res_op.write(UInt(result, res_op.size))
        if mnem in ("adds", "subs"):
            cpu.regfile.nzcv = nzcv

    def _adds_subs_immediate(cpu, res_op, reg_op, imm_op, mnem):
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM
        assert mnem in ("add", "adds", "sub", "subs")

        insn_rx = "[01]"  # sf
        if mnem in ("add", "adds"):
            insn_rx += "0"  # op
        else:
            insn_rx += "1"  # op
        if mnem in ("add", "sub"):
            insn_rx += "0"  # S
        else:
            insn_rx += "1"  # S
        insn_rx += "10001"
        insn_rx += "(?!1[01])[01]{2}"  # shift != 1x
        insn_rx += "[01]{12}"  # imm12
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        imm = imm_op.op.imm
        assert imm in range(0, 4096)

        if imm_op.is_shifted():
            shift = imm_op.op.shift
            assert shift.type == cs.arm64.ARM64_SFT_LSL
            assert shift.value in [0, 12]
            imm = LSL(imm, shift.value, res_op.size)

        if mnem in ("add", "adds"):
            result, nzcv = cpu._add_with_carry(res_op.size, reg, imm, 0)
        else:
            result, nzcv = cpu._add_with_carry(res_op.size, reg, ~imm, 1)
        res_op.write(UInt(result, res_op.size))
        if mnem in ("adds", "subs"):
            cpu.regfile.nzcv = nzcv

    def _adds_subs_shifted_register(cpu, res_op, reg_op1, reg_op2, mnem):
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG
        assert mnem in ("add", "adds", "sub", "subs")

        insn_rx = "[01]"  # sf
        if mnem in ("add", "adds"):
            insn_rx += "0"  # op
        else:
            insn_rx += "1"  # op
        if mnem in ("add", "sub"):
            insn_rx += "0"  # S
        else:
            insn_rx += "1"  # S
        insn_rx += "01011"
        insn_rx += "[01]{2}"  # shift
        insn_rx += "0"
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "[01]{6}"  # imm6
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        if mnem in ("add", "adds"):

            def action(x, y):
                return cpu._add_with_carry(res_op.size, x, y, 0)

        else:

            def action(x, y):
                return cpu._add_with_carry(res_op.size, x, ~y, 1)

        if mnem in ("add", "sub"):
            flags = False
        else:
            flags = True

        cpu._shifted_register(
            res_op=res_op,
            reg_op1=reg_op1,
            reg_op2=reg_op2,
            action=action,
            flags=flags,
            shifts=[cs.arm64.ARM64_SFT_LSL, cs.arm64.ARM64_SFT_LSR, cs.arm64.ARM64_SFT_ASR],
        )

    def _add_sub_vector(cpu, res_op, reg_op1, reg_op2, add):
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        scalar_rx = "01"
        if add:
            scalar_rx += "0"  # U
        else:
            scalar_rx += "1"  # U
        scalar_rx += "11110"
        scalar_rx += "[01]{2}"  # size
        scalar_rx += "1"
        scalar_rx += "[01]{5}"  # Rm
        scalar_rx += "10000"
        scalar_rx += "1"
        scalar_rx += "[01]{5}"  # Rn
        scalar_rx += "[01]{5}"  # Rd

        vector_rx = "0"
        vector_rx += "[01]"  # Q
        if add:
            vector_rx += "0"  # U
        else:
            vector_rx += "1"  # U
        vector_rx += "01110"
        vector_rx += "[01]{2}"  # size
        vector_rx += "1"
        vector_rx += "[01]{5}"  # Rm
        vector_rx += "10000"
        vector_rx += "1"
        vector_rx += "[01]{5}"  # Rn
        vector_rx += "[01]{5}"  # Rd

        assert re.match(scalar_rx, cpu.insn_bit_str) or re.match(vector_rx, cpu.insn_bit_str)

        # XXX: Check if trapped.

        reg1 = reg_op1.read()
        reg2 = reg_op2.read()
        vas = res_op.op.vas

        if vas == cs.arm64.ARM64_VAS_8B:
            elem_size = 8
            elem_count = 8

        elif vas == cs.arm64.ARM64_VAS_16B:
            elem_size = 8
            elem_count = 16

        elif vas == cs.arm64.ARM64_VAS_4H:
            elem_size = 16
            elem_count = 4

        elif vas == cs.arm64.ARM64_VAS_8H:
            elem_size = 16
            elem_count = 8

        elif vas == cs.arm64.ARM64_VAS_2S:
            elem_size = 32
            elem_count = 2

        elif vas == cs.arm64.ARM64_VAS_4S:
            elem_size = 32
            elem_count = 4

        elif vas == cs.arm64.ARM64_VAS_2D:
            elem_size = 64
            elem_count = 2

        elif vas == cs.arm64.ARM64_VAS_INVALID:  # scalar
            assert res_op.size == 64
            assert reg_op1.size == 64
            assert reg_op2.size == 64
            elem_size = 64
            elem_count = 1

        else:
            raise Aarch64InvalidInstruction

        result = 0
        for i in range(elem_count):
            elem1 = Operators.EXTRACT(reg1, i * elem_size, elem_size)
            elem2 = Operators.EXTRACT(reg2, i * elem_size, elem_size)
            if add:
                elem = UInt(elem1 + elem2, elem_size)
            else:
                elem = UInt(elem1 - elem2, elem_size)
            elem = Operators.ZEXTEND(elem, res_op.size)
            result |= elem << (i * elem_size)

        result = UInt(result, res_op.size)
        res_op.write(result)

    # XXX: Copied from '_ADD' in 'arm.py'.
    def _add_with_carry(cpu, size, x, y, carry_in):
        y = Operators.ZEXTEND(y, size)

        usum = UInt(x, size * 2)
        usum += UInt(y, size * 2)
        usum += UInt(carry_in, 1)

        ssum = SInt(Operators.SEXTEND(x, size, size * 2), size * 2)
        ssum += SInt(Operators.SEXTEND(y, size, size * 2), size * 2)
        ssum += UInt(carry_in, 1)

        res = GetNBits(usum, size)

        ures = UInt(res, size * 2)
        sres = SInt(Operators.SEXTEND(res, size, size * 2), size * 2)

        n = Operators.EXTRACT(res, size - 1, 1)
        z = Operators.ITEBV(1, res == 0, 1, 0)
        c = Operators.ITEBV(1, ures == usum, 0, 1)
        v = Operators.ITEBV(1, sres == ssum, 0, 1)

        return (res, (n, z, c, v))

    def _ccmp_imm_reg(cpu, reg_op, reg_imm_op, nzcv_op, imm):
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert reg_imm_op.type in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]
        assert nzcv_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # sf
        insn_rx += "1"  # op
        insn_rx += "1"
        insn_rx += "11010010"
        if imm:
            insn_rx += "[01]{5}"  # imm5
        else:
            insn_rx += "[01]{5}"  # Rm
        insn_rx += "[01]{4}"  # cond
        if imm:
            insn_rx += "1"
        else:
            insn_rx += "0"
        insn_rx += "0"
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "0"
        insn_rx += "[01]{4}"  # nzcv

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        if imm:
            reg_imm = reg_imm_op.op.imm
        else:
            reg_imm = reg_imm_op.read()
        nzcv = nzcv_op.op.imm

        assert nzcv in range(16)

        # XXX: This is only necessary because of 'ITEBV'.  If more code needs
        # this, consider just returning NZCV as a single value from
        # '_add_with_carry'.
        def make_nzcv(n, z, c, v):
            n = Operators.ZEXTEND(n, 4)
            z = Operators.ZEXTEND(z, 4)
            c = Operators.ZEXTEND(c, 4)
            v = Operators.ZEXTEND(v, 4)
            nzcv = LSL(n, 3, 4)
            nzcv |= LSL(z, 2, 4)
            nzcv |= LSL(c, 1, 4)
            nzcv |= LSL(v, 0, 4)
            return nzcv

        nzcv = Operators.ITEBV(
            4,
            cpu.cond_holds(cpu.instruction.cc),
            make_nzcv(*cpu._add_with_carry(reg_op.size, reg, ~reg_imm, 1)[1]),
            nzcv,
        )

        n = Operators.EXTRACT(nzcv, 3, 1)
        z = Operators.EXTRACT(nzcv, 2, 1)
        c = Operators.EXTRACT(nzcv, 1, 1)
        v = Operators.EXTRACT(nzcv, 0, 1)

        cpu.regfile.nzcv = (n, z, c, v)

    def _cmeq(cpu, res_op, reg_op, reg_imm_op, register):
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert reg_imm_op.type in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]

        scalar_rx = "01"
        if register:
            scalar_rx += "1"  # U
        else:
            scalar_rx += "0"  # U
        scalar_rx += "11110"
        scalar_rx += "[01]{2}"  # size
        if register:
            scalar_rx += "1"
            scalar_rx += "[01]{5}"  # Rm
            scalar_rx += "10001"
            scalar_rx += "1"
        else:
            scalar_rx += "10000"
            scalar_rx += "0100"
            scalar_rx += "1"  # op
            scalar_rx += "10"
        scalar_rx += "[01]{5}"  # Rn
        scalar_rx += "[01]{5}"  # Rd

        vector_rx = "0"
        vector_rx += "[01]"  # Q
        if register:
            vector_rx += "1"  # U
        else:
            vector_rx += "0"  # U
        vector_rx += "01110"
        vector_rx += "[01]{2}"  # size
        if register:
            vector_rx += "1"
            vector_rx += "[01]{5}"  # Rm
            vector_rx += "10001"
            vector_rx += "1"
        else:
            vector_rx += "10000"
            vector_rx += "0100"
            vector_rx += "1"  # op
            vector_rx += "10"
        vector_rx += "[01]{5}"  # Rn
        vector_rx += "[01]{5}"  # Rd

        assert re.match(scalar_rx, cpu.insn_bit_str) or re.match(vector_rx, cpu.insn_bit_str)

        # XXX: Check if trapped.

        op1 = reg_op.read()
        op2 = reg_imm_op.read()

        if not register:
            assert op2 == 0

        vas = res_op.op.vas

        if vas == cs.arm64.ARM64_VAS_8B:
            elem_size = 8
            elem_count = 8

        elif vas == cs.arm64.ARM64_VAS_16B:
            elem_size = 8
            elem_count = 16

        elif vas == cs.arm64.ARM64_VAS_4H:
            elem_size = 16
            elem_count = 4

        elif vas == cs.arm64.ARM64_VAS_8H:
            elem_size = 16
            elem_count = 8

        elif vas == cs.arm64.ARM64_VAS_2S:
            elem_size = 32
            elem_count = 2

        elif vas == cs.arm64.ARM64_VAS_4S:
            elem_size = 32
            elem_count = 4

        elif vas == cs.arm64.ARM64_VAS_2D:
            elem_size = 64
            elem_count = 2

        elif vas == cs.arm64.ARM64_VAS_INVALID:  # scalar
            assert res_op.size == 64
            assert reg_op.size == 64
            assert not register or reg_imm_op.size == 64
            elem_size = 64
            elem_count = 1

        else:
            raise Aarch64InvalidInstruction

        result = 0
        for i in range(elem_count):
            elem1 = Operators.EXTRACT(op1, i * elem_size, elem_size)
            elem2 = Operators.EXTRACT(op2, i * elem_size, elem_size)
            elem = Operators.ITEBV(elem_size, elem1 == elem2, Mask(elem_size), 0)
            elem = Operators.ZEXTEND(elem, res_op.size)
            result |= elem << (i * elem_size)

        result = UInt(result, res_op.size)
        res_op.write(result)

    def _shifted_register(cpu, res_op, reg_op1, reg_op2, action, shifts, flags=False):
        reg1 = reg_op1.read()
        reg2 = reg_op2.read()
        reg2_size = cpu.regfile.size(reg_op2.reg)

        if reg_op2.is_shifted():
            shift = reg_op2.shift

            assert (res_op.size == 32 and shift.value in range(0, 32)) or (
                res_op.size == 64 and shift.value in range(0, 64)
            )

            if shift.type == cs.arm64.ARM64_SFT_LSL and shift.type in shifts:
                reg2 = LSL(reg2, shift.value, reg2_size)

            elif shift.type == cs.arm64.ARM64_SFT_LSR and shift.type in shifts:
                reg2 = LSR(reg2, shift.value, reg2_size)

            elif shift.type == cs.arm64.ARM64_SFT_ASR and shift.type in shifts:
                reg2 = ASR(reg2, shift.value, reg2_size)

            elif shift.type == cs.arm64.ARM64_SFT_ROR and shift.type in shifts:
                reg2 = ROR(reg2, shift.value, reg2_size)

            else:
                raise Aarch64InvalidInstruction

        result, nzcv = action(reg1, reg2)
        if flags:
            cpu.regfile.nzcv = nzcv
        result = UInt(result, res_op.size)
        res_op.write(result)

    def _ldp_stp(cpu, reg_op1, reg_op2, mem_op, mimm_op, ldp):
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG
        assert mem_op.type is cs.arm64.ARM64_OP_MEM
        assert not mimm_op or mimm_op.type is cs.arm64.ARM64_OP_IMM

        post_index_rx = "[01]{2}"  # opc
        post_index_rx += "101"
        post_index_rx += "[01]"
        post_index_rx += "001"
        if ldp:
            post_index_rx += "1"  # L
        else:
            post_index_rx += "0"  # L
        post_index_rx += "[01]{7}"  # imm7
        post_index_rx += "[01]{5}"  # Rt2
        post_index_rx += "[01]{5}"  # Rn
        post_index_rx += "[01]{5}"  # Rt

        pre_index_rx = "[01]{2}"  # opc
        pre_index_rx += "101"
        pre_index_rx += "[01]"
        pre_index_rx += "011"
        if ldp:
            pre_index_rx += "1"  # L
        else:
            pre_index_rx += "0"  # L
        pre_index_rx += "[01]{7}"  # imm7
        pre_index_rx += "[01]{5}"  # Rt2
        pre_index_rx += "[01]{5}"  # Rn
        pre_index_rx += "[01]{5}"  # Rt

        signed_offset_rx = "[01]{2}"  # opc
        signed_offset_rx += "101"
        signed_offset_rx += "[01]"
        signed_offset_rx += "010"
        if ldp:
            signed_offset_rx += "1"  # L
        else:
            signed_offset_rx += "0"  # L
        signed_offset_rx += "[01]{7}"  # imm7
        signed_offset_rx += "[01]{5}"  # Rt2
        signed_offset_rx += "[01]{5}"  # Rn
        signed_offset_rx += "[01]{5}"  # Rt

        assert (
            re.match(post_index_rx, cpu.insn_bit_str)
            or re.match(pre_index_rx, cpu.insn_bit_str)
            or re.match(signed_offset_rx, cpu.insn_bit_str)
        )

        # XXX: SIMD&FP: check if trapped.

        base = cpu.regfile.read(mem_op.mem.base)
        imm = mem_op.mem.disp

        if mimm_op:  # post-indexed
            wback = mimm_op.op.imm
        else:
            wback = imm  # use it for writeback if applicable

        if ldp:
            result1 = cpu.read_int(base + imm, reg_op1.size)
            reg_op1.write(result1)

            result2 = cpu.read_int(base + imm + reg_op1.size // 8, reg_op2.size)
            reg_op2.write(result2)
        else:
            reg1 = reg_op1.read()
            cpu.write_int(base + imm, reg1, reg_op1.size)

            reg2 = reg_op2.read()
            cpu.write_int(base + imm + reg_op1.size // 8, reg2, reg_op2.size)

        if cpu.instruction.writeback:
            cpu.regfile.write(mem_op.mem.base, base + wback)

    def _ldr_str_immediate(cpu, reg_op, mem_op, mimm_op, ldr, size=None, sextend=False):
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert mem_op.type is cs.arm64.ARM64_OP_MEM
        assert not mimm_op or mimm_op.type is cs.arm64.ARM64_OP_IMM

        if size == 8:
            post_index_rx = "00"  # size
        elif size == 16:
            post_index_rx = "01"  # size
        else:
            post_index_rx = "1[01]"  # size
        post_index_rx += "111"
        post_index_rx += "0"
        post_index_rx += "00"
        if ldr and sextend:
            post_index_rx += "10"  # opc
        elif ldr:
            post_index_rx += "01"  # opc
        else:
            post_index_rx += "00"  # opc
        post_index_rx += "0"
        post_index_rx += "[01]{9}"  # imm9
        post_index_rx += "01"
        post_index_rx += "[01]{5}"  # Rn
        post_index_rx += "[01]{5}"  # Rt

        if size == 8:
            pre_index_rx = "00"  # size
        elif size == 16:
            pre_index_rx = "01"  # size
        else:
            pre_index_rx = "1[01]"  # size
        pre_index_rx += "111"
        pre_index_rx += "0"
        pre_index_rx += "00"
        if ldr and sextend:
            pre_index_rx += "10"  # opc
        elif ldr:
            pre_index_rx += "01"  # opc
        else:
            pre_index_rx += "00"  # opc
        pre_index_rx += "0"
        pre_index_rx += "[01]{9}"  # imm9
        pre_index_rx += "11"
        pre_index_rx += "[01]{5}"  # Rn
        pre_index_rx += "[01]{5}"  # Rt

        if size == 8:
            unsigned_offset_rx = "00"  # size
        elif size == 16:
            unsigned_offset_rx = "01"  # size
        else:
            unsigned_offset_rx = "1[01]"  # size
        unsigned_offset_rx += "111"
        unsigned_offset_rx += "0"
        unsigned_offset_rx += "01"
        if ldr and sextend:
            unsigned_offset_rx += "10"  # opc
        elif ldr:
            unsigned_offset_rx += "01"  # opc
        else:
            unsigned_offset_rx += "00"  # opc
        unsigned_offset_rx += "[01]{12}"  # imm12
        unsigned_offset_rx += "[01]{5}"  # Rn
        unsigned_offset_rx += "[01]{5}"  # Rt

        assert (
            re.match(post_index_rx, cpu.insn_bit_str)
            or re.match(pre_index_rx, cpu.insn_bit_str)
            or re.match(unsigned_offset_rx, cpu.insn_bit_str)
        )

        base = cpu.regfile.read(mem_op.mem.base)
        imm = mem_op.mem.disp
        size = size if size else reg_op.size

        if mimm_op:  # post-indexed
            wback = mimm_op.op.imm
        else:
            wback = imm  # use it for writeback if applicable

        if ldr:
            result = cpu.read_int(base + imm, size)
            if sextend:
                result = Operators.SEXTEND(result, size, reg_op.size)
            else:
                result = Operators.ZEXTEND(result, reg_op.size)
            reg_op.write(result)
        else:
            reg = reg_op.read()
            cpu.write_int(base + imm, reg, size)

        if cpu.instruction.writeback:
            cpu.regfile.write(mem_op.mem.base, base + wback)

    def _ldr_str_register(cpu, reg_op, mem_op, ldr, size=None, sextend=False):
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert mem_op.type is cs.arm64.ARM64_OP_MEM

        if size == 8:
            insn_rx = "00"  # size
        elif size == 16:
            insn_rx = "01"  # size
        else:
            insn_rx = "1[01]"  # size
        insn_rx += "111"
        insn_rx += "0"
        insn_rx += "00"
        if ldr and sextend:
            insn_rx += "10"  # opc
        elif ldr:
            insn_rx += "01"  # opc
        else:
            insn_rx += "00"  # opc
        insn_rx += "1"
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "[01]{3}"  # option
        insn_rx += "[01]"  # S
        insn_rx += "10"
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rt

        assert re.match(insn_rx, cpu.insn_bit_str)

        base = cpu.regfile.read(mem_op.mem.base)
        index = cpu.regfile.read(mem_op.mem.index)
        index_size = cpu.regfile.size(mem_op.mem.index)
        size = size if size else reg_op.size

        if mem_op.is_extended():
            ext = mem_op.op.ext

            assert ext in [
                cs.arm64.ARM64_EXT_UXTW,
                cs.arm64.ARM64_EXT_SXTW,
                cs.arm64.ARM64_EXT_SXTX,
            ]

            if ext == cs.arm64.ARM64_EXT_UXTW:
                index = Operators.ZEXTEND(index, cpu.address_bit_size)
                index_size = cpu.address_bit_size

            elif ext == cs.arm64.ARM64_EXT_SXTW:
                index = Operators.SEXTEND(index, index_size, cpu.address_bit_size)
                index_size = cpu.address_bit_size

            elif ext == cs.arm64.ARM64_EXT_SXTX:
                index = Operators.SEXTEND(index, index_size, cpu.address_bit_size)
                index_size = cpu.address_bit_size

            else:
                raise Aarch64InvalidInstruction

        if mem_op.is_shifted():
            shift = mem_op.op.shift
            assert shift.type == cs.arm64.ARM64_SFT_LSL
            index = LSL(index, shift.value, index_size)

        base = UInt(base, cpu.address_bit_size)
        index = SInt(index, cpu.address_bit_size)

        if ldr:
            result = cpu.read_int(base + index, size)
            if sextend:
                result = Operators.SEXTEND(result, size, cpu.address_bit_size)
            reg_op.write(result)
        else:
            reg = reg_op.read()
            cpu.write_int(base + index, reg, size)

    def _ldr_literal(cpu, reg_op, imm_op, size=None, sextend=False):
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        if sextend:
            insn_rx = "10"  # opc
        else:
            insn_rx = "0[01]"  # opc
        insn_rx += "011"
        insn_rx += "0"
        insn_rx += "00"
        insn_rx += "[01]{19}"  # imm19
        insn_rx += "[01]{5}"  # Rt

        assert re.match(insn_rx, cpu.insn_bit_str)

        size = size if size else reg_op.size
        imm = imm_op.op.imm

        result = cpu.read_int(imm, size)
        if sextend:
            result = Operators.SEXTEND(result, size, cpu.address_bit_size)
        reg_op.write(result)

    def _ldur_stur(cpu, reg_op, mem_op, ldur):
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert mem_op.type is cs.arm64.ARM64_OP_MEM

        insn_rx = "1[01]"  # size
        insn_rx += "111"
        insn_rx += "0"
        insn_rx += "00"
        if ldur:
            insn_rx += "01"  # opc
        else:
            insn_rx += "00"  # opc
        insn_rx += "0"
        insn_rx += "[01]{9}"  # imm9
        insn_rx += "00"
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rt

        assert re.match(insn_rx, cpu.insn_bit_str)

        base = cpu.regfile.read(mem_op.mem.base)
        imm = mem_op.mem.disp

        assert imm >= -256 and imm <= 255

        if ldur:
            result = cpu.read_int(base + imm, reg_op.size)
            reg_op.write(result)
        else:
            reg = reg_op.read()
            cpu.write_int(base + imm, reg, reg_op.size)

    def _ADD_extended_register(cpu, res_op, reg_op1, reg_op2):
        """
        ADD (extended register).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        cpu._adds_subs_extended_register(res_op, reg_op1, reg_op2, mnem="add")

    def _ADD_immediate(cpu, res_op, reg_op, imm_op):
        """
        ADD (immediate).

        :param res_op: destination register.
        :param reg_op: source register.
        :param imm_op: immediate.
        """
        cpu._adds_subs_immediate(res_op, reg_op, imm_op, mnem="add")

    def _ADD_shifted_register(cpu, res_op, reg_op1, reg_op2):
        """
        ADD (shifted register).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        cpu._adds_subs_shifted_register(res_op, reg_op1, reg_op2, mnem="add")

    def _ADD_vector(cpu, res_op, reg_op1, reg_op2):
        """
        ADD (vector).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        cpu._add_sub_vector(res_op, reg_op1, reg_op2, add=True)

    @instruction
    def ADD(cpu, res_op, reg_op, reg_imm_op):
        """
        Combines ADD (extended register), ADD (immediate), ADD (shifted
        register), and ADD (vector).

        :param res_op: destination register.
        :param reg_op: source register.
        :param reg_imm_op: source register or immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert reg_imm_op.type in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]

        bit21 = cpu.insn_bit_str[-22]
        bit24 = cpu.insn_bit_str[-25]

        if reg_imm_op.type == cs.arm64.ARM64_OP_IMM:
            cpu._ADD_immediate(res_op, reg_op, reg_imm_op)

        elif reg_imm_op.type == cs.arm64.ARM64_OP_REG and bit24 == "0":
            cpu._ADD_vector(res_op, reg_op, reg_imm_op)

        elif reg_imm_op.type == cs.arm64.ARM64_OP_REG and bit24 == "1" and bit21 == "0":
            cpu._ADD_shifted_register(res_op, reg_op, reg_imm_op)

        elif reg_imm_op.type == cs.arm64.ARM64_OP_REG and bit24 == "1" and bit21 == "1":
            cpu._ADD_extended_register(res_op, reg_op, reg_imm_op)

        else:
            raise Aarch64InvalidInstruction

    def _ADDP_scalar(cpu, res_op, reg_op):
        """
        ADDP (scalar).

        :param res_op: destination register.
        :param reg_op: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx = "01"
        insn_rx += "0"
        insn_rx += "11110"
        insn_rx += "[01]{2}"  # size
        insn_rx += "11000"
        insn_rx += "11011"
        insn_rx += "10"
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # XXX: Check if trapped.

        reg = reg_op.read()

        assert reg_op.op.vas == cs.arm64.ARM64_VAS_2D
        hi = Operators.EXTRACT(reg, 64, 64)
        lo = Operators.EXTRACT(reg, 0, 64)

        result = UInt(hi + lo, res_op.size)
        res_op.write(result)

    def _ADDP_vector(cpu, res_op, reg_op1, reg_op2):
        """
        ADDP (vector).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx = "0"
        insn_rx += "[01]"  # Q
        insn_rx += "0"
        insn_rx += "01110"
        insn_rx += "[01]{2}"  # size
        insn_rx += "1"
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "10111"
        insn_rx += "1"
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # XXX: Check if trapped.

        reg1 = reg_op1.read()
        reg2 = reg_op2.read()
        vas = res_op.op.vas

        if vas == cs.arm64.ARM64_VAS_8B:
            elem_size = 8
            elem_count = 8

        elif vas == cs.arm64.ARM64_VAS_16B:
            elem_size = 8
            elem_count = 16

        elif vas == cs.arm64.ARM64_VAS_4H:
            elem_size = 16
            elem_count = 4

        elif vas == cs.arm64.ARM64_VAS_8H:
            elem_size = 16
            elem_count = 8

        elif vas == cs.arm64.ARM64_VAS_2S:
            elem_size = 32
            elem_count = 2

        elif vas == cs.arm64.ARM64_VAS_4S:
            elem_size = 32
            elem_count = 4

        elif vas == cs.arm64.ARM64_VAS_2D:
            elem_size = 64
            elem_count = 2

        else:
            raise Aarch64InvalidInstruction

        size = elem_size * elem_count

        reg1 = Operators.EXTRACT(reg1, 0, size)
        reg2 = Operators.EXTRACT(reg2, 0, size)

        reg1 = Operators.ZEXTEND(reg1, size * 2)
        reg2 = Operators.ZEXTEND(reg2, size * 2)

        concat = UInt((reg2 << size) | reg1, size * 2)

        result = 0
        for i in range(elem_count):
            elem1 = Operators.EXTRACT(concat, (2 * i) * elem_size, elem_size)
            elem2 = Operators.EXTRACT(concat, (2 * i + 1) * elem_size, elem_size)
            elem = UInt(elem1 + elem2, elem_size)
            elem = Operators.ZEXTEND(elem, res_op.size)
            result |= elem << (i * elem_size)

        result = UInt(result, res_op.size)
        res_op.write(result)

    @instruction
    def ADDP(cpu, res_op, reg_op1, mreg_op2=None):
        """
        Combines ADDP (scalar) and ADDP (vector).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param mreg_op2: None or source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert not mreg_op2 or mreg_op2.type is cs.arm64.ARM64_OP_REG

        if mreg_op2:
            cpu._ADDP_vector(res_op, reg_op1, mreg_op2)
        else:
            cpu._ADDP_scalar(res_op, reg_op1)

    def _ADDS_extended_register(cpu, res_op, reg_op1, reg_op2):
        """
        ADDS (extended register).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        cpu._adds_subs_extended_register(res_op, reg_op1, reg_op2, mnem="adds")

    def _ADDS_immediate(cpu, res_op, reg_op, imm_op):
        """
        ADDS (immediate).

        :param res_op: destination register.
        :param reg_op: source register.
        :param imm_op: immediate.
        """
        cpu._adds_subs_immediate(res_op, reg_op, imm_op, mnem="adds")

    def _ADDS_shifted_register(cpu, res_op, reg_op1, reg_op2):
        """
        ADDS (shifted register).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        cpu._adds_subs_shifted_register(res_op, reg_op1, reg_op2, mnem="adds")

    @instruction
    def ADDS(cpu, res_op, reg_op, reg_imm_op):
        """
        Combines ADDS (extended register), ADDS (immediate), and ADDS (shifted
        register).

        :param res_op: destination register.
        :param reg_op: source register.
        :param reg_imm_op: source register or immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert reg_imm_op.type in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]

        bit21 = cpu.insn_bit_str[-22]

        if reg_imm_op.type == cs.arm64.ARM64_OP_IMM:
            cpu._ADDS_immediate(res_op, reg_op, reg_imm_op)

        elif reg_imm_op.type == cs.arm64.ARM64_OP_REG and bit21 == "0":
            cpu._ADDS_shifted_register(res_op, reg_op, reg_imm_op)

        elif reg_imm_op.type == cs.arm64.ARM64_OP_REG and bit21 == "1":
            cpu._ADDS_extended_register(res_op, reg_op, reg_imm_op)

        else:
            raise Aarch64InvalidInstruction

    @instruction
    def ADR(cpu, res_op, imm_op):
        """
        ADR.

        :param res_op: destination register.
        :param imm_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "0"  # op
        insn_rx += "[01]{2}"  # immlo
        insn_rx += "10000"
        insn_rx += "[01]{19}"  # immhi
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        imm = imm_op.op.imm  # PC + offset
        res_op.write(imm)

    @instruction
    def ADRP(cpu, res_op, imm_op):
        """
        ADRP.

        :param res_op: destination register.
        :param imm_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "1"  # op
        insn_rx += "[01]{2}"  # immlo
        insn_rx += "10000"
        insn_rx += "[01]{19}"  # immhi
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        imm = imm_op.op.imm  # PC + offset
        res_op.write(imm)

    def _AND_immediate(cpu, res_op, reg_op, imm_op):
        """
        AND (immediate).

        :param res_op: destination register.
        :param reg_op: source register.
        :param imm_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # sf
        insn_rx += "00"  # opc
        insn_rx += "100100"
        insn_rx += "[01]"  # N
        insn_rx += "[01]{6}"  # immr
        insn_rx += "[01]{6}"  # imms
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        imm = imm_op.op.imm
        result = UInt(reg & imm, res_op.size)
        res_op.write(result)

    def _AND_shifted_register(cpu, res_op, reg_op1, reg_op2):
        """
        AND (shifted register).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "00"  # opc
        insn_rx += "01010"
        insn_rx += "[01]{2}"  # shift
        insn_rx += "0"  # N
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "[01]{6}"  # imm6
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        cpu._shifted_register(
            res_op=res_op,
            reg_op1=reg_op1,
            reg_op2=reg_op2,
            action=lambda x, y: (x & y, None),
            shifts=[
                cs.arm64.ARM64_SFT_LSL,
                cs.arm64.ARM64_SFT_LSR,
                cs.arm64.ARM64_SFT_ASR,
                cs.arm64.ARM64_SFT_ROR,
            ],
        )

    def _AND_vector(cpu, res_op, reg_op1, reg_op2):
        """
        AND (vector).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx = "0"
        insn_rx += "[01]"  # Q
        insn_rx += "0"
        insn_rx += "01110"
        insn_rx += "00"  # size
        insn_rx += "1"
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "00011"
        insn_rx += "1"
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # XXX: Check if trapped.

        reg1 = reg_op1.read()
        reg2 = reg_op2.read()
        vas = res_op.op.vas

        if vas == cs.arm64.ARM64_VAS_8B:
            reg1 = Operators.EXTRACT(reg1, 0, 64)
            reg2 = Operators.EXTRACT(reg2, 0, 64)

        elif vas == cs.arm64.ARM64_VAS_16B:
            pass

        else:
            raise Aarch64InvalidInstruction

        result = UInt(reg1 & reg2, res_op.size)
        res_op.write(result)

    @instruction
    def AND(cpu, res_op, reg_op, reg_imm_op):
        """
        Combines AND (immediate), AND (shifted register), and AND (vector).

        :param res_op: destination register.
        :param reg_op: source register.
        :param reg_imm_op: source register or immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert reg_imm_op.type in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]

        bit21 = cpu.insn_bit_str[-22]

        if reg_imm_op.type == cs.arm64.ARM64_OP_REG and bit21 == "0":
            cpu._AND_shifted_register(res_op, reg_op, reg_imm_op)

        elif reg_imm_op.type == cs.arm64.ARM64_OP_REG and bit21 == "1":
            cpu._AND_vector(res_op, reg_op, reg_imm_op)

        elif reg_imm_op.type == cs.arm64.ARM64_OP_IMM:
            cpu._AND_immediate(res_op, reg_op, reg_imm_op)

        else:
            raise Aarch64InvalidInstruction

    def _ANDS_immediate(cpu, res_op, reg_op, imm_op):
        """
        ANDS (immediate).

        :param res_op: destination register.
        :param reg_op: source register.
        :param imm_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # sf
        insn_rx += "11"  # opc
        insn_rx += "100100"
        insn_rx += "[01]"  # N
        insn_rx += "[01]{6}"  # immr
        insn_rx += "[01]{6}"  # imms
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        imm = imm_op.op.imm
        result = UInt(reg & imm, res_op.size)
        res_op.write(result)

        n = Operators.EXTRACT(result, res_op.size - 1, 1)
        z = Operators.ITEBV(1, result == 0, 1, 0)
        cpu.regfile.nzcv = (n, z, 0, 0)

    def _ANDS_shifted_register(cpu, res_op, reg_op1, reg_op2):
        """
        ANDS (shifted register).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "11"  # opc
        insn_rx += "01010"
        insn_rx += "[01]{2}"  # shift
        insn_rx += "0"  # N
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "[01]{6}"  # imm6
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        def action(x, y):
            result = x & y
            n = Operators.EXTRACT(result, res_op.size - 1, 1)
            z = Operators.ITEBV(1, result == 0, 1, 0)
            return (result, (n, z, 0, 0))

        cpu._shifted_register(
            res_op=res_op,
            reg_op1=reg_op1,
            reg_op2=reg_op2,
            action=lambda x, y: action(x, y),
            flags=True,
            shifts=[
                cs.arm64.ARM64_SFT_LSL,
                cs.arm64.ARM64_SFT_LSR,
                cs.arm64.ARM64_SFT_ASR,
                cs.arm64.ARM64_SFT_ROR,
            ],
        )

    @instruction
    def ANDS(cpu, res_op, reg_op, reg_imm_op):
        """
        Combines ANDS (immediate) and ANDS (shifted register).

        :param res_op: destination register.
        :param reg_op: source register.
        :param reg_imm_op: source register or immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert reg_imm_op.type in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]

        if reg_imm_op.type == cs.arm64.ARM64_OP_REG:
            cpu._ANDS_shifted_register(res_op, reg_op, reg_imm_op)

        elif reg_imm_op.type == cs.arm64.ARM64_OP_IMM:
            cpu._ANDS_immediate(res_op, reg_op, reg_imm_op)

        else:
            raise Aarch64InvalidInstruction

    def _ASR_immediate(cpu, res_op, reg_op, immr_op):
        """
        ASR (immediate).

        :param res_op: destination register.
        :param reg_op: source register.
        :param immr_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert immr_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # sf
        insn_rx += "00"  # opc
        insn_rx += "100110"
        insn_rx += "[01]"  # N
        insn_rx += "[01]{6}"  # immr
        insn_rx += "[01]1{5}"  # imms
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # Fake an immediate operand.
        imms_op = Aarch64Operand.make_imm(cpu, res_op.size - 1)

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.SBFM.__wrapped__(cpu, res_op, reg_op, immr_op, imms_op)

    def _ASR_register(cpu, res_op, reg_op1, reg_op2):
        """
        ASR (register).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "0"
        insn_rx += "0"
        insn_rx += "11010110"
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "0010"
        insn_rx += "10"  # op2
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.ASRV.__wrapped__(cpu, res_op, reg_op1, reg_op2)

    @instruction
    def ASR(cpu, res_op, reg_op, reg_imm_op):
        """
        Combines ASR (register) and ASR (immediate).

        :param res_op: destination register.
        :param reg_op: source register.
        :param reg_imm_op: source register or immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert reg_imm_op.type in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]

        if reg_imm_op.type == cs.arm64.ARM64_OP_REG:
            cpu._ASR_register(res_op, reg_op, reg_imm_op)

        elif reg_imm_op.type == cs.arm64.ARM64_OP_IMM:
            cpu._ASR_immediate(res_op, reg_op, reg_imm_op)

        else:
            raise Aarch64InvalidInstruction

    @instruction
    def ASRV(cpu, res_op, reg_op1, reg_op2):
        """
        ASRV.

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "0"
        insn_rx += "0"
        insn_rx += "11010110"
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "0010"
        insn_rx += "10"  # op2
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op1.read()
        sft = reg_op2.read()

        result = ASR(reg, sft % res_op.size, res_op.size)
        res_op.write(result)

    @instruction
    def B_cond(cpu, imm_op):
        """
        B.cond.

        :param imm_op: immediate.
        """
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "0101010"
        insn_rx += "0"
        insn_rx += "[01]{19}"  # imm19
        insn_rx += "0"
        insn_rx += "[01]{4}"  # cond

        assert re.match(insn_rx, cpu.insn_bit_str)

        imm = imm_op.op.imm

        cpu.PC = Operators.ITEBV(
            cpu.regfile.size("PC"), cpu.cond_holds(cpu.instruction.cc), imm, cpu.PC
        )

    @instruction
    def B(cpu, imm_op):
        """
        B.

        :param imm_op: immediate.
        """
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "0"  # op
        insn_rx += "00101"
        insn_rx += "[01]{26}"  # imm26

        assert re.match(insn_rx, cpu.insn_bit_str)

        imm = imm_op.op.imm
        cpu.PC = imm

    @instruction
    def BFC(cpu, res_op, lsb_op, width_op):
        """
        BFC.

        :param res_op: destination register.
        :param lsb_op: immediate.
        :param width_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert lsb_op.type is cs.arm64.ARM64_OP_IMM
        assert width_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # sf
        insn_rx += "01"  # opc
        insn_rx += "100110"
        insn_rx += "[01]"  # N
        insn_rx += "[01]{6}"  # immr
        insn_rx += "[01]{6}"  # imms
        insn_rx += "1{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        lsb = lsb_op.op.imm
        lsb_op.value.imm = -lsb % res_op.size
        width_op.value.imm -= 1

        # Fake a register operand.
        if res_op.size == 32:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_WZR)
        elif res_op.size == 64:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_XZR)
        else:
            raise Aarch64InvalidInstruction

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.BFM.__wrapped__(cpu, res_op, zr, lsb_op, width_op)

    @instruction
    def BFI(cpu, res_op, reg_op, lsb_op, width_op):
        """
        BFI.

        :param res_op: destination register.
        :param reg_op: source register.
        :param lsb_op: immediate.
        :param width_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert lsb_op.type is cs.arm64.ARM64_OP_IMM
        assert width_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # sf
        insn_rx += "01"  # opc
        insn_rx += "100110"
        insn_rx += "[01]"  # N
        insn_rx += "[01]{6}"  # immr
        insn_rx += "[01]{6}"  # imms
        insn_rx += "(?!1{5})[01]{5}"  # Rn != 11111
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        lsb = lsb_op.op.imm
        lsb_op.value.imm = -lsb % res_op.size
        width_op.value.imm -= 1

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.BFM.__wrapped__(cpu, res_op, reg_op, lsb_op, width_op)

    @instruction
    def BFM(cpu, res_op, reg_op, immr_op, imms_op):
        """
        BFM.

        :param res_op: destination register.
        :param reg_op: source register.
        :param immr_op: immediate.
        :param imms_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert immr_op.type is cs.arm64.ARM64_OP_IMM
        assert imms_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # sf
        insn_rx += "01"  # opc
        insn_rx += "100110"
        insn_rx += "[01]"  # N
        insn_rx += "[01]{6}"  # immr
        insn_rx += "[01]{6}"  # imms
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        res = res_op.read()
        reg = reg_op.read()
        immr = immr_op.op.imm
        imms = imms_op.op.imm

        assert immr in range(res_op.size)
        assert imms in range(res_op.size)

        if imms >= immr:
            width = imms - immr + 1
            copy_from = immr
            copy_to = 0
        else:
            width = imms + 1
            copy_from = 0
            copy_to = res_op.size - immr

        result = ((reg & (Mask(width) << copy_from)) >> copy_from) << copy_to
        result |= res & ~(Mask(width) << copy_to)
        res_op.write(result)

    @instruction
    def BFXIL(cpu, res_op, reg_op, lsb_op, width_op):
        """
        BFXIL.

        :param res_op: destination register.
        :param reg_op: source register.
        :param lsb_op: immediate.
        :param width_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert lsb_op.type is cs.arm64.ARM64_OP_IMM
        assert width_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # sf
        insn_rx += "01"  # opc
        insn_rx += "100110"
        insn_rx += "[01]"  # N
        insn_rx += "[01]{6}"  # immr
        insn_rx += "[01]{6}"  # imms
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        lsb = lsb_op.op.imm
        width = width_op.op.imm
        width_op.value.imm = lsb + width - 1

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.BFM.__wrapped__(cpu, res_op, reg_op, lsb_op, width_op)

    # XXX: Support BIC (vector, immediate) and BIC (vector, register).
    @instruction
    def BIC(cpu, res_op, reg_op1, reg_op2):
        """
        BIC (shifted register).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "00"  # opc
        insn_rx += "01010"
        insn_rx += "[01]{2}"  # shift
        insn_rx += "1"  # N
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "[01]{6}"  # imm6
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        cpu._shifted_register(
            res_op=res_op,
            reg_op1=reg_op1,
            reg_op2=reg_op2,
            action=lambda x, y: (x & ~y, None),
            shifts=[
                cs.arm64.ARM64_SFT_LSL,
                cs.arm64.ARM64_SFT_LSR,
                cs.arm64.ARM64_SFT_ASR,
                cs.arm64.ARM64_SFT_ROR,
            ],
        )

    @instruction
    def BICS(cpu, res_op, reg_op1, reg_op2):
        """
        BICS (shifted register).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "11"  # opc
        insn_rx += "01010"
        insn_rx += "[01]{2}"  # shift
        insn_rx += "1"  # N
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "[01]{6}"  # imm6
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        def action(x, y):
            result = x & ~y
            n = Operators.EXTRACT(result, res_op.size - 1, 1)
            z = Operators.ITEBV(1, result == 0, 1, 0)
            return (result, (n, z, 0, 0))

        cpu._shifted_register(
            res_op=res_op,
            reg_op1=reg_op1,
            reg_op2=reg_op2,
            action=lambda x, y: action(x, y),
            flags=True,
            shifts=[
                cs.arm64.ARM64_SFT_LSL,
                cs.arm64.ARM64_SFT_LSR,
                cs.arm64.ARM64_SFT_ASR,
                cs.arm64.ARM64_SFT_ROR,
            ],
        )

    @instruction
    def BL(cpu, imm_op):
        """
        BL.

        :param imm_op: immediate.
        """
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "1"  # op
        insn_rx += "00101"
        insn_rx += "[01]{26}"  # imm26

        assert re.match(insn_rx, cpu.insn_bit_str)

        imm = imm_op.op.imm
        # The 'instruction' decorator makes PC point to the next instruction.
        cpu.X30 = cpu.PC
        cpu.PC = imm

    @instruction
    def BLR(cpu, reg_op):
        """
        BLR.

        :param reg_op: register.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx = "1101011"
        insn_rx += "0"  # Z
        insn_rx += "0"
        insn_rx += "01"  # op
        insn_rx += "1{5}"
        insn_rx += "0{4}"
        insn_rx += "0"  # A
        insn_rx += "0"  # M
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "0{5}"  # Rm

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        # The 'instruction' decorator makes PC point to the next instruction.
        cpu.X30 = cpu.PC
        cpu.PC = reg

    @instruction
    def BR(cpu, reg_op):
        """
        BR.

        :param reg_op: register.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx = "1101011"
        insn_rx += "0"  # Z
        insn_rx += "0"
        insn_rx += "00"  # op
        insn_rx += "1{5}"
        insn_rx += "0{4}"
        insn_rx += "0"  # A
        insn_rx += "0"  # M
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "0{5}"  # Rm

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        cpu.PC = reg

    @instruction
    def CBNZ(cpu, reg_op, imm_op):
        """
        CBNZ.

        :param reg_op: register.
        :param imm_op: immediate.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # sf
        insn_rx += "011010"
        insn_rx += "1"  # op
        insn_rx += "[01]{19}"  # imm19
        insn_rx += "[01]{5}"  # Rt

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        imm = imm_op.op.imm

        cpu.PC = Operators.ITEBV(cpu.regfile.size("PC"), reg != 0, imm, cpu.PC)

    @instruction
    def CBZ(cpu, reg_op, imm_op):
        """
        CBZ.

        :param reg_op: register.
        :param imm_op: immediate.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # sf
        insn_rx += "011010"
        insn_rx += "0"  # op
        insn_rx += "[01]{19}"  # imm19
        insn_rx += "[01]{5}"  # Rt

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        imm = imm_op.op.imm

        cpu.PC = Operators.ITEBV(cpu.regfile.size("PC"), reg == 0, imm, cpu.PC)

    def _CCMP_immediate(cpu, reg_op, imm_op, nzcv_op):
        """
        CCMP (immediate).

        :param reg_op: register.
        :param imm_op: immediate.
        :param nzcv_op: immediate.
        """
        cpu._ccmp_imm_reg(reg_op, imm_op, nzcv_op, imm=True)

    def _CCMP_register(cpu, reg_op1, reg_op2, nzcv_op):
        """
        CCMP (register).

        :param reg_op1: register.
        :param reg_op2: register.
        :param nzcv_op: immediate.
        """
        cpu._ccmp_imm_reg(reg_op1, reg_op2, nzcv_op, imm=False)

    @instruction
    def CCMP(cpu, reg_op, reg_imm_op, nzcv_op):
        """
        Combines CCMP (register) and CCMP (immediate).

        :param reg_op: register.
        :param reg_imm_op: register or immediate.
        :param nzcv_op: immediate.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert reg_imm_op.type in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]
        assert nzcv_op.type is cs.arm64.ARM64_OP_IMM

        if reg_imm_op.type == cs.arm64.ARM64_OP_REG:
            cpu._CCMP_register(reg_op, reg_imm_op, nzcv_op)

        elif reg_imm_op.type == cs.arm64.ARM64_OP_IMM:
            cpu._CCMP_immediate(reg_op, reg_imm_op, nzcv_op)

        else:
            raise Aarch64InvalidInstruction

    @instruction
    def CINC(cpu, res_op, reg_op):
        """
        CINC.

        :param res_op: destination register.
        :param reg_op: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "0"  # op
        insn_rx += "0"
        insn_rx += "11010100"
        insn_rx += "(?!1{5})[01]{5}"  # Rm != 11111
        insn_rx += "(?!111[01])[01]{4}"  # cond != 111x
        insn_rx += "0"
        insn_rx += "1"  # o2
        insn_rx += "(?!1{5})[01]{5}"  # Rn != 11111
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        cond = cpu.invert_cond(cpu.instruction.cc)

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.CSINC.__wrapped__(cpu, res_op, reg_op, reg_op, cond)

    @instruction
    def CINV(cpu, res_op, reg_op):
        """
        CINV.

        :param res_op: destination register.
        :param reg_op: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "1"  # op
        insn_rx += "0"
        insn_rx += "11010100"
        insn_rx += "(?!1{5})[01]{5}"  # Rm != 11111
        insn_rx += "(?!111[01])[01]{4}"  # cond != 111x
        insn_rx += "0"
        insn_rx += "0"  # o2
        insn_rx += "(?!1{5})[01]{5}"  # Rn != 11111
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        cond = cpu.invert_cond(cpu.instruction.cc)

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.CSINV.__wrapped__(cpu, res_op, reg_op, reg_op, cond)

    # XXX: Support CLZ (vector).
    @instruction
    def CLZ(cpu, res_op, reg_op):
        """
        CLZ.

        :param res_op: destination register.
        :param reg_op: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "1"
        insn_rx += "0"
        insn_rx += "11010110"
        insn_rx += "0{5}"
        insn_rx += "00010"
        insn_rx += "0"  # op
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # XXX: Copied from 'CLZ' in 'arm.py'.
        reg = reg_op.read()
        msb = res_op.size - 1
        result = res_op.size

        for pos in range(res_op.size):
            cond = Operators.EXTRACT(reg, pos, 1) == 1
            result = Operators.ITEBV(res_op.size, cond, msb - pos, result)

        res_op.write(result)

    def _CMEQ_register(cpu, res_op, reg_op1, reg_op2):
        """
        CMEQ (register).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        cpu._cmeq(res_op, reg_op1, reg_op2, register=True)

    def _CMEQ_zero(cpu, res_op, reg_op, imm_op):
        """
        CMEQ (zero).

        :param res_op: destination register.
        :param reg_op: source register.
        :param imm_op: immediate (zero).
        """
        cpu._cmeq(res_op, reg_op, imm_op, register=False)

    @instruction
    def CMEQ(cpu, res_op, reg_op, reg_imm_op):
        """
        Combines CMEQ (register) and CMEQ (zero).

        :param res_op: destination register.
        :param reg_op: source register.
        :param reg_imm_op: source register or immediate (zero).
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert reg_imm_op.type in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]

        if reg_imm_op.type == cs.arm64.ARM64_OP_REG:
            cpu._CMEQ_register(res_op, reg_op, reg_imm_op)

        else:
            cpu._CMEQ_zero(res_op, reg_op, reg_imm_op)

    def _CMN_extended_register(cpu, reg_op1, reg_op2):
        """
        CMN (extended register).

        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "0"  # op
        insn_rx += "1"  # S
        insn_rx += "01011"
        insn_rx += "00"
        insn_rx += "1"
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "[01]{3}"  # option
        insn_rx += "[01]{3}"  # imm3
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "1{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # Fake a register operand.
        if reg_op1.size == 32:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_WZR)
        elif reg_op1.size == 64:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_XZR)
        else:
            raise Aarch64InvalidInstruction

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.ADDS.__wrapped__(cpu, zr, reg_op1, reg_op2)

    def _CMN_immediate(cpu, reg_op, imm_op):
        """
        CMN (immediate).

        :param reg_op: source register.
        :param imm_op: immediate.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # sf
        insn_rx += "0"  # op
        insn_rx += "1"  # S
        insn_rx += "10001"
        insn_rx += "(?!1[01])[01]{2}"  # shift != 1x
        insn_rx += "[01]{12}"  # imm12
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "1{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # Fake a register operand.
        if reg_op.size == 32:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_WZR)
        elif reg_op.size == 64:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_XZR)
        else:
            raise Aarch64InvalidInstruction

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.ADDS.__wrapped__(cpu, zr, reg_op, imm_op)

    def _CMN_shifted_register(cpu, reg_op1, reg_op2):
        """
        CMN (shifted register).

        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "0"  # op
        insn_rx += "1"  # S
        insn_rx += "01011"
        insn_rx += "[01]{2}"  # shift
        insn_rx += "0"
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "[01]{6}"  # imm6
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "1{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # Fake a register operand.
        if reg_op1.size == 32:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_WZR)
        elif reg_op1.size == 64:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_XZR)
        else:
            raise Aarch64InvalidInstruction

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.ADDS.__wrapped__(cpu, zr, reg_op1, reg_op2)

    @instruction
    def CMN(cpu, reg_op, reg_imm_op):
        """
        Combines CMN (extended register), CMN (immediate), and CMN (shifted
        register).

        :param reg_op: source register.
        :param reg_imm_op: source register or immediate.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert reg_imm_op.type in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]

        bit21 = cpu.insn_bit_str[-22]

        if reg_imm_op.type == cs.arm64.ARM64_OP_IMM:
            cpu._CMN_immediate(reg_op, reg_imm_op)

        elif reg_imm_op.type == cs.arm64.ARM64_OP_REG and bit21 == "0":
            cpu._CMN_shifted_register(reg_op, reg_imm_op)

        elif reg_imm_op.type == cs.arm64.ARM64_OP_REG and bit21 == "1":
            cpu._CMN_extended_register(reg_op, reg_imm_op)

        else:
            raise Aarch64InvalidInstruction

    def _CMP_extended_register(cpu, reg_op1, reg_op2):
        """
        CMP (extended register).

        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "1"  # op
        insn_rx += "1"  # S
        insn_rx += "01011"
        insn_rx += "00"
        insn_rx += "1"
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "[01]{3}"  # option
        insn_rx += "[01]{3}"  # imm3
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "1{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # Fake a register operand.
        if reg_op1.size == 32:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_WZR)
        elif reg_op1.size == 64:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_XZR)
        else:
            raise Aarch64InvalidInstruction

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.SUBS.__wrapped__(cpu, zr, reg_op1, reg_op2)

    def _CMP_immediate(cpu, reg_op, imm_op):
        """
        CMP (immediate).

        :param reg_op: source register.
        :param imm_op: immediate.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # sf
        insn_rx += "1"  # op
        insn_rx += "1"  # S
        insn_rx += "10001"
        insn_rx += "(?!1[01])[01]{2}"  # shift != 1x
        insn_rx += "[01]{12}"  # imm12
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "1{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # Fake a register operand.
        if reg_op.size == 32:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_WZR)
        elif reg_op.size == 64:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_XZR)
        else:
            raise Aarch64InvalidInstruction

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.SUBS.__wrapped__(cpu, zr, reg_op, imm_op)

    def _CMP_shifted_register(cpu, reg_op1, reg_op2):
        """
        CMP (shifted register).

        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "1"  # op
        insn_rx += "1"  # S
        insn_rx += "01011"
        insn_rx += "[01]{2}"  # shift
        insn_rx += "0"
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "[01]{6}"  # imm6
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "1{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # Fake a register operand.
        if reg_op1.size == 32:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_WZR)
        elif reg_op1.size == 64:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_XZR)
        else:
            raise Aarch64InvalidInstruction

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.SUBS.__wrapped__(cpu, zr, reg_op1, reg_op2)

    @instruction
    def CMP(cpu, reg_op, reg_imm_op):
        """
        Combines CMP (extended register), CMP (immediate), and CMP (shifted
        register).

        :param reg_op: source register.
        :param reg_imm_op: source register or immediate.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert reg_imm_op.type in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]

        bit21 = cpu.insn_bit_str[-22]

        if reg_imm_op.type == cs.arm64.ARM64_OP_IMM:
            cpu._CMP_immediate(reg_op, reg_imm_op)

        elif reg_imm_op.type == cs.arm64.ARM64_OP_REG and bit21 == "0":
            cpu._CMP_shifted_register(reg_op, reg_imm_op)

        elif reg_imm_op.type == cs.arm64.ARM64_OP_REG and bit21 == "1":
            cpu._CMP_extended_register(reg_op, reg_imm_op)

        else:
            raise Aarch64InvalidInstruction

    @instruction
    def CSEL(cpu, res_op, reg_op1, reg_op2):
        """
        CSEL.

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "0"  # op
        insn_rx += "0"
        insn_rx += "11010100"
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "[01]{4}"  # cond
        insn_rx += "0"
        insn_rx += "0"  # o2
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg1 = reg_op1.read()
        reg2 = reg_op2.read()

        result = Operators.ITEBV(res_op.size, cpu.cond_holds(cpu.instruction.cc), reg1, reg2)

        res_op.write(result)

    @instruction
    def CSET(cpu, res_op):
        """
        CSET.

        :param res_op: destination register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "0"  # op
        insn_rx += "0"
        insn_rx += "11010100"
        insn_rx += "1{5}"  # Rm
        insn_rx += "(?!111[01])[01]{4}"  # cond != 111x
        insn_rx += "0"
        insn_rx += "1"  # o2
        insn_rx += "1{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        cond = cpu.invert_cond(cpu.instruction.cc)

        # Fake a register operand.
        if res_op.size == 32:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_WZR)
        elif res_op.size == 64:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_XZR)
        else:
            raise Aarch64InvalidInstruction

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.CSINC.__wrapped__(cpu, res_op, zr, zr, cond)

    @instruction
    def CSETM(cpu, res_op):
        """
        CSETM.

        :param res_op: destination register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "1"  # op
        insn_rx += "0"
        insn_rx += "11010100"
        insn_rx += "1{5}"  # Rm
        insn_rx += "(?!111[01])[01]{4}"  # cond != 111x
        insn_rx += "0"
        insn_rx += "0"  # o2
        insn_rx += "1{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        cond = cpu.invert_cond(cpu.instruction.cc)

        # Fake a register operand.
        if res_op.size == 32:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_WZR)
        elif res_op.size == 64:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_XZR)
        else:
            raise Aarch64InvalidInstruction

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.CSINV.__wrapped__(cpu, res_op, zr, zr, cond)

    @instruction
    def CSINC(cpu, res_op, reg_op1, reg_op2, cond=None):
        """
        CSINC.

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "0"  # op
        insn_rx += "0"
        insn_rx += "11010100"
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "[01]{4}"  # cond
        insn_rx += "0"
        insn_rx += "1"  # o2
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg1 = reg_op1.read()
        reg2 = reg_op2.read()
        cond = cond if cond else cpu.instruction.cc

        result = Operators.ITEBV(res_op.size, cpu.cond_holds(cond), reg1, reg2 + 1)

        res_op.write(UInt(result, res_op.size))

    @instruction
    def CSINV(cpu, res_op, reg_op1, reg_op2, cond=None):
        """
        CSINV.

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "1"  # op
        insn_rx += "0"
        insn_rx += "11010100"
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "[01]{4}"  # cond
        insn_rx += "0"
        insn_rx += "0"  # o2
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg1 = reg_op1.read()
        reg2 = reg_op2.read()
        cond = cond if cond else cpu.instruction.cc

        result = Operators.ITEBV(res_op.size, cpu.cond_holds(cond), reg1, ~reg2)

        res_op.write(UInt(result, res_op.size))

    @instruction
    def DMB(cpu, bar_imm_op):
        """
        DMB.

        :param bar_imm_op: barrier or immediate.
        """
        assert bar_imm_op.type in [cs.arm64.ARM64_OP_BARRIER, cs.arm64.ARM64_OP_IMM]

        insn_rx = "1101010100"
        insn_rx += "0"
        insn_rx += "00"
        insn_rx += "011"
        insn_rx += "0011"
        insn_rx += "[01]{4}"  # CRm
        insn_rx += "1"
        insn_rx += "01"  # opc
        insn_rx += "1{5}"

        assert re.match(insn_rx, cpu.insn_bit_str)
        # XXX: Assumes sequential execution.

    # XXX: Support DUP (element).
    @instruction
    def DUP(cpu, res_op, reg_op):
        """
        DUP (general).

        :param res_op: destination register.
        :param reg_op: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx = "0"
        insn_rx += "[01]"  # Q
        insn_rx += "0"
        insn_rx += "01110000"
        insn_rx += "[01]{5}"  # imm5
        insn_rx += "0"
        insn_rx += "0001"
        insn_rx += "1"
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # XXX: Check if trapped.

        reg = reg_op.read()
        vas = res_op.op.vas

        if vas == cs.arm64.ARM64_VAS_8B:
            elem_size = 8
            elem_count = 8

        elif vas == cs.arm64.ARM64_VAS_16B:
            elem_size = 8
            elem_count = 16

        elif vas == cs.arm64.ARM64_VAS_4H:
            elem_size = 16
            elem_count = 4

        elif vas == cs.arm64.ARM64_VAS_8H:
            elem_size = 16
            elem_count = 8

        elif vas == cs.arm64.ARM64_VAS_2S:
            elem_size = 32
            elem_count = 2

        elif vas == cs.arm64.ARM64_VAS_4S:
            elem_size = 32
            elem_count = 4

        elif vas == cs.arm64.ARM64_VAS_2D:
            elem_size = 64
            elem_count = 2

        else:
            raise Aarch64InvalidInstruction

        reg = Operators.EXTRACT(reg, 0, elem_size)
        reg = Operators.ZEXTEND(reg, res_op.size)
        result = 0
        for i in range(elem_count):
            result |= reg << (i * elem_size)

        result = UInt(result, res_op.size)
        res_op.write(result)

    # XXX: Support EOR (immediate) and EOR (vector).
    @instruction
    def EOR(cpu, res_op, reg_op1, reg_op2):
        """
        EOR (shifted register).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "10"  # opc
        insn_rx += "01010"
        insn_rx += "[01]{2}"  # shift
        insn_rx += "0"  # N
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "[01]{6}"  # imm6
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        cpu._shifted_register(
            res_op=res_op,
            reg_op1=reg_op1,
            reg_op2=reg_op2,
            action=lambda x, y: (x ^ y, None),
            shifts=[
                cs.arm64.ARM64_SFT_LSL,
                cs.arm64.ARM64_SFT_LSR,
                cs.arm64.ARM64_SFT_ASR,
                cs.arm64.ARM64_SFT_ROR,
            ],
        )

    # XXX: Support LD1 (single structure).
    @instruction
    def LD1(cpu, op1, op2, op3=None, op4=None, op5=None, op6=None):
        """
        LD1 (multiple structures).

        :param op1: register.
        :param op2: memory or register.
        :param op3: None, memory, register, or immediate.
        :param op4: None, memory, register, or immediate.
        :param op5: None, memory, register, or immediate.
        :param op6: None, register, or immediate.
        """
        assert op1.type is cs.arm64.ARM64_OP_REG
        assert op2.type in [cs.arm64.ARM64_OP_MEM, cs.arm64.ARM64_OP_REG]
        assert not op3 or op3.type in [
            cs.arm64.ARM64_OP_MEM,
            cs.arm64.ARM64_OP_REG,
            cs.arm64.ARM64_OP_IMM,
        ]
        assert not op4 or op4.type in [
            cs.arm64.ARM64_OP_MEM,
            cs.arm64.ARM64_OP_REG,
            cs.arm64.ARM64_OP_IMM,
        ]
        assert not op5 or op5.type in [
            cs.arm64.ARM64_OP_MEM,
            cs.arm64.ARM64_OP_REG,
            cs.arm64.ARM64_OP_IMM,
        ]
        assert not op6 or op6.type in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]

        no_offset_rx = "0"
        no_offset_rx += "[01]"  # Q
        no_offset_rx += "0011000"
        no_offset_rx += "1"  # L
        no_offset_rx += "000000"
        no_offset_rx += "[01]{2}1[01]"  # opcode
        no_offset_rx += "[01]{2}"  # size
        no_offset_rx += "[01]{5}"  # Rn
        no_offset_rx += "[01]{5}"  # Rt

        post_index_rx = "0"
        post_index_rx += "[01]"  # Q
        post_index_rx += "0011001"
        post_index_rx += "1"  # L
        post_index_rx += "0"
        post_index_rx += "[01]{5}"  # Rm
        post_index_rx += "[01]{2}1[01]"  # opcode
        post_index_rx += "[01]{2}"  # size
        post_index_rx += "[01]{5}"  # Rn
        post_index_rx += "[01]{5}"  # Rt

        assert re.match(no_offset_rx, cpu.insn_bit_str) or re.match(post_index_rx, cpu.insn_bit_str)

        # XXX: Check if trapped.

        # Four registers.
        if (
            op1.type == cs.arm64.ARM64_OP_REG
            and op2.type == cs.arm64.ARM64_OP_REG
            and op3.type == cs.arm64.ARM64_OP_REG
            and op4.type == cs.arm64.ARM64_OP_REG
        ):
            res_ops = [op1, op2, op3, op4]
            mem_op = op5
            wback_op = op6

        # Three registers.
        elif (
            op1.type == cs.arm64.ARM64_OP_REG
            and op2.type == cs.arm64.ARM64_OP_REG
            and op3.type == cs.arm64.ARM64_OP_REG
        ):
            res_ops = [op1, op2, op3]
            mem_op = op4
            wback_op = op5

        # Two registers.
        elif op1.type == cs.arm64.ARM64_OP_REG and op2.type == cs.arm64.ARM64_OP_REG:
            res_ops = [op1, op2]
            mem_op = op3
            wback_op = op4

        # One register.
        else:
            res_ops = [op1]
            mem_op = op2
            wback_op = op3

        i = 0
        for res_op in res_ops:
            base = cpu.regfile.read(mem_op.mem.base)
            vas = res_op.op.vas

            if vas == cs.arm64.ARM64_VAS_8B:
                elem_size = 8
                elem_count = 8

            elif vas == cs.arm64.ARM64_VAS_16B:
                elem_size = 8
                elem_count = 16

            elif vas == cs.arm64.ARM64_VAS_4H:
                elem_size = 16
                elem_count = 4

            elif vas == cs.arm64.ARM64_VAS_8H:
                elem_size = 16
                elem_count = 8

            elif vas == cs.arm64.ARM64_VAS_2S:
                elem_size = 32
                elem_count = 2

            elif vas == cs.arm64.ARM64_VAS_4S:
                elem_size = 32
                elem_count = 4

            elif vas == cs.arm64.ARM64_VAS_1D:
                elem_size = 64
                elem_count = 1

            elif vas == cs.arm64.ARM64_VAS_2D:
                elem_size = 64
                elem_count = 2

            else:
                raise Aarch64InvalidInstruction

            size = elem_size * elem_count
            assert size <= res_op.size
            result = cpu.read_int(base + i * (size // 8), size)
            res_op.write(result)

            i += 1

        if cpu.instruction.writeback:
            wback = wback_op.read()
            wback = UInt(base + wback, cpu.address_bit_size)
            cpu.regfile.write(mem_op.mem.base, wback)

    @instruction
    def LDAXR(cpu, reg_op, mem_op):
        """
        LDAXR.

        :param reg_op: destination register.
        :param mem_op: memory.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert mem_op.type is cs.arm64.ARM64_OP_MEM

        insn_rx = "1[01]"  # size
        insn_rx += "001000"
        insn_rx += "0"
        insn_rx += "1"  # L
        insn_rx += "0"
        insn_rx += "1{5}"  # Rs
        insn_rx += "1"  # o0
        insn_rx += "1{5}"  # Rt2
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rt

        assert re.match(insn_rx, cpu.insn_bit_str)

        # XXX: Support exclusive access.

        base = cpu.regfile.read(mem_op.mem.base)
        imm = mem_op.mem.disp
        assert imm == 0

        result = cpu.read_int(base, reg_op.size)
        reg_op.write(result)

    # XXX: Support LDP (SIMD&FP).
    @instruction
    def LDP(cpu, reg_op1, reg_op2, mem_op, mimm_op=None):
        """
        LDP.

        :param reg_op1: destination register.
        :param reg_op2: destination register.
        :param mem_op: memory.
        :param mimm_op: None or immediate.
        """
        cpu._ldp_stp(reg_op1, reg_op2, mem_op, mimm_op, ldp=True)

    def _LDR_immediate(cpu, reg_op, mem_op, mimm_op):
        """
        LDR (immediate).

        :param reg_op: destination register.
        :param mem_op: memory.
        :param mimm_op: None or immediate.
        """
        cpu._ldr_str_immediate(reg_op, mem_op, mimm_op, ldr=True)

    def _LDR_literal(cpu, reg_op, imm_op):
        """
        LDR (literal).

        :param reg_op: destination register.
        :param imm_op: immediate.
        """
        cpu._ldr_literal(reg_op, imm_op)

    def _LDR_register(cpu, reg_op, mem_op):
        """
        LDR (register).

        :param reg_op: destination register.
        :param mem_op: memory.
        """
        cpu._ldr_str_register(reg_op, mem_op, ldr=True)

    # XXX: Support LDR (immediate, SIMD&FP), LDR (literal, SIMD&FP), and LDR
    # (register, SIMD&FP).
    @instruction
    def LDR(cpu, res_op, mem_imm_op, mimm_op=None):
        """
        Combines LDR (immediate), LDR (literal), and LDR (register).

        :param res_op: destination register.
        :param mem_imm_op: memory or immediate.
        :param mimm_op: None or immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert mem_imm_op.type in [cs.arm64.ARM64_OP_MEM, cs.arm64.ARM64_OP_IMM]
        assert not mimm_op or mimm_op.type is cs.arm64.ARM64_OP_IMM

        if mem_imm_op.type == cs.arm64.ARM64_OP_MEM:
            if mem_imm_op.mem.index:
                cpu._LDR_register(res_op, mem_imm_op)
            else:
                cpu._LDR_immediate(res_op, mem_imm_op, mimm_op)

        elif mem_imm_op.type == cs.arm64.ARM64_OP_IMM:
            cpu._LDR_literal(res_op, mem_imm_op)

        else:
            raise Aarch64InvalidInstruction

    def _LDRB_immediate(cpu, reg_op, mem_op, mimm_op):
        """
        LDRB (immediate).

        :param reg_op: destination register.
        :param mem_op: memory.
        :param mimm_op: None or immediate.
        """
        cpu._ldr_str_immediate(reg_op, mem_op, mimm_op, ldr=True, size=8)

    def _LDRB_register(cpu, reg_op, mem_op):
        """
        LDRB (register).

        :param reg_op: destination register.
        :param mem_op: memory.
        """
        cpu._ldr_str_register(reg_op, mem_op, ldr=True, size=8)

    @instruction
    def LDRB(cpu, reg_op, mem_op, mimm_op=None):
        """
        Combines LDRB (immediate) and LDRB (register).

        :param reg_op: destination register.
        :param mem_op: memory.
        :param mimm_op: None or immediate.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert mem_op.type is cs.arm64.ARM64_OP_MEM
        assert not mimm_op or mimm_op.type is cs.arm64.ARM64_OP_IMM

        if mem_op.mem.index:
            cpu._LDRB_register(reg_op, mem_op)
        else:
            cpu._LDRB_immediate(reg_op, mem_op, mimm_op)

    def _LDRH_immediate(cpu, reg_op, mem_op, mimm_op):
        """
        LDRH (immediate).

        :param reg_op: destination register.
        :param mem_op: memory.
        :param mimm_op: None or immediate.
        """
        cpu._ldr_str_immediate(reg_op, mem_op, mimm_op, ldr=True, size=16)

    def _LDRH_register(cpu, reg_op, mem_op):
        """
        LDRH (register).

        :param reg_op: destination register.
        :param mem_op: memory.
        """
        cpu._ldr_str_register(reg_op, mem_op, ldr=True, size=16)

    @instruction
    def LDRH(cpu, reg_op, mem_op, mimm_op=None):
        """
        Combines LDRH (immediate) and LDRH (register).

        :param reg_op: destination register.
        :param mem_op: memory.
        :param mimm_op: None or immediate.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert mem_op.type is cs.arm64.ARM64_OP_MEM
        assert not mimm_op or mimm_op.type is cs.arm64.ARM64_OP_IMM

        if mem_op.mem.index:
            cpu._LDRH_register(reg_op, mem_op)
        else:
            cpu._LDRH_immediate(reg_op, mem_op, mimm_op)

    def _LDRSW_immediate(cpu, reg_op, mem_op, mimm_op):
        """
        LDRSW (immediate).

        :param reg_op: destination register.
        :param mem_op: memory.
        :param mimm_op: None or immediate.
        """
        cpu._ldr_str_immediate(reg_op, mem_op, mimm_op, ldr=True, size=32, sextend=True)

    def _LDRSW_literal(cpu, reg_op, imm_op):
        """
        LDRSW (literal).

        :param reg_op: destination register.
        :param imm_op: immediate.
        """
        cpu._ldr_literal(reg_op, imm_op, size=32, sextend=True)

    def _LDRSW_register(cpu, reg_op, mem_op):
        """
        LDRSW (register).

        :param reg_op: destination register.
        :param mem_op: memory.
        """
        cpu._ldr_str_register(reg_op, mem_op, ldr=True, size=32, sextend=True)

    @instruction
    def LDRSW(cpu, res_op, mem_imm_op, mimm_op=None):
        """
        Combines LDRSW (immediate), LDRSW (literal), and LDRSW (register).

        :param res_op: destination register.
        :param mem_imm_op: memory or immediate.
        :param mimm_op: None or immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert mem_imm_op.type in [cs.arm64.ARM64_OP_MEM, cs.arm64.ARM64_OP_IMM]
        assert not mimm_op or mimm_op.type is cs.arm64.ARM64_OP_IMM

        if mem_imm_op.type == cs.arm64.ARM64_OP_MEM:
            if mem_imm_op.mem.index:
                cpu._LDRSW_register(res_op, mem_imm_op)
            else:
                cpu._LDRSW_immediate(res_op, mem_imm_op, mimm_op)

        elif mem_imm_op.type == cs.arm64.ARM64_OP_IMM:
            cpu._LDRSW_literal(res_op, mem_imm_op)

        else:
            raise Aarch64InvalidInstruction

    # XXX: Support LDUR (SIMD&FP).
    @instruction
    def LDUR(cpu, reg_op, mem_op):
        """
        LDUR.

        :param reg_op: destination register.
        :param mem_op: memory.
        """
        cpu._ldur_stur(reg_op, mem_op, ldur=True)

    @instruction
    def LDXR(cpu, reg_op, mem_op):
        """
        LDXR.

        :param reg_op: destination register.
        :param mem_op: memory.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert mem_op.type is cs.arm64.ARM64_OP_MEM

        insn_rx = "1[01]"  # size
        insn_rx += "001000"
        insn_rx += "0"
        insn_rx += "1"  # L
        insn_rx += "0"
        insn_rx += "1{5}"  # Rs
        insn_rx += "0"  # o0
        insn_rx += "1{5}"  # Rt2
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rt

        assert re.match(insn_rx, cpu.insn_bit_str)

        # XXX: Support exclusive access.

        base = cpu.regfile.read(mem_op.mem.base)
        imm = mem_op.mem.disp
        assert imm == 0

        result = cpu.read_int(base, reg_op.size)
        reg_op.write(result)

    def _LSL_immediate(cpu, res_op, reg_op, imm_op):
        """
        LSL (immediate).

        :param res_op: destination register.
        :param reg_op: source register.
        :param imm_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # sf
        insn_rx += "10"  # opc
        insn_rx += "100110"
        insn_rx += "[01]"  # N
        insn_rx += "[01]{6}"  # immr
        insn_rx += "[01]{6}"  # imms
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        imm = imm_op.op.imm

        # Fake immediate operands.
        immr_op = Aarch64Operand.make_imm(cpu, -imm % res_op.size)
        imms_op = Aarch64Operand.make_imm(cpu, res_op.size - 1 - imm)

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.UBFM.__wrapped__(cpu, res_op, reg_op, immr_op, imms_op)

    def _LSL_register(cpu, res_op, reg_op1, reg_op2):
        """
        LSL (register).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "0"
        insn_rx += "0"
        insn_rx += "11010110"
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "0010"
        insn_rx += "00"  # op2
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.LSLV.__wrapped__(cpu, res_op, reg_op1, reg_op2)

    @instruction
    def LSL(cpu, res_op, reg_op, reg_imm_op):
        """
        Combines LSL (register) and LSL (immediate).

        :param res_op: destination register.
        :param reg_op: source register.
        :param reg_imm_op: source register or immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert reg_imm_op.type in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]

        if reg_imm_op.type == cs.arm64.ARM64_OP_REG:
            cpu._LSL_register(res_op, reg_op, reg_imm_op)

        elif reg_imm_op.type == cs.arm64.ARM64_OP_IMM:
            cpu._LSL_immediate(res_op, reg_op, reg_imm_op)

        else:
            raise Aarch64InvalidInstruction

    @instruction
    def LSLV(cpu, res_op, reg_op1, reg_op2):
        """
        LSLV.

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "0"
        insn_rx += "0"
        insn_rx += "11010110"
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "0010"
        insn_rx += "00"  # op2
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op1.read()
        sft = reg_op2.read()

        result = LSL(reg, sft % res_op.size, res_op.size)
        res_op.write(result)

    def _LSR_immediate(cpu, res_op, reg_op, immr_op):
        """
        LSR (immediate).

        :param res_op: destination register.
        :param reg_op: source register.
        :param immr_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert immr_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # sf
        insn_rx += "10"  # opc
        insn_rx += "100110"
        insn_rx += "[01]"  # N
        insn_rx += "[01]{6}"  # immr
        insn_rx += "[01]1{5}"  # imms
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # Fake an immediate operand.
        imms_op = Aarch64Operand.make_imm(cpu, res_op.size - 1)

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.UBFM.__wrapped__(cpu, res_op, reg_op, immr_op, imms_op)

    def _LSR_register(cpu, res_op, reg_op1, reg_op2):
        """
        LSR (register).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "0"
        insn_rx += "0"
        insn_rx += "11010110"
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "0010"
        insn_rx += "01"  # op2
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.LSRV.__wrapped__(cpu, res_op, reg_op1, reg_op2)

    @instruction
    def LSR(cpu, res_op, reg_op, reg_imm_op):
        """
        Combines LSR (register) and LSR (immediate).

        :param res_op: destination register.
        :param reg_op: source register.
        :param reg_imm_op: source register or immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert reg_imm_op.type in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]

        if reg_imm_op.type == cs.arm64.ARM64_OP_REG:
            cpu._LSR_register(res_op, reg_op, reg_imm_op)

        elif reg_imm_op.type == cs.arm64.ARM64_OP_IMM:
            cpu._LSR_immediate(res_op, reg_op, reg_imm_op)

        else:
            raise Aarch64InvalidInstruction

    @instruction
    def LSRV(cpu, res_op, reg_op1, reg_op2):
        """
        LSRV.

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "0"
        insn_rx += "0"
        insn_rx += "11010110"
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "0010"
        insn_rx += "01"  # op2
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op1.read()
        sft = reg_op2.read()

        result = LSR(reg, sft % res_op.size, res_op.size)
        res_op.write(result)

    @instruction
    def MADD(cpu, res_op, reg_op1, reg_op2, reg_op3):
        """
        MADD.

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        :param reg_op3: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG
        assert reg_op3.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "00"
        insn_rx += "11011"
        insn_rx += "000"
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "0"  # o0
        insn_rx += "[01]{5}"  # Ra
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg1 = reg_op1.read()
        reg2 = reg_op2.read()
        reg3 = reg_op3.read()

        result = reg3 + (reg1 * reg2)
        res_op.write(UInt(result, res_op.size))

    def _MOV_to_general(cpu, res_op, reg_op):
        """
        MOV (to general).

        :param res_op: destination register.
        :param reg_op: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx = "0"
        insn_rx += "[01]"  # Q
        insn_rx += "0"
        insn_rx += "01110000"
        insn_rx += "[01]{3}00"  # imm5
        insn_rx += "0"
        insn_rx += "01"
        insn_rx += "1"
        insn_rx += "1"
        insn_rx += "1"
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # XXX: Check if trapped.

        # XXX: Capstone doesn't set 'vess' for this alias:
        # https://github.com/aquynh/capstone/issues/1452
        if res_op.size == 32:
            reg_op.op.vess = cs.arm64.ARM64_VESS_S

        elif res_op.size == 64:
            reg_op.op.vess = cs.arm64.ARM64_VESS_D

        else:
            raise Aarch64InvalidInstruction

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.UMOV.__wrapped__(cpu, res_op, reg_op)

    # XXX: Support MOV (scalar), MOV (element), MOV (from general), and MOV
    # (vector).
    @instruction
    def MOV(cpu, res_op, reg_imm_op):
        """
        Combines MOV (to/from SP), MOV (inverted wide immediate), MOV (wide
        immediate), MOV (bitmask immediate), MOV (register), and MOV (to
        general).

        :param res_op: destination register.
        :param reg_imm_op: source register or immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_imm_op.type in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]

        # Fake a register operand.
        if res_op.size == 32:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_WZR)
        elif res_op.size == 64:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_XZR)
        else:
            raise Aarch64InvalidInstruction

        opc = cpu.insn_bit_str[1:3]  # 'op S' for MOV (to/from SP)
        bit26 = cpu.insn_bit_str[-27]

        if reg_imm_op.type is cs.arm64.ARM64_OP_REG:
            # MOV (to general).
            if bit26 == "1":
                cpu._MOV_to_general(res_op, reg_imm_op)

            # MOV (to/from SP).
            elif bit26 == "0" and opc == "00":
                # Fake an immediate operand.
                zero = Aarch64Operand.make_imm(cpu, 0)

                # The 'instruction' decorator advances PC, so call the original
                # method.
                cpu.ADD.__wrapped__(cpu, res_op, reg_imm_op, zero)

            # MOV (register).
            elif bit26 == "0" and opc == "01":
                # The 'instruction' decorator advances PC, so call the original
                # method.
                cpu.ORR.__wrapped__(cpu, res_op, zr, reg_imm_op)

            else:
                raise Aarch64InvalidInstruction

        elif reg_imm_op.type is cs.arm64.ARM64_OP_IMM:
            # MOV (inverted wide immediate).
            if opc == "00":
                # The 'instruction' decorator advances PC, so call the original
                # method.
                cpu.MOVN.__wrapped__(cpu, res_op, reg_imm_op)

            # MOV (wide immediate).
            elif opc == "10":
                # The 'instruction' decorator advances PC, so call the original
                # method.
                cpu.MOVZ.__wrapped__(cpu, res_op, reg_imm_op)

            # MOV (bitmask immediate).
            elif opc == "01":
                # The 'instruction' decorator advances PC, so call the original
                # method.
                cpu.ORR.__wrapped__(cpu, res_op, zr, reg_imm_op)

            else:
                raise Aarch64InvalidInstruction

        else:
            raise Aarch64InvalidInstruction

    @instruction
    def MOVK(cpu, res_op, imm_op):
        """
        MOVK.

        :param res_op: destination register.
        :param imm_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # sf
        insn_rx += "11"  # opc
        insn_rx += "100101"
        insn_rx += "[01]{2}"  # hw
        insn_rx += "[01]{16}"  # imm16
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        res = res_op.read()
        imm = imm_op.op.imm
        sft = imm_op.op.shift.value

        if imm_op.is_shifted():
            assert imm_op.op.shift.type == cs.arm64.ARM64_SFT_LSL

        assert imm >= 0 and imm <= 65535
        assert (res_op.size == 32 and sft in [0, 16]) or (
            res_op.size == 64 and sft in [0, 16, 32, 48]
        )

        imm = LSL(imm, sft, res_op.size)
        mask = LSL(65535, sft, res_op.size)
        result = (res & ~mask) | imm
        res_op.write(result)

    @instruction
    def MOVN(cpu, res_op, imm_op):
        """
        MOVN.

        :param res_op: destination register.
        :param imm_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # sf
        insn_rx += "00"  # opc
        insn_rx += "100101"
        insn_rx += "[01]{2}"  # hw
        insn_rx += "[01]{16}"  # imm16
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        imm = imm_op.op.imm
        sft = imm_op.op.shift.value

        if imm_op.is_shifted():
            assert imm_op.op.shift.type == cs.arm64.ARM64_SFT_LSL

        assert imm >= 0 and imm <= 65535
        assert (res_op.size == 32 and sft in [0, 16]) or (
            res_op.size == 64 and sft in [0, 16, 32, 48]
        )

        result = UInt(~LSL(imm, sft, res_op.size), res_op.size)
        res_op.write(result)

    @instruction
    def MOVZ(cpu, res_op, imm_op):
        """
        MOVZ.

        :param res_op: destination register.
        :param imm_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # sf
        insn_rx += "10"  # opc
        insn_rx += "100101"
        insn_rx += "[01]{2}"  # hw
        insn_rx += "[01]{16}"  # imm16
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        imm = imm_op.op.imm
        sft = imm_op.op.shift.value

        if imm_op.is_shifted():
            assert imm_op.op.shift.type == cs.arm64.ARM64_SFT_LSL

        assert imm >= 0 and imm <= 65535
        assert (res_op.size == 32 and sft in [0, 16]) or (
            res_op.size == 64 and sft in [0, 16, 32, 48]
        )

        result = UInt(LSL(imm, sft, res_op.size), res_op.size)
        res_op.write(result)

    @instruction
    def MRS(cpu, res_op, reg_op):
        """
        MRS.

        :param res_op: destination register.
        :param reg_op: source system register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG_MRS

        insn_rx = "1101010100"
        insn_rx += "1"  # L
        insn_rx += "1"
        insn_rx += "[01]"  # o0
        insn_rx += "[01]{3}"  # op1
        insn_rx += "[01]{4}"  # CRn
        insn_rx += "[01]{4}"  # CRm
        insn_rx += "[01]{3}"  # op2
        insn_rx += "[01]{5}"  # Rt

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        res_op.write(reg)

    # XXX: Support MSR (immediate).
    @instruction
    def MSR(cpu, res_op, reg_op):
        """
        MSR (register).

        :param res_op: destination system register.
        :param reg_op: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG_MSR
        assert reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx = "1101010100"
        insn_rx += "0"  # L
        insn_rx += "1"
        insn_rx += "[01]"  # o0
        insn_rx += "[01]{3}"  # op1
        insn_rx += "[01]{4}"  # CRn
        insn_rx += "[01]{4}"  # CRm
        insn_rx += "[01]{3}"  # op2
        insn_rx += "[01]{5}"  # Rt

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        res_op.write(reg)

    @instruction
    def MSUB(cpu, res_op, reg_op1, reg_op2, reg_op3):
        """
        MSUB.

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        :param reg_op3: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG
        assert reg_op3.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "00"
        insn_rx += "11011"
        insn_rx += "000"
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "1"  # o0
        insn_rx += "[01]{5}"  # Ra
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg1 = reg_op1.read()
        reg2 = reg_op2.read()
        reg3 = reg_op3.read()

        result = reg3 - (reg1 * reg2)
        res_op.write(UInt(result, res_op.size))

    # XXX: Support MUL (by element) and MUL (vector).
    @instruction
    def MUL(cpu, res_op, reg_op1, reg_op2):
        """
        MUL.

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "00"
        insn_rx += "11011"
        insn_rx += "000"
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "0"  # o0
        insn_rx += "1{5}"  # Ra
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # Fake a register operand.
        if res_op.size == 32:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_WZR)
        elif res_op.size == 64:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_XZR)
        else:
            raise Aarch64InvalidInstruction

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.MADD.__wrapped__(cpu, res_op, reg_op1, reg_op2, zr)

    # XXX: Support NEG (vector).
    @instruction
    def NEG(cpu, res_op, reg_op):
        """
        NEG (shifted register).

        :param res_op: destination register.
        :param reg_op: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "1"  # op
        insn_rx += "0"  # S
        insn_rx += "01011"
        insn_rx += "[01]{2}"  # shift
        insn_rx += "0"
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "[01]{6}"  # imm6
        insn_rx += "1{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # Fake a register operand.
        if res_op.size == 32:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_WZR)
        elif res_op.size == 64:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_XZR)
        else:
            raise Aarch64InvalidInstruction

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.SUB.__wrapped__(cpu, res_op, zr, reg_op)

    @instruction
    def NOP(cpu):
        """
        NOP.
        """
        insn_rx = "1101010100"
        insn_rx += "0"
        insn_rx += "00"
        insn_rx += "011"
        insn_rx += "0010"
        insn_rx += "0000"  # CRm
        insn_rx += "000"  # op2
        insn_rx += "11111"

        assert re.match(insn_rx, cpu.insn_bit_str)

    def _ORR_immediate(cpu, res_op, reg_op, imm_op):
        """
        ORR (immediate).

        :param res_op: destination register.
        :param reg_op: source register.
        :param imm_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # sf
        insn_rx += "01"  # opc
        insn_rx += "100100"
        insn_rx += "[01]"  # N
        insn_rx += "[01]{6}"  # immr
        insn_rx += "[01]{6}"  # imms
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        imm = imm_op.op.imm
        result = UInt(reg | imm, res_op.size)
        res_op.write(result)

    def _ORR_shifted_register(cpu, res_op, reg_op1, reg_op2):
        """
        ORR (shifted register).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "01"  # opc
        insn_rx += "01010"
        insn_rx += "[01]{2}"  # shift
        insn_rx += "0"  # N
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "[01]{6}"  # imm6
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        cpu._shifted_register(
            res_op=res_op,
            reg_op1=reg_op1,
            reg_op2=reg_op2,
            action=lambda x, y: (x | y, None),
            shifts=[
                cs.arm64.ARM64_SFT_LSL,
                cs.arm64.ARM64_SFT_LSR,
                cs.arm64.ARM64_SFT_ASR,
                cs.arm64.ARM64_SFT_ROR,
            ],
        )

    def _ORR_vector_register(cpu, res_op, reg_op1, reg_op2):
        """
        ORR (vector, register).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx = "0"
        insn_rx += "[01]"  # Q
        insn_rx += "0"
        insn_rx += "01110"
        insn_rx += "10"  # size
        insn_rx += "1"
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "00011"
        insn_rx += "1"
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # XXX: Check if trapped.

        reg1 = reg_op1.read()
        reg2 = reg_op2.read()
        vas = res_op.op.vas

        if vas == cs.arm64.ARM64_VAS_8B:
            elem_size = 8
            elem_count = 8

        elif vas == cs.arm64.ARM64_VAS_16B:
            elem_size = 8
            elem_count = 16

        else:
            raise Aarch64InvalidInstruction

        result = 0
        for i in range(elem_count):
            elem1 = Operators.EXTRACT(reg1, i * elem_size, elem_size)
            elem2 = Operators.EXTRACT(reg2, i * elem_size, elem_size)
            elem = UInt(elem1 | elem2, elem_size)
            elem = Operators.ZEXTEND(elem, res_op.size)
            result |= elem << (i * elem_size)

        result = UInt(result, res_op.size)
        res_op.write(result)

    # XXX: Support ORR (vector, immediate).
    @instruction
    def ORR(cpu, res_op, reg_op, reg_imm_op):
        """
        Combines ORR (immediate), ORR (shifted register), and ORR (vector,
        register).

        :param res_op: destination register.
        :param reg_op: source register.
        :param reg_imm_op: source register or immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert reg_imm_op.type in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]

        bit21 = cpu.insn_bit_str[-22]

        if reg_imm_op.type == cs.arm64.ARM64_OP_IMM:
            cpu._ORR_immediate(res_op, reg_op, reg_imm_op)

        elif reg_imm_op.type == cs.arm64.ARM64_OP_REG and bit21 == "0":
            cpu._ORR_shifted_register(res_op, reg_op, reg_imm_op)

        elif reg_imm_op.type == cs.arm64.ARM64_OP_REG and bit21 == "1":
            cpu._ORR_vector_register(res_op, reg_op, reg_imm_op)

        else:
            raise Aarch64InvalidInstruction

    # XXX: Support RBIT (vector).
    @instruction
    def RBIT(cpu, res_op, reg_op):
        """
        RBIT.

        :param res_op: destination register.
        :param reg_op: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "1"
        insn_rx += "0"
        insn_rx += "11010110"
        insn_rx += "0{5}"
        insn_rx += "0{4}"
        insn_rx += "0{2}"
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        size = reg_op.size

        result = 0
        for pos in range(size):
            bit = Operators.EXTRACT(reg, pos, 1)
            bit = Operators.ZEXTEND(bit, res_op.size)
            result <<= 1
            result |= bit

        res_op.write(result)

    @instruction
    def RET(cpu, reg_op=None):
        """
        RET.

        :param reg_op: None or register.
        """
        assert not reg_op or reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx = "1101011"
        insn_rx += "0"  # Z
        insn_rx += "0"
        insn_rx += "10"  # op
        insn_rx += "1{5}"
        insn_rx += "0{4}"
        insn_rx += "0"  # A
        insn_rx += "0"  # M
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "0{5}"  # Rm

        assert re.match(insn_rx, cpu.insn_bit_str)

        if reg_op:
            reg = reg_op.read()
        else:
            reg = cpu.X30
        cpu.PC = reg

    @instruction
    def REV(cpu, res_op, reg_op):
        """
        REV.

        :param res_op: destination register.
        :param reg_op: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "1"
        insn_rx += "0"
        insn_rx += "11010110"
        insn_rx += "0{5}"
        insn_rx += "0{4}"
        insn_rx += "1[01]"  # opc
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        size = reg_op.size

        result = 0
        step = 8
        for pos in range(0, size, step):
            byte = Operators.EXTRACT(reg, pos, step)
            byte = Operators.ZEXTEND(byte, res_op.size)
            result <<= step
            result |= byte

        res_op.write(result)

    @instruction
    def SBFIZ(cpu, res_op, reg_op, lsb_op, width_op):
        """
        SBFIZ.

        :param res_op: destination register.
        :param reg_op: source register.
        :param lsb_op: immediate.
        :param width_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert lsb_op.type is cs.arm64.ARM64_OP_IMM
        assert width_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # sf
        insn_rx += "00"  # opc
        insn_rx += "100110"
        insn_rx += "[01]"  # N
        insn_rx += "[01]{6}"  # immr
        insn_rx += "[01]{6}"  # imms
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        lsb = lsb_op.op.imm
        lsb_op.value.imm = -lsb % res_op.size
        width_op.value.imm -= 1

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.SBFM.__wrapped__(cpu, res_op, reg_op, lsb_op, width_op)

    @instruction
    def SBFM(cpu, res_op, reg_op, immr_op, imms_op):
        """
        SBFM.

        :param res_op: destination register.
        :param reg_op: source register.
        :param immr_op: immediate.
        :param imms_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert immr_op.type is cs.arm64.ARM64_OP_IMM
        assert imms_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # sf
        insn_rx += "00"  # opc
        insn_rx += "100110"
        insn_rx += "[01]"  # N
        insn_rx += "[01]{6}"  # immr
        insn_rx += "[01]{6}"  # imms
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        immr = immr_op.op.imm
        imms = imms_op.op.imm

        assert immr in range(res_op.size)
        assert imms in range(res_op.size)

        if imms >= immr:
            width = imms - immr + 1
            copy_from = immr
            copy_to = 0
        else:
            width = imms + 1
            copy_from = 0
            copy_to = res_op.size - immr

        result = ((reg & (Mask(width) << copy_from)) >> copy_from) << copy_to
        result = Operators.ZEXTEND(result, res_op.size)
        result = Operators.ITEBV(
            res_op.size,
            Operators.EXTRACT(result, width + copy_to - 1, 1) == 1,
            (Mask(res_op.size) & ~Mask(width + copy_to)) | result,
            result,
        )

        res_op.write(result)

    @instruction
    def SBFX(cpu, res_op, reg_op, lsb_op, width_op):
        """
        SBFX.

        :param res_op: destination register.
        :param reg_op: source register.
        :param lsb_op: immediate.
        :param width_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert lsb_op.type is cs.arm64.ARM64_OP_IMM
        assert width_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # sf
        insn_rx += "00"  # opc
        insn_rx += "100110"
        insn_rx += "[01]"  # N
        insn_rx += "[01]{6}"  # immr
        insn_rx += "[01]{6}"  # imms
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        lsb = lsb_op.op.imm
        width = width_op.op.imm
        width_op.value.imm = lsb + width - 1

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.SBFM.__wrapped__(cpu, res_op, reg_op, lsb_op, width_op)

    # XXX: Add tests.
    @instruction
    def STLXR(cpu, stat_op, reg_op, mem_op):
        """
        STLXR.

        :param stat_op: status register.
        :param reg_op: source register.
        :param mem_op: memory.
        """
        assert stat_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert mem_op.type is cs.arm64.ARM64_OP_MEM

        insn_rx = "1[01]"  # size
        insn_rx += "001000"
        insn_rx += "0"
        insn_rx += "0"  # L
        insn_rx += "0"
        insn_rx += "[01]{5}"  # Rs
        insn_rx += "1"  # o0
        insn_rx += "1{5}"  # Rt2
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rt

        assert re.match(insn_rx, cpu.insn_bit_str)

        # XXX: Support exclusive access and check alignment.

        base = cpu.regfile.read(mem_op.mem.base)
        imm = mem_op.mem.disp
        assert imm == 0
        reg = reg_op.read()

        cpu.write_int(base, reg, reg_op.size)
        stat_op.write(0)  # XXX: always succeeds

    @instruction
    def STP(cpu, reg_op1, reg_op2, mem_op, mimm_op=None):
        """
        STP.

        :param reg_op1: source register.
        :param reg_op2: source register.
        :param mem_op: memory.
        :param mimm_op: None or immediate.
        """
        cpu._ldp_stp(reg_op1, reg_op2, mem_op, mimm_op, ldp=False)

    def _STR_immediate(cpu, reg_op, mem_op, mimm_op):
        """
        STR (immediate).

        :param reg_op: source register.
        :param mem_op: memory.
        :param mimm_op: None or immediate.
        """
        cpu._ldr_str_immediate(reg_op, mem_op, mimm_op, ldr=False)

    def _STR_register(cpu, reg_op, mem_op):
        """
        STR (register).

        :param reg_op: source register.
        :param mem_op: memory.
        """
        cpu._ldr_str_register(reg_op, mem_op, ldr=False)

    # XXX: Support STR (immediate, SIMD&FP) and STR (register, SIMD&FP).
    @instruction
    def STR(cpu, reg_op, mem_op, mimm_op=None):
        """
        Combines STR (immediate) and STR (register).

        :param reg_op: source register.
        :param mem_op: memory.
        :param mimm_op: None or immediate.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert mem_op.type is cs.arm64.ARM64_OP_MEM
        assert not mimm_op or mimm_op.type is cs.arm64.ARM64_OP_IMM

        if mem_op.mem.index:
            cpu._STR_register(reg_op, mem_op)
        else:
            cpu._STR_immediate(reg_op, mem_op, mimm_op)

    def _STRB_immediate(cpu, reg_op, mem_op, mimm_op):
        """
        STRB (immediate).

        :param reg_op: source register.
        :param mem_op: memory.
        :param mimm_op: None or immediate.
        """
        cpu._ldr_str_immediate(reg_op, mem_op, mimm_op, ldr=False, size=8)

    def _STRB_register(cpu, reg_op, mem_op):
        """
        STRB (register).

        :param reg_op: source register.
        :param mem_op: memory.
        """
        cpu._ldr_str_register(reg_op, mem_op, ldr=False, size=8)

    @instruction
    def STRB(cpu, reg_op, mem_op, mimm_op=None):
        """
        Combines STRB (immediate) and STRB (register).

        :param reg_op: source register.
        :param mem_op: memory.
        :param mimm_op: None or immediate.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert mem_op.type is cs.arm64.ARM64_OP_MEM
        assert not mimm_op or mimm_op.type is cs.arm64.ARM64_OP_IMM

        if mem_op.mem.index:
            cpu._STRB_register(reg_op, mem_op)
        else:
            cpu._STRB_immediate(reg_op, mem_op, mimm_op)

    def _STRH_immediate(cpu, reg_op, mem_op, mimm_op):
        """
        STRH (immediate).

        :param reg_op: source register.
        :param mem_op: memory.
        :param mimm_op: None or immediate.
        """
        cpu._ldr_str_immediate(reg_op, mem_op, mimm_op, ldr=False, size=16)

    def _STRH_register(cpu, reg_op, mem_op):
        """
        STRH (register).

        :param reg_op: source register.
        :param mem_op: memory.
        """
        cpu._ldr_str_register(reg_op, mem_op, ldr=False, size=16)

    @instruction
    def STRH(cpu, reg_op, mem_op, mimm_op=None):
        """
        Combines STRH (immediate) and STRH (register).

        :param reg_op: source register.
        :param mem_op: memory.
        :param mimm_op: None or immediate.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert mem_op.type is cs.arm64.ARM64_OP_MEM
        assert not mimm_op or mimm_op.type is cs.arm64.ARM64_OP_IMM

        if mem_op.mem.index:
            cpu._STRH_register(reg_op, mem_op)
        else:
            cpu._STRH_immediate(reg_op, mem_op, mimm_op)

    # XXX: Support STUR (SIMD&FP).
    @instruction
    def STUR(cpu, reg_op, mem_op):
        """
        STUR.

        :param reg_op: source register.
        :param mem_op: memory.
        """
        cpu._ldur_stur(reg_op, mem_op, ldur=False)

    # XXX: Add tests.
    @instruction
    def STXR(cpu, stat_op, reg_op, mem_op):
        """
        STXR.

        :param stat_op: status register.
        :param reg_op: source register.
        :param mem_op: memory.
        """
        assert stat_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert mem_op.type is cs.arm64.ARM64_OP_MEM

        insn_rx = "1[01]"  # size
        insn_rx += "001000"
        insn_rx += "0"
        insn_rx += "0"  # L
        insn_rx += "0"
        insn_rx += "[01]{5}"  # Rs
        insn_rx += "0"  # o0
        insn_rx += "1{5}"  # Rt2
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rt

        assert re.match(insn_rx, cpu.insn_bit_str)

        # XXX: Support exclusive access and check alignment.

        base = cpu.regfile.read(mem_op.mem.base)
        imm = mem_op.mem.disp
        assert imm == 0
        reg = reg_op.read()

        cpu.write_int(base, reg, reg_op.size)
        stat_op.write(0)  # XXX: always succeeds

    def _SUB_extended_register(cpu, res_op, reg_op1, reg_op2):
        """
        SUB (extended register).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        cpu._adds_subs_extended_register(res_op, reg_op1, reg_op2, mnem="sub")

    def _SUB_immediate(cpu, res_op, reg_op, imm_op):
        """
        SUB (immediate).

        :param res_op: destination register.
        :param reg_op: source register.
        :param imm_op: immediate.
        """
        cpu._adds_subs_immediate(res_op, reg_op, imm_op, mnem="sub")

    def _SUB_shifted_register(cpu, res_op, reg_op1, reg_op2):
        """
        SUB (shifted register).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        cpu._adds_subs_shifted_register(res_op, reg_op1, reg_op2, mnem="sub")

    def _SUB_vector(cpu, res_op, reg_op1, reg_op2):
        """
        SUB (vector).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        cpu._add_sub_vector(res_op, reg_op1, reg_op2, add=False)

    @instruction
    def SUB(cpu, res_op, reg_op, reg_imm_op):
        """
        Combines SUB (extended register), SUB (immediate), SUB (shifted
        register), and SUB (vector).

        :param res_op: destination register.
        :param reg_op: source register.
        :param reg_imm_op: source register or immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert reg_imm_op.type in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]

        bit21 = cpu.insn_bit_str[-22]
        bit24 = cpu.insn_bit_str[-25]

        if reg_imm_op.type == cs.arm64.ARM64_OP_IMM:
            cpu._SUB_immediate(res_op, reg_op, reg_imm_op)

        elif reg_imm_op.type == cs.arm64.ARM64_OP_REG and bit24 == "0":
            cpu._SUB_vector(res_op, reg_op, reg_imm_op)

        elif reg_imm_op.type == cs.arm64.ARM64_OP_REG and bit24 == "1" and bit21 == "0":
            cpu._SUB_shifted_register(res_op, reg_op, reg_imm_op)

        elif reg_imm_op.type == cs.arm64.ARM64_OP_REG and bit24 == "1" and bit21 == "1":
            cpu._SUB_extended_register(res_op, reg_op, reg_imm_op)

        else:
            raise Aarch64InvalidInstruction

    def _SUBS_extended_register(cpu, res_op, reg_op1, reg_op2):
        """
        SUBS (extended register).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        cpu._adds_subs_extended_register(res_op, reg_op1, reg_op2, mnem="subs")

    def _SUBS_immediate(cpu, res_op, reg_op, imm_op):
        """
        SUBS (immediate).

        :param res_op: destination register.
        :param reg_op: source register.
        :param imm_op: immediate.
        """
        cpu._adds_subs_immediate(res_op, reg_op, imm_op, mnem="subs")

    def _SUBS_shifted_register(cpu, res_op, reg_op1, reg_op2):
        """
        SUBS (shifted register).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        cpu._adds_subs_shifted_register(res_op, reg_op1, reg_op2, mnem="subs")

    @instruction
    def SUBS(cpu, res_op, reg_op, reg_imm_op):
        """
        Combines SUBS (extended register), SUBS (immediate), and SUBS (shifted
        register).

        :param res_op: destination register.
        :param reg_op: source register.
        :param reg_imm_op: source register or immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert reg_imm_op.type in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]

        bit21 = cpu.insn_bit_str[-22]

        if reg_imm_op.type == cs.arm64.ARM64_OP_IMM:
            cpu._SUBS_immediate(res_op, reg_op, reg_imm_op)

        elif reg_imm_op.type == cs.arm64.ARM64_OP_REG and bit21 == "0":
            cpu._SUBS_shifted_register(res_op, reg_op, reg_imm_op)

        elif reg_imm_op.type == cs.arm64.ARM64_OP_REG and bit21 == "1":
            cpu._SUBS_extended_register(res_op, reg_op, reg_imm_op)

        else:
            raise Aarch64InvalidInstruction

    @instruction
    def SVC(cpu, imm_op):
        """
        SVC.

        :param imm_op: immediate.
        """
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        imm = imm_op.op.imm
        assert imm >= 0 and imm <= 65535

        if imm != 0:
            raise InstructionNotImplementedError(f"SVC #{imm}")
        raise Interruption(imm)

    @instruction
    def SXTB(cpu, res_op, reg_op):
        """
        SXTB.

        :param res_op: destination register.
        :param reg_op: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "00"  # opc
        insn_rx += "100110"
        insn_rx += "[01]"  # N
        insn_rx += "0{6}"  # immr
        insn_rx += "000111"  # imms
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # Fake immediate operands.
        immr_op = Aarch64Operand.make_imm(cpu, 0)
        imms_op = Aarch64Operand.make_imm(cpu, 7)

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.SBFM.__wrapped__(cpu, res_op, reg_op, immr_op, imms_op)

    @instruction
    def SXTH(cpu, res_op, reg_op):
        """
        SXTH.

        :param res_op: destination register.
        :param reg_op: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "00"  # opc
        insn_rx += "100110"
        insn_rx += "[01]"  # N
        insn_rx += "0{6}"  # immr
        insn_rx += "001111"  # imms
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # Fake immediate operands.
        immr_op = Aarch64Operand.make_imm(cpu, 0)
        imms_op = Aarch64Operand.make_imm(cpu, 15)

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.SBFM.__wrapped__(cpu, res_op, reg_op, immr_op, imms_op)

    @instruction
    def SXTW(cpu, res_op, reg_op):
        """
        SXTW.

        :param res_op: destination register.
        :param reg_op: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx = "1"  # sf
        insn_rx += "00"  # opc
        insn_rx += "100110"
        insn_rx += "1"  # N
        insn_rx += "000000"  # immr
        insn_rx += "011111"  # imms
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # Fake immediate operands.
        immr_op = Aarch64Operand.make_imm(cpu, 0)
        imms_op = Aarch64Operand.make_imm(cpu, 31)

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.SBFM.__wrapped__(cpu, res_op, reg_op, immr_op, imms_op)

    @instruction
    def TBNZ(cpu, reg_op, imm_op, lab_op):
        """
        TBNZ.

        :param reg_op: register.
        :param imm_op: immediate.
        :param lab_op: immediate.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM
        assert lab_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # b5
        insn_rx += "011011"
        insn_rx += "1"  # op
        insn_rx += "[01]{5}"  # b40
        insn_rx += "[01]{14}"  # imm14
        insn_rx += "[01]{5}"  # Rt

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        imm = imm_op.op.imm
        lab = lab_op.op.imm

        assert imm in range(reg_op.size)

        cpu.PC = Operators.ITEBV(
            cpu.regfile.size("PC"), Operators.EXTRACT(reg, imm, 1) != 0, lab, cpu.PC
        )

    @instruction
    def TBZ(cpu, reg_op, imm_op, lab_op):
        """
        TBZ.

        :param reg_op: register.
        :param imm_op: immediate.
        :param lab_op: immediate.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM
        assert lab_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # b5
        insn_rx += "011011"
        insn_rx += "0"  # op
        insn_rx += "[01]{5}"  # b40
        insn_rx += "[01]{14}"  # imm14
        insn_rx += "[01]{5}"  # Rt

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        imm = imm_op.op.imm
        lab = lab_op.op.imm

        assert imm in range(reg_op.size)

        cpu.PC = Operators.ITEBV(
            cpu.regfile.size("PC"), Operators.EXTRACT(reg, imm, 1) == 0, lab, cpu.PC
        )

    def _TST_immediate(cpu, reg_op, imm_op):
        """
        TST (immediate).

        :param reg_op: source register.
        :param imm_op: immediate.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # sf
        insn_rx += "11"  # opc
        insn_rx += "100100"
        insn_rx += "[01]"  # N
        insn_rx += "[01]{6}"  # immr
        insn_rx += "[01]{6}"  # imms
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "1{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # Fake a register operand.
        if reg_op.size == 32:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_WZR)
        elif reg_op.size == 64:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_XZR)
        else:
            raise Aarch64InvalidInstruction

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.ANDS.__wrapped__(cpu, zr, reg_op, imm_op)

    def _TST_shifted_register(cpu, reg_op1, reg_op2):
        """
        TST (shifted register).

        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "11"  # opc
        insn_rx += "01010"
        insn_rx += "[01]{2}"  # shift
        insn_rx += "0"  # N
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "[01]{6}"  # imm6
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "1{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # Fake a register operand.
        if reg_op1.size == 32:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_WZR)
        elif reg_op1.size == 64:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_XZR)
        else:
            raise Aarch64InvalidInstruction

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.ANDS.__wrapped__(cpu, zr, reg_op1, reg_op2)

    @instruction
    def TST(cpu, reg_op, reg_imm_op):
        """
        Combines TST (immediate) and TST (shifted register).

        :param reg_op: source register.
        :param reg_imm_op: source register or immediate.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert reg_imm_op.type in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]

        if reg_imm_op.type == cs.arm64.ARM64_OP_REG:
            cpu._TST_shifted_register(reg_op, reg_imm_op)

        elif reg_imm_op.type == cs.arm64.ARM64_OP_IMM:
            cpu._TST_immediate(reg_op, reg_imm_op)

        else:
            raise Aarch64InvalidInstruction

    @instruction
    def UBFIZ(cpu, res_op, reg_op, lsb_op, width_op):
        """
        UBFIZ.

        :param res_op: destination register.
        :param reg_op: source register.
        :param lsb_op: immediate.
        :param width_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert lsb_op.type is cs.arm64.ARM64_OP_IMM
        assert width_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # sf
        insn_rx += "10"  # opc
        insn_rx += "100110"
        insn_rx += "[01]"  # N
        insn_rx += "[01]{6}"  # immr
        insn_rx += "[01]{6}"  # imms
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        lsb = lsb_op.op.imm
        lsb_op.value.imm = -lsb % res_op.size
        width_op.value.imm -= 1

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.UBFM.__wrapped__(cpu, res_op, reg_op, lsb_op, width_op)

    @instruction
    def UBFM(cpu, res_op, reg_op, immr_op, imms_op):
        """
        UBFM.

        :param res_op: destination register.
        :param reg_op: source register.
        :param immr_op: immediate.
        :param imms_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert immr_op.type is cs.arm64.ARM64_OP_IMM
        assert imms_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # sf
        insn_rx += "10"  # opc
        insn_rx += "100110"
        insn_rx += "[01]"  # N
        insn_rx += "[01]{6}"  # immr
        insn_rx += "[01]{6}"  # imms
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        immr = immr_op.op.imm
        imms = imms_op.op.imm

        assert immr in range(res_op.size)
        assert imms in range(res_op.size)

        if imms >= immr:
            width = imms - immr + 1
            copy_from = immr
            copy_to = 0
        else:
            width = imms + 1
            copy_from = 0
            copy_to = res_op.size - immr

        mask = Mask(width)
        result = ((reg & (mask << copy_from)) >> copy_from) << copy_to
        res_op.write(result)

    @instruction
    def UBFX(cpu, res_op, reg_op, lsb_op, width_op):
        """
        UBFX.

        :param res_op: destination register.
        :param reg_op: source register.
        :param lsb_op: immediate.
        :param width_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert lsb_op.type is cs.arm64.ARM64_OP_IMM
        assert width_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx = "[01]"  # sf
        insn_rx += "10"  # opc
        insn_rx += "100110"
        insn_rx += "[01]"  # N
        insn_rx += "[01]{6}"  # immr
        insn_rx += "[01]{6}"  # imms
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        lsb = lsb_op.op.imm
        width = width_op.op.imm
        width_op.value.imm = lsb + width - 1

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.UBFM.__wrapped__(cpu, res_op, reg_op, lsb_op, width_op)

    @instruction
    def UDIV(cpu, res_op, reg_op1, reg_op2):
        """
        UDIV.

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx = "[01]"  # sf
        insn_rx += "0"
        insn_rx += "0"
        insn_rx += "11010110"
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "00001"
        insn_rx += "0"  # o1
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg1 = UInt(reg_op1.read(), reg_op1.size)
        reg2 = UInt(reg_op2.read(), reg_op2.size)

        # Compute regardless of the second argument, so it can be referenced in
        # 'ITEBV'.  But the result shouldn't be used if 'reg2 == 0'.
        try:
            quot = Operators.UDIV(reg1, reg2)  # rounds toward zero
        except ZeroDivisionError:
            quot = 0

        result = Operators.ITEBV(res_op.size, reg2 == 0, 0, quot)

        res_op.write(result)

    @instruction
    def UMOV(cpu, res_op, reg_op):
        """
        UMOV.

        :param res_op: destination register.
        :param reg_op: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx = "0"
        insn_rx += "[01]"  # Q
        insn_rx += "0"
        insn_rx += "01110000"
        insn_rx += "[01]{5}"  # imm5
        insn_rx += "0"
        insn_rx += "01"
        insn_rx += "1"
        insn_rx += "1"
        insn_rx += "1"
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # XXX: Check if trapped.

        reg = reg_op.read()
        index = reg_op.op.vector_index
        vess = reg_op.op.vess

        if vess == cs.arm64.ARM64_VESS_B:
            elem_size = 8

        elif vess == cs.arm64.ARM64_VESS_H:
            elem_size = 16

        elif vess == cs.arm64.ARM64_VESS_S:
            elem_size = 32

        elif vess == cs.arm64.ARM64_VESS_D:
            elem_size = 64

        else:
            raise Aarch64InvalidInstruction

        result = Operators.EXTRACT(reg, index * elem_size, elem_size)
        res_op.write(UInt(result, res_op.size))

    @instruction
    def UMULH(cpu, res_op, reg_op1, reg_op2):
        """
        UMULH.

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx = "1"
        insn_rx += "00"
        insn_rx += "11011"
        insn_rx += "1"  # U
        insn_rx += "10"
        insn_rx += "[01]{5}"  # Rm
        insn_rx += "0"
        insn_rx += "1{5}"  # Ra
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg1 = UInt(reg_op1.read(), reg_op1.size)
        reg2 = UInt(reg_op2.read(), reg_op2.size)

        reg1 = Operators.ZEXTEND(reg1, 128)
        reg2 = Operators.ZEXTEND(reg2, 128)

        result = Operators.EXTRACT(reg1 * reg2, 64, 64)
        res_op.write(result)

    @instruction
    def UXTB(cpu, res_op, reg_op):
        """
        UXTB.

        :param res_op: destination register.
        :param reg_op: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx = "0"  # sf
        insn_rx += "10"  # opc
        insn_rx += "100110"
        insn_rx += "0"  # N
        insn_rx += "0{6}"  # immr
        insn_rx += "000111"  # imms
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # Fake immediate operands.
        immr_op = Aarch64Operand.make_imm(cpu, 0)
        imms_op = Aarch64Operand.make_imm(cpu, 7)

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.UBFM.__wrapped__(cpu, res_op, reg_op, immr_op, imms_op)

    @instruction
    def UXTH(cpu, res_op, reg_op):
        """
        UXTH.

        :param res_op: destination register.
        :param reg_op: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx = "0"  # sf
        insn_rx += "10"  # opc
        insn_rx += "100110"
        insn_rx += "0"  # N
        insn_rx += "0{6}"  # immr
        insn_rx += "001111"  # imms
        insn_rx += "[01]{5}"  # Rn
        insn_rx += "[01]{5}"  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # Fake immediate operands.
        immr_op = Aarch64Operand.make_imm(cpu, 0)
        imms_op = Aarch64Operand.make_imm(cpu, 15)

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.UBFM.__wrapped__(cpu, res_op, reg_op, immr_op, imms_op)


class Aarch64CdeclAbi(Abi):
    """Aarch64/arm64 cdecl function call ABI"""

    # XXX: Floating-point arguments are not supported.
    # For floats and doubles, the first 8 arguments are passed via registers
    # (S0-S7 for floats, D0-D7 for doubles), then on stack.
    # The result is returned in S0 for floats and D0 for doubles.

    def get_arguments(self):
        # First 8 arguments are passed via X0-X7 (or W0-W7 if they are 32-bit),
        # then on stack.

        for reg in ("X0", "X1", "X2", "X3", "X4", "X5", "X6", "X7"):
            yield reg

        for address in self.values_from(self._cpu.STACK):
            yield address

    def get_result_reg(self):
        return "X0"

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
        return ("X{}".format(i) for i in range(6))

    def get_result_reg(self):
        return "X0"

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
            cs.arm64.ARM64_OP_BARRIER,
        ):
            raise NotImplementedError(f"Unsupported operand type: '{self.op.type}'")

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
                raise NotImplementedError(f"Unsupported system register: '0x{self.op.sys:x}'")
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
                raise NotImplementedError(f"Unsupported system register: '0x{self.op.sys:x}'")
            self.cpu.regfile.write(name, value)
        else:
            raise NotImplementedError(f"Unsupported operand type: '{self.type}'")
