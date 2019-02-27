import warnings

import capstone as cs
import collections
from decimal import Decimal
import re
import struct

from .abstractcpu import (
    Cpu, CpuException, Interruption, InstructionNotImplementedError,
    RegisterFile, Abi, SyscallAbi, Operand, instruction
)
from .arm import HighBit, Armv7Operand
from .bitwise import SInt, UInt, ASR, LSL, LSR, ROR, Mask
from .register import Register
from ...core.smtlib import Operators


class Aarch64InvalidInstruction(CpuException):
    pass


# Map different instructions to a single implementation.
OP_NAME_MAP = {
    # Make these go through 'MOV' to ensure that code path is reached.
    'MOVZ': 'MOV',
    'MOVN': 'MOV'
}


# See "C1.2.4 Condition code" in ARM Architecture Reference Manual
# ARMv8, for ARMv8-A architecture profile.
COND_MAP = {
    cs.arm64.ARM64_CC_EQ: lambda n, z, c, v: z == 1,
    cs.arm64.ARM64_CC_NE: lambda n, z, c, v: z == 0,
    cs.arm64.ARM64_CC_HS: lambda n, z, c, v: c == 1,
    cs.arm64.ARM64_CC_LO: lambda n, z, c, v: c == 0,
    cs.arm64.ARM64_CC_MI: lambda n, z, c, v: n == 1,
    cs.arm64.ARM64_CC_PL: lambda n, z, c, v: n == 0,
    cs.arm64.ARM64_CC_VS: lambda n, z, c, v: v == 1,
    cs.arm64.ARM64_CC_VC: lambda n, z, c, v: v == 0,
    cs.arm64.ARM64_CC_HI: lambda n, z, c, v: c == 1 and z == 0,
    cs.arm64.ARM64_CC_LS: lambda n, z, c, v: not (c == 1 and z == 0),
    cs.arm64.ARM64_CC_GE: lambda n, z, c, v: n == v,
    cs.arm64.ARM64_CC_LT: lambda n, z, c, v: n != v,
    cs.arm64.ARM64_CC_GT: lambda n, z, c, v: z == 0 and n == v,
    cs.arm64.ARM64_CC_LE: lambda n, z, c, v: not (z == 0 and n == v),
    cs.arm64.ARM64_CC_AL: lambda n, z, c, v: True,
    cs.arm64.ARM64_CC_NV: lambda n, z, c, v: True
}


class Aarch64RegisterFile(RegisterFile):
    Regspec = collections.namedtuple('RegSpec', 'parent size')

    # Register table.
    _table = {}

    # From "B1.2 Registers in AArch64 Execution state" in the ARM Architecture
    # Reference Manual: ARMv8, for ARMv8-A architecture profile:
    #
    # 31 general-purpose registers, R0 to R30.
    # Each register can be accessed as:
    # * A 64-bit general-purpose register named X0 to X30.
    # * A 32-bit general-purpose register named W0 to W30.
    for i in range(31):
        _table[f'X{i}'] = Regspec(f'X{i}', 64)
        _table[f'W{i}'] = Regspec(f'X{i}', 32)

    # A 64-bit dedicated Stack Pointer register.  The least significant 32 bits
    # of the stack-pointer can be accessed via the register name WSP.
    #
    # The use of SP as an operand in an instruction, indicates the use of the
    # current stack pointer.
    _table['SP']  = Regspec('SP', 64)
    _table['WSP'] = Regspec('SP', 32)

    # A 64-bit Program Counter holding the address of the current instruction.
    # Software cannot write directly to the PC.  It can only be updated on a
    # branch, exception entry or exception return.
    #
    # Attempting to execute an A64 instruction that is not word-aligned
    # generates a PC alignment fault, see "PC alignment checking".
    _table['PC'] = Regspec('PC', 64)

    # 32 SIMD&FP registers, V0 to V31.
    # Each register can be accessed as:
    # * A 128-bit register named Q0 to Q31.
    # * A 64-bit register named D0 to D31.
    # * A 32-bit register named S0 to S31.
    # * A 16-bit register named H0 to H31.
    # * An 8-bit register named B0 to B31.
    # * A 128-bit vector of elements.
    # * A 64-bit vector of elements.
    #
    # Where the number of bits described by a register name does not occupy an entire
    # SIMD&FP register, it refers to the least significant bits.
    for i in range(32):
        _table[f'Q{i}'] = Regspec(f'Q{i}', 128)
        _table[f'D{i}'] = Regspec(f'Q{i}', 64)
        _table[f'S{i}'] = Regspec(f'Q{i}', 32)
        _table[f'H{i}'] = Regspec(f'Q{i}', 16)
        _table[f'B{i}'] = Regspec(f'Q{i}', 8)
        # XXX: Support vectors.
        # For more information about data types and vector formats, see "Supported
        # data types".

    # Two SIMD and floating-point control and status registers, FPCR and FPSR.
    _table['FPCR'] = Regspec('FPCR', 64)
    _table['FPSR'] = Regspec('FPSR', 64)

    # Condition flags.
    # Flag-setting instructions set these.
    #
    # N Negative Condition flag.  If the result of the instruction is regarded
    # as a two's complement signed integer, the PE sets this to:
    # * 1 if the result is negative.
    # * 0 if the result is positive or zero.
    #
    # Z Zero Condition flag.  Set to:
    # * 1 if the result of the instruction is zero.
    # * 0 otherwise.
    # A result of zero often indicates an equal result from a comparison.
    #
    # C Carry Condition flag.  Set to:
    # * 1 if the instruction results in a carry condition, for example an unsigned overflow
    #   that is the result of an addition.
    # * 0 otherwise.
    #
    # V Overflow Condition flag.  Set to:
    # * 1 if the instruction results in an overflow condition, for example a signed
    #   overflow that is the result of an addition.
    # * 0 otherwise.
    #
    # Conditional instructions test the N, Z, C and V Condition flags, combining them
    # with the Condition code for the instruction to determine whether the instruction
    # must be executed.  In this way, execution of the instruction is conditional on
    # the result of a previous operation.  For more information about conditional
    # execution, see "Condition flags and related instructions".
    #
    # Also see "C5.2.9 NZCV, Condition Flags".
    # Counting from the right:
    # N, bit [31]
    # Z, bit [30]
    # C, bit [29]
    # V, bit [28]
    _table['NZCV'] = Regspec('NZCV', 64)

    # From "C1.2.5 Register names":
    # Zero register.
    _table['XZR'] = Regspec('XZR', 64)
    _table['WZR'] = Regspec('XZR', 32)

    def __init__(self):
        # Register aliases.
        _aliases = {
            # This one is required by the 'Cpu' class.
            'STACK': 'SP',
            # From "5.1 Machine Registers" in Procedure Call Standard for the ARM 64-bit
            # Architecture (AArch64):
            # Frame pointer.
            'FP': 'X29',
            # Intra-procedure-call temporary registers (can be used by call veneers
            # and PLT code); at other times may be used as temporary registers.
            'IP1': 'X17',
            'IP0': 'X16',
            # From "B1.2 Registers in AArch64 Execution state" in the ARM Architecture
            # Reference Manual: ARMv8, for ARMv8-A architecture profile:
            # The X30 general-purpose register is used as the procedure call
            # link register.
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

        if name != parent:
            _, parent_size = self._table[parent]
            if size < parent_size:
                value = Operators.EXTRACT(value, 0, size)

        return value

    def write(self, register, value):
        assert register in self
        name = self._alias(register)
        parent, size = self._table[name]
        assert value <= 2 ** size - 1
        # Ignore writes to the zero register.
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
        return self._parent_registers - not_supported

    @property
    def all_registers(self):
        return self._all_registers

    # See "C5.2.9 NZCV, Condition Flags".
    # Counting from the right:
    # N, bit [31]
    # Z, bit [30]
    # C, bit [29]
    # V, bit [28]
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
        n, z, c, v = value
        assert n in [0, 1]
        assert z in [0, 1]
        assert c in [0, 1]
        assert v in [0, 1]

        nzcv = self.read('NZCV')
        mask = 0xf0000000

        n = LSL(n, 31, 32)
        z = LSL(z, 30, 32)
        c = LSL(c, 29, 32)
        v = LSL(v, 28, 32)

        result = (nzcv & ~mask) | n | z | c | v
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
    # From "A1.3.2 The ARMv8 instruction sets" in ARM Architecture Reference
    # Manual ARMv8, for ARMv8-A architecture profile:
    # AArch64 state supports only a single instruction set, called A64.  This is
    # a fixed-length instruction set that uses 32-bit instruction encodings.
    mode = cs.CS_ARCH_ARM

    # The A64 instruction set does not support conditional execution for every
    # instruction.  There is a small set of conditional data processing
    # instructions that are unconditionally executed but use the condition flags
    # as an extra input to the instruction.
    #
    # The A64 instruction set enables conditional execution of only program flow
    # control branch instructions.  This is in contrast to A32 and T32 where
    # most instructions can be predicated with a condition code.
    #
    # See "6.2.5 Conditional instructions" in ARM Cortex-A Series
    # Programmer's Guide for ARMv8-A.

    def __init__(self, memory):
        warnings.warn('Aarch64 support is experimental')
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
            not ops[2].is_shifted()
           ):
            name = 'MOV'
            del ops[1]

        # Map all B.cond variants to a single implementation.
        elif (len(name_list) == 2 and
              name_list[0] == 'B' and
              insn.cc != cs.arm64.ARM64_CC_INVALID
             ):
            name = 'B_cond'

        return name

    @property
    def insn_bit_str(self):
        # XXX: Hardcoded endianness and instruction size.
        insn = struct.unpack("<I", self.instruction.bytes)[0]
        return f'{insn:032b}'

    def cond_holds(cpu):
        cond = cpu.instruction.cc
        return COND_MAP[cond](*cpu.regfile.nzcv)

    # XXX: Use masking when writing to the destination register?  Avoiding this
    # for now, but the assert in the 'write' method should catch such cases.

    def _shifted_register(cpu, res_op, reg_op1, reg_op2, action, shifts):
        reg1 = reg_op1.read()
        reg2 = reg_op2.read()
        reg2_size = cpu.regfile.size(reg_op2.reg)

        if reg_op2.is_shifted():
            shift = reg_op2.shift

            assert (
                (res_op.size == 32 and shift.value in range(0, 32)) or
                (res_op.size == 64 and shift.value in range(0, 64))
            )

            if (shift.type == cs.arm64.ARM64_SFT_LSL and
                shift.type in shifts):
                reg2 = LSL(reg2, shift.value, reg2_size)

            elif (shift.type == cs.arm64.ARM64_SFT_LSR and
                  shift.type in shifts):
                reg2 = LSR(reg2, shift.value, reg2_size)

            elif (shift.type == cs.arm64.ARM64_SFT_ASR and
                  shift.type in shifts):
                reg2 = ASR(reg2, shift.value, reg2_size)

            elif (shift.type == cs.arm64.ARM64_SFT_ROR and
                  shift.type in shifts):
                reg2 = ROR(reg2, shift.value, reg2_size)

            else:
                raise Aarch64InvalidInstruction

        result = UInt(action(reg1, reg2), res_op.size)
        res_op.write(result)
        return result

    def _ldr_str_immediate(cpu, reg_op, mem_op, mimm_op, ldr):
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert mem_op.type is cs.arm64.ARM64_OP_MEM
        assert not mimm_op or mimm_op.type is cs.arm64.ARM64_OP_IMM

        post_index_rx  = '1[01]'    # size
        post_index_rx += '111'
        post_index_rx += '0'
        post_index_rx += '00'
        if ldr:
            post_index_rx += '01'   # opc
        else:
            post_index_rx += '00'   # opc
        post_index_rx += '0'
        post_index_rx += '[01]{9}'  # imm9
        post_index_rx += '01'
        post_index_rx += '[01]{5}'  # Rn
        post_index_rx += '[01]{5}'  # Rt

        pre_index_rx  = '1[01]'     # size
        pre_index_rx += '111'
        pre_index_rx += '0'
        pre_index_rx += '00'
        if ldr:
            pre_index_rx += '01'    # opc
        else:
            pre_index_rx += '00'    # opc
        pre_index_rx += '0'
        pre_index_rx += '[01]{9}'   # imm9
        pre_index_rx += '11'
        pre_index_rx += '[01]{5}'   # Rn
        pre_index_rx += '[01]{5}'   # Rt

        unsigned_offset_rx  = '1[01]'     # size
        unsigned_offset_rx += '111'
        unsigned_offset_rx += '0'
        unsigned_offset_rx += '01'
        if ldr:
            unsigned_offset_rx += '01'    # opc
        else:
            unsigned_offset_rx += '00'    # opc
        unsigned_offset_rx += '[01]{12}'  # imm12
        unsigned_offset_rx += '[01]{5}'   # Rn
        unsigned_offset_rx += '[01]{5}'   # Rt

        assert (
            re.match(post_index_rx, cpu.insn_bit_str) or
            re.match(pre_index_rx, cpu.insn_bit_str) or
            re.match(unsigned_offset_rx, cpu.insn_bit_str)
        )

        base = cpu.regfile.read(mem_op.mem.base)
        imm = mem_op.mem.disp

        if mimm_op:  # post-indexed
            wback = mimm_op.op.imm
        else:
            wback = imm  # use it for writeback if applicable

        if ldr:
            result = cpu.read_int(base + imm, reg_op.size)
            reg_op.write(result)
        else:
            reg = reg_op.read()
            cpu.write_int(base + imm, reg, reg_op.size)

        if cpu.instruction.writeback:
            cpu.regfile.write(mem_op.mem.base, base + wback)

    def _ldr_str_register(cpu, reg_op, mem_op, ldr):
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert mem_op.type is cs.arm64.ARM64_OP_MEM

        insn_rx  = '1[01]'    # size
        insn_rx += '111'
        insn_rx += '0'
        insn_rx += '00'
        if ldr:
            insn_rx += '01'   # opc
        else:
            insn_rx += '00'   # opc
        insn_rx += '1'
        insn_rx += '[01]{5}'  # Rm
        insn_rx += '[01]{3}'  # option
        insn_rx += '[01]'     # S
        insn_rx += '10'
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '[01]{5}'  # Rt

        assert re.match(insn_rx, cpu.insn_bit_str)

        base = cpu.regfile.read(mem_op.mem.base)
        index = cpu.regfile.read(mem_op.mem.index)
        index_size = cpu.regfile.size(mem_op.mem.index)

        if mem_op.is_extended():
            ext = mem_op.op.ext

            assert ext in [
                cs.arm64.ARM64_EXT_UXTW,
                cs.arm64.ARM64_EXT_SXTW,
                cs.arm64.ARM64_EXT_SXTX
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
            result = cpu.read_int(base + index, reg_op.size)
            reg_op.write(result)
        else:
            reg = reg_op.read()
            cpu.write_int(base + index, reg, reg_op.size)

    def _ldur_stur(cpu, reg_op, mem_op, ldur):
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert mem_op.type is cs.arm64.ARM64_OP_MEM

        insn_rx  = '1[01]'    # size
        insn_rx += '111'
        insn_rx += '0'
        insn_rx += '00'
        if ldur:
            insn_rx += '01'   # opc
        else:
            insn_rx += '00'   # opc
        insn_rx += '0'
        insn_rx += '[01]{9}'  # imm9
        insn_rx += '00'
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '[01]{5}'  # Rt

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

    def _ADD_immediate(cpu, res_op, reg_op, imm_op):
        """
        ADD (immediate).

        Add (immediate) adds a register value and an optionally-shifted
        immediate value, and writes the result to the destination register.

        This instruction is used by the alias MOV (to/from SP).

        :param res_op: destination register.
        :param reg_op: source register.
        :param imm_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx  = '[01]'              # sf
        insn_rx += '0'                 # op
        insn_rx += '0'                 # S
        insn_rx += '10001'
        insn_rx += '(?!1[01])[01]{2}'  # shift != 1x
        insn_rx += '[01]{12}'          # imm12
        insn_rx += '[01]{5}'           # Rn
        insn_rx += '[01]{5}'           # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        imm = imm_op.op.imm
        assert imm in range(0, 4096)

        if imm_op.is_shifted():
            shift = imm_op.op.shift
            assert shift.type == cs.arm64.ARM64_SFT_LSL
            assert shift.value in [0, 12]
            imm = LSL(imm, shift.value, res_op.size)

        result = UInt(reg + imm, res_op.size)
        res_op.write(result)

    def _ADD_shifted_register(cpu, res_op, reg_op1, reg_op2):
        """
        ADD (shifted register).

        Add (shifted register) adds a register value and an optionally-shifted
        register value, and writes the result to the destination register.

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type  is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx  = '[01]'     # sf
        insn_rx += '0'        # op
        insn_rx += '0'        # S
        insn_rx += '01011'
        insn_rx += '[01]{2}'  # shift
        insn_rx += '0'
        insn_rx += '[01]{5}'  # Rm
        insn_rx += '[01]{6}'  # imm6
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '[01]{5}'  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        cpu._shifted_register(
            res_op = res_op,
            reg_op1 = reg_op1,
            reg_op2 = reg_op2,
            action = lambda x, y: x + y,
            shifts = [
                cs.arm64.ARM64_SFT_LSL,
                cs.arm64.ARM64_SFT_LSR,
                cs.arm64.ARM64_SFT_ASR
            ])

    @instruction
    def ADD(cpu, res_op, op1, op2):
        """
        Combines ADD (immediate) and ADD (shifted register).

        :param res_op: destination register.
        :param op1: source register.
        :param op2: source register or immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert op1.type    is cs.arm64.ARM64_OP_REG
        assert op2.type    in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]

        bit21 = cpu.insn_bit_str[-22]

        if op2.type == cs.arm64.ARM64_OP_IMM:
            cpu._ADD_immediate(res_op, op1, op2)

        elif op2.type == cs.arm64.ARM64_OP_REG and bit21 == '0':
            cpu._ADD_shifted_register(res_op, op1, op2)

        # XXX: Support the extended register variant (update the docstring).
        # elif op2.type == cs.arm64.ARM64_OP_REG and bit21 == '1':

        else:
            raise Aarch64InvalidInstruction

    @instruction
    def ADR(cpu, res_op, imm_op):
        """
        ADR.

        Form PC-relative address adds an immediate value to the PC value to form
        a PC-relative address, and writes the result to the destination
        register.

        :param res_op: destination register.
        :param imm_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx  = '0'         # op
        insn_rx += '[01]{2}'   # immlo
        insn_rx += '10000'
        insn_rx += '[01]{19}'  # immhi
        insn_rx += '[01]{5}'   # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        imm = imm_op.op.imm  # PC + offset
        res_op.write(imm)

    @instruction
    def ADRP(cpu, res_op, imm_op):
        """
        ADRP.

        Form PC-relative address to 4KB page adds an immediate value that is
        shifted left by 12 bits, to the PC value to form a PC-relative address,
        with the bottom 12 bits masked out, and writes the result to the
        destination register.

        :param res_op: destination register.
        :param imm_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx  = '1'         # op
        insn_rx += '[01]{2}'   # immlo
        insn_rx += '10000'
        insn_rx += '[01]{19}'  # immhi
        insn_rx += '[01]{5}'   # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        imm = imm_op.op.imm  # PC + offset
        res_op.write(imm)

    def _AND_immediate(cpu, res_op, reg_op, imm_op):
        """
        AND (immediate).

        Bitwise AND (immediate) performs a bitwise AND of a register value and
        an immediate value, and writes the result to the destination register.

        :param res_op: destination register.
        :param reg_op: source register.
        :param imm_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx  = '[01]'     # sf
        insn_rx += '00'       # opc
        insn_rx += '100100'
        insn_rx += '[01]'     # N
        insn_rx += '[01]{6}'  # immr
        insn_rx += '[01]{6}'  # imms
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '[01]{5}'  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        imm = imm_op.op.imm
        result = UInt(reg & imm, res_op.size)
        res_op.write(result)

    def _AND_shifted_register(cpu, res_op, reg_op1, reg_op2):
        """
        AND (shifted register).

        Bitwise AND (shifted register) performs a bitwise AND of a register
        value and an optionally-shifted register value, and writes the result to
        the destination register.

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type  is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx  = '[01]'     # sf
        insn_rx += '00'       # opc
        insn_rx += '01010'
        insn_rx += '[01]{2}'  # shift
        insn_rx += '0'        # N
        insn_rx += '[01]{5}'  # Rm
        insn_rx += '[01]{6}'  # imm6
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '[01]{5}'  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        cpu._shifted_register(
            res_op = res_op,
            reg_op1 = reg_op1,
            reg_op2 = reg_op2,
            action = lambda x, y: x & y,
            shifts = [
                cs.arm64.ARM64_SFT_LSL,
                cs.arm64.ARM64_SFT_LSR,
                cs.arm64.ARM64_SFT_ASR,
                cs.arm64.ARM64_SFT_ROR
            ])

    @instruction
    def AND(cpu, res_op, op1, op2):
        """
        Combines AND (immediate) and AND (shifted register).

        :param res_op: destination register.
        :param op1: source register.
        :param op2: source register or immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert op1.type is cs.arm64.ARM64_OP_REG
        assert op2.type in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]

        if op2.type == cs.arm64.ARM64_OP_REG:
            cpu._AND_shifted_register(res_op, op1, op2)

        elif op2.type == cs.arm64.ARM64_OP_IMM:
            cpu._AND_immediate(res_op, op1, op2)

        else:
            raise Aarch64InvalidInstruction

    def _ANDS_immediate(cpu, res_op, reg_op, imm_op):
        """
        ANDS (immediate).

        Bitwise AND (immediate), setting flags, performs a bitwise AND of a
        register value and an immediate value, and writes the result to the
        destination register.  It updates the condition flags based on the
        result.

        This instruction is used by the alias TST (immediate).

        :param res_op: destination register.
        :param reg_op: source register.
        :param imm_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx  = '[01]'     # sf
        insn_rx += '11'       # opc
        insn_rx += '100100'
        insn_rx += '[01]'     # N
        insn_rx += '[01]{6}'  # immr
        insn_rx += '[01]{6}'  # imms
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '[01]{5}'  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        imm = imm_op.op.imm
        result = UInt(reg & imm, res_op.size)
        res_op.write(result)

        n = Operators.EXTRACT(result, res_op.size - 1, 1)
        z = 1 if result == 0 else 0
        cpu.regfile.nzcv = (n, z, 0, 0)

    def _ANDS_shifted_register(cpu, res_op, reg_op1, reg_op2):
        """
        ANDS (shifted register).

        Bitwise AND (shifted register), setting flags, performs a bitwise AND of
        a register value and an optionally-shifted register value, and writes
        the result to the destination register.  It updates the condition flags
        based on the result.

        This instruction is used by the alias TST (shifted register).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type  is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx  = '[01]'     # sf
        insn_rx += '11'       # opc
        insn_rx += '01010'
        insn_rx += '[01]{2}'  # shift
        insn_rx += '0'        # N
        insn_rx += '[01]{5}'  # Rm
        insn_rx += '[01]{6}'  # imm6
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '[01]{5}'  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        result = cpu._shifted_register(
            res_op = res_op,
            reg_op1 = reg_op1,
            reg_op2 = reg_op2,
            action = lambda x, y: x & y,
            shifts = [
                cs.arm64.ARM64_SFT_LSL,
                cs.arm64.ARM64_SFT_LSR,
                cs.arm64.ARM64_SFT_ASR,
                cs.arm64.ARM64_SFT_ROR
            ])

        # XXX: Maybe move this inside the method.
        n = Operators.EXTRACT(result, res_op.size - 1, 1)
        z = 1 if result == 0 else 0
        cpu.regfile.nzcv = (n, z, 0, 0)

    @instruction
    def ANDS(cpu, res_op, op1, op2):
        """
        Combines ANDS (immediate) and ANDS (shifted register).

        :param res_op: destination register.
        :param op1: source register.
        :param op2: source register or immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert op1.type is cs.arm64.ARM64_OP_REG
        assert op2.type in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]

        if op2.type == cs.arm64.ARM64_OP_REG:
            cpu._ANDS_shifted_register(res_op, op1, op2)

        elif op2.type == cs.arm64.ARM64_OP_IMM:
            cpu._ANDS_immediate(res_op, op1, op2)

        else:
            raise Aarch64InvalidInstruction

    @instruction
    def B_cond(cpu, imm_op):
        """
        B.cond.

        Branch conditionally to a label at a PC-relative offset, with a hint
        that this is not a subroutine call or return.

        :param imm_op: immediate.
        """
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx  = '0101010'
        insn_rx += '0'
        insn_rx += '[01]{19}'  # imm19
        insn_rx += '0'
        insn_rx += '[01]{4}'   # cond

        assert re.match(insn_rx, cpu.insn_bit_str)

        imm = imm_op.op.imm

        if cpu.cond_holds():
            cpu.PC = imm

    @instruction
    def B(cpu, imm_op):
        """
        B.

        Branch causes an unconditional branch to a label at a PC-relative
        offset, with a hint that this is not a subroutine call or return.

        :param imm_op: immediate.
        """
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx  = '0'         # op
        insn_rx += '00101'
        insn_rx += '[01]{26}'  # imm26

        assert re.match(insn_rx, cpu.insn_bit_str)

        imm = imm_op.op.imm
        cpu.PC = imm

    @instruction
    def BIC(cpu, res_op, reg_op1, reg_op2):
        """
        BIC (shifted register).

        Bitwise Bit Clear (shifted register) performs a bitwise AND of a
        register value and the complement of an optionally-shifted register
        value, and writes the result to the destination register.

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type  is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx  = '[01]'     # sf
        insn_rx += '00'       # opc
        insn_rx += '01010'
        insn_rx += '[01]{2}'  # shift
        insn_rx += '1'        # N
        insn_rx += '[01]{5}'  # Rm
        insn_rx += '[01]{6}'  # imm6
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '[01]{5}'  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        cpu._shifted_register(
            res_op = res_op,
            reg_op1 = reg_op1,
            reg_op2 = reg_op2,
            action = lambda x, y: x & ~y,
            shifts = [
                cs.arm64.ARM64_SFT_LSL,
                cs.arm64.ARM64_SFT_LSR,
                cs.arm64.ARM64_SFT_ASR,
                cs.arm64.ARM64_SFT_ROR
            ])

    @instruction
    def BICS(cpu, res_op, reg_op1, reg_op2):
        """
        BICS (shifted register).

        Bitwise Bit Clear (shifted register), setting flags, performs a bitwise
        AND of a register value and the complement of an optionally-shifted
        register value, and writes the result to the destination register.  It
        updates the condition flags based on the result.

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type  is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx  = '[01]'     # sf
        insn_rx += '11'       # opc
        insn_rx += '01010'
        insn_rx += '[01]{2}'  # shift
        insn_rx += '1'        # N
        insn_rx += '[01]{5}'  # Rm
        insn_rx += '[01]{6}'  # imm6
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '[01]{5}'  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        result = cpu._shifted_register(
            res_op = res_op,
            reg_op1 = reg_op1,
            reg_op2 = reg_op2,
            action = lambda x, y: x & ~y,
            shifts = [
                cs.arm64.ARM64_SFT_LSL,
                cs.arm64.ARM64_SFT_LSR,
                cs.arm64.ARM64_SFT_ASR,
                cs.arm64.ARM64_SFT_ROR
            ])

        # XXX: Maybe move this inside the method.
        n = Operators.EXTRACT(result, res_op.size - 1, 1)
        z = 1 if result == 0 else 0
        cpu.regfile.nzcv = (n, z, 0, 0)

    @instruction
    def BL(cpu, imm_op):
        """
        BL.

        Branch with Link branches to a PC-relative offset, setting the register
        X30 to PC+4.  It provides a hint that this is a subroutine call.

        :param imm_op: immediate.
        """
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx  = '1'         # op
        insn_rx += '00101'
        insn_rx += '[01]{26}'  # imm26

        assert re.match(insn_rx, cpu.insn_bit_str)

        imm = imm_op.op.imm
        # The 'instruction' decorator makes PC point to the next instruction.
        cpu.X30 = cpu.PC
        cpu.PC = imm

    @instruction
    def BLR(cpu, reg_op):
        """
        BLR.

        Branch with Link to Register calls a subroutine at an address in a
        register, setting register X30 to PC+4.

        :param reg_op: register.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx  = '1101011'
        insn_rx += '0'        # Z
        insn_rx += '0'
        insn_rx += '01'       # op
        insn_rx += '1{5}'
        insn_rx += '0{4}'
        insn_rx += '0'        # A
        insn_rx += '0'        # M
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '0{5}'     # Rm

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        # The 'instruction' decorator makes PC point to the next instruction.
        cpu.X30 = cpu.PC
        cpu.PC = reg

    @instruction
    def BR(cpu, reg_op):
        """
        BR.

        Branch to Register branches unconditionally to an address in a register,
        with a hint that this is not a subroutine return.

        :param reg_op: register.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx  = '1101011'
        insn_rx += '0'        # Z
        insn_rx += '0'
        insn_rx += '00'       # op
        insn_rx += '1{5}'
        insn_rx += '0{4}'
        insn_rx += '0'        # A
        insn_rx += '0'        # M
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '0{5}'     # Rm

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        cpu.PC = reg

    @instruction
    def CBNZ(cpu, reg_op, imm_op):
        """
        CBNZ.

        Compare and Branch on Nonzero compares the value in a register with
        zero, and conditionally branches to a label at a PC-relative offset if
        the comparison is not equal.  It provides a hint that this is not a
        subroutine call or return.  This instruction does not affect the
        condition flags.

        :param reg_op: register.
        :param imm_op: immediate.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx  = '[01]'      # sf
        insn_rx += '011010'
        insn_rx += '1'         # op
        insn_rx += '[01]{19}'  # imm19
        insn_rx += '[01]{5}'   # Rt

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        imm = imm_op.op.imm

        if reg != 0:
            cpu.PC = imm

    @instruction
    def CBZ(cpu, reg_op, imm_op):
        """
        CBZ.

        Compare and Branch on Zero compares the value in a register with zero,
        and conditionally branches to a label at a PC-relative offset if the
        comparison is equal.  It provides a hint that this is not a subroutine
        call or return.  This instruction does not affect condition flags.

        :param reg_op: register.
        :param imm_op: immediate.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx  = '[01]'      # sf
        insn_rx += '011010'
        insn_rx += '0'         # op
        insn_rx += '[01]{19}'  # imm19
        insn_rx += '[01]{5}'   # Rt

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        imm = imm_op.op.imm

        if reg == 0:
            cpu.PC = imm

    @instruction
    def CLZ(cpu, res_op, reg_op):
        """
        CLZ.

        Count Leading Zeros counts the number of binary zero bits before the
        first binary one bit in the value of the source register, and writes the
        result to the destination register.

        :param res_op: destination register.
        :param reg_op: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx  = '[01]'     # sf
        insn_rx += '1'
        insn_rx += '0'
        insn_rx += '11010110'
        insn_rx += '0{5}'
        insn_rx += '00010'
        insn_rx += '0'        # op
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '[01]{5}'  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        size = reg_op.size

        count = 0
        for pos in range(size - 1, -1, -1):
            if Operators.EXTRACT(reg, pos, 1) == 1:
                break
            count += 1

        res_op.write(count)

    @instruction
    def CSEL(cpu, res_op, reg_op1, reg_op2):
        """
        CSEL.

        Conditional Select returns, in the destination register, the value of
        the first source register if the condition is TRUE, and otherwise
        returns the value of the second source register.

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type  is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx  = '[01]'      # sf
        insn_rx += '0'         # op
        insn_rx += '0'
        insn_rx += '11010100'
        insn_rx += '[01]{5}'   # Rm
        insn_rx += '[01]{4}'   # cond
        insn_rx += '0'
        insn_rx += '0'         # o2
        insn_rx += '[01]{5}'   # Rn
        insn_rx += '[01]{5}'   # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg1 = reg_op1.read()
        reg2 = reg_op2.read()

        if cpu.cond_holds():
            result = reg1
        else:
            result = reg2

        res_op.write(result)

    def _LDR_immediate(cpu, reg_op, mem_op, mimm_op):
        """
        LDR (immediate).

        Load Register (immediate) loads a word or doubleword from memory and
        writes it to a register.  The address that is used for the load is
        calculated from a base register and an immediate offset.

        :param reg_op: destination register.
        :param mem_op: memory.
        :param mimm_op: None or immediate.
        """
        cpu._ldr_str_immediate(reg_op, mem_op, mimm_op, ldr=True)

    def _LDR_literal(cpu, dst, src):
        """
        LDR (literal).

        Load Register (literal) calculates an address from the PC value and an
        immediate offset, loads a word from memory, and writes it to a register.

        :param dst: destination register.
        :param src: immediate.
        """
        assert dst.type is cs.arm64.ARM64_OP_REG
        assert src.type is cs.arm64.ARM64_OP_IMM

        insn_rx  = '0[01]'     # opc
        insn_rx += '011'
        insn_rx += '0'
        insn_rx += '00'
        insn_rx += '[01]{19}'  # imm19
        insn_rx += '[01]{5}'   # Rt

        assert re.match(insn_rx, cpu.insn_bit_str)

        imm = src.op.imm
        result = cpu.read_int(imm, dst.size)
        dst.write(result)

    def _LDR_register(cpu, reg_op, mem_op):
        """
        LDR (register).

        Load Register (register) calculates an address from a base register
        value and an offset register value, loads a word from memory, and writes
        it to a register.  The offset register value can optionally be shifted
        and extended.

        :param reg_op: destination register.
        :param mem_op: memory.
        """
        cpu._ldr_str_register(reg_op, mem_op, ldr=True)

    @instruction
    def LDR(cpu, dst, src, rest=None):
        """
        Combines LDR (immediate), LDR (literal), and LDR (register).

        :param dst: destination register.
        :param src: memory or immediate.
        :param rest: None or immediate.
        """
        assert dst.type is cs.arm64.ARM64_OP_REG
        assert src.type in [cs.arm64.ARM64_OP_MEM, cs.arm64.ARM64_OP_IMM]
        assert not rest or rest.type is cs.arm64.ARM64_OP_IMM

        if src.type == cs.arm64.ARM64_OP_MEM:
            if src.mem.index:
                cpu._LDR_register(dst, src)
            else:
                cpu._LDR_immediate(dst, src, rest)

        elif src.type == cs.arm64.ARM64_OP_IMM:
            cpu._LDR_literal(dst, src)

        else:
            raise Aarch64InvalidInstruction

    @instruction
    def LDUR(cpu, reg_op, mem_op):
        """
        LDUR.

        Load Register (unscaled) calculates an address from a base register and
        an immediate offset, loads a 32-bit word or 64-bit doubleword from
        memory, zero-extends it, and writes it to a register.

        :param reg_op: destination register.
        :param mem_op: memory.
        """
        cpu._ldur_stur(reg_op, mem_op, ldur=True)

    def _LSL_immediate(cpu, res_op, reg_op, imm_op):
        """
        LSL (immediate).

        Logical Shift Left (immediate) shifts a register value left by an
        immediate number of bits, shifting in zeros, and writes the result to
        the destination register.

        This instruction is an alias of the UBFM instruction.

        :param res_op: destination register.
        :param reg_op: source register.
        :param imm_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx  = '[01]'     # sf
        insn_rx += '10'       # opc
        insn_rx += '100110'
        insn_rx += '[01]'     # N
        insn_rx += '[01]{6}'  # immr
        insn_rx += '[01]{6}'  # imms
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '[01]{5}'  # Rd

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

        Logical Shift Left (register) shifts a register value left by a variable
        number of bits, shifting in zeros, and writes the result to the
        destination register.  The remainder obtained by dividing the second
        source register by the data size defines the number of bits by which the
        first source register is left-shifted.

        This instruction is an alias of the LSLV instruction.

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx  = '[01]'      # sf
        insn_rx += '0'
        insn_rx += '0'
        insn_rx += '11010110'
        insn_rx += '[01]{5}'   # Rm
        insn_rx += '0010'
        insn_rx += '00'        # op2
        insn_rx += '[01]{5}'   # Rn
        insn_rx += '[01]{5}'   # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.LSLV.__wrapped__(cpu, res_op, reg_op1, reg_op2)

    @instruction
    def LSL(cpu, res_op, op1, op2):
        """
        Combines LSL (register) and LSL (immediate).

        :param res_op: destination register.
        :param op1: source register.
        :param op2: source register or immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert op1.type is cs.arm64.ARM64_OP_REG
        assert op2.type in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]

        if op2.type == cs.arm64.ARM64_OP_REG:
            cpu._LSL_register(res_op, op1, op2)

        elif op2.type == cs.arm64.ARM64_OP_IMM:
            cpu._LSL_immediate(res_op, op1, op2)

        else:
            raise Aarch64InvalidInstruction

    @instruction
    def LSLV(cpu, res_op, reg_op1, reg_op2):
        """
        LSLV.

        Logical Shift Left Variable shifts a register value left by a variable
        number of bits, shifting in zeros, and writes the result to the
        destination register.  The remainder obtained by dividing the second
        source register by the data size defines the number of bits by which the
        first source register is left-shifted.

        This instruction is used by the alias LSL (register).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx  = '[01]'      # sf
        insn_rx += '0'
        insn_rx += '0'
        insn_rx += '11010110'
        insn_rx += '[01]{5}'   # Rm
        insn_rx += '0010'
        insn_rx += '00'        # op2
        insn_rx += '[01]{5}'   # Rn
        insn_rx += '[01]{5}'   # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op1.read()
        sft = reg_op2.read()

        result = LSL(reg, sft % res_op.size, res_op.size)
        res_op.write(result)

    def _LSR_immediate(cpu, res_op, reg_op, immr_op):
        """
        LSR (immediate).

        Logical Shift Right (immediate) shifts a register value right by an
        immediate number of bits, shifting in zeros, and writes the result to
        the destination register.

        This instruction is an alias of the UBFM instruction.

        :param res_op: destination register.
        :param reg_op: source register.
        :param immr_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert immr_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx  = '[01]'      # sf
        insn_rx += '10'        # opc
        insn_rx += '100110'
        insn_rx += '[01]'      # N
        insn_rx += '[01]{6}'   # immr
        insn_rx += '[01]1{5}'  # imms
        insn_rx += '[01]{5}'   # Rn
        insn_rx += '[01]{5}'   # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # Fake an immediate operand.
        imms_op = Aarch64Operand.make_imm(cpu, res_op.size - 1)

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.UBFM.__wrapped__(cpu, res_op, reg_op, immr_op, imms_op)

    def _LSR_register(cpu, res_op, reg_op1, reg_op2):
        """
        LSR (register).

        Logical Shift Right (register) shifts a register value right by a
        variable number of bits, shifting in zeros, and writes the result to the
        destination register.  The remainder obtained by dividing the second
        source register by the data size defines the number of bits by which the
        first source register is right-shifted.

        This instruction is an alias of the LSRV instruction.

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx  = '[01]'      # sf
        insn_rx += '0'
        insn_rx += '0'
        insn_rx += '11010110'
        insn_rx += '[01]{5}'   # Rm
        insn_rx += '0010'
        insn_rx += '01'        # op2
        insn_rx += '[01]{5}'   # Rn
        insn_rx += '[01]{5}'   # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        # The 'instruction' decorator advances PC, so call the original
        # method.
        cpu.LSRV.__wrapped__(cpu, res_op, reg_op1, reg_op2)

    @instruction
    def LSR(cpu, res_op, op1, op2):
        """
        Combines LSR (register) and LSR (immediate).

        :param res_op: destination register.
        :param op1: source register.
        :param op2: source register or immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert op1.type is cs.arm64.ARM64_OP_REG
        assert op2.type in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]

        if op2.type == cs.arm64.ARM64_OP_REG:
            cpu._LSR_register(res_op, op1, op2)

        elif op2.type == cs.arm64.ARM64_OP_IMM:
            cpu._LSR_immediate(res_op, op1, op2)

        else:
            raise Aarch64InvalidInstruction

    @instruction
    def LSRV(cpu, res_op, reg_op1, reg_op2):
        """
        LSRV.

        Logical Shift Right Variable shifts a register value right by a variable
        number of bits, shifting in zeros, and writes the result to the
        destination register.  The remainder obtained by dividing the second
        source register by the data size defines the number of bits by which the
        first source register is right-shifted.

        This instruction is used by the alias LSR (register).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx  = '[01]'      # sf
        insn_rx += '0'
        insn_rx += '0'
        insn_rx += '11010110'
        insn_rx += '[01]{5}'   # Rm
        insn_rx += '0010'
        insn_rx += '01'        # op2
        insn_rx += '[01]{5}'   # Rn
        insn_rx += '[01]{5}'   # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op1.read()
        sft = reg_op2.read()

        result = LSR(reg, sft % res_op.size, res_op.size)
        res_op.write(result)

    @instruction
    def MADD(cpu, res_op, reg_op1, reg_op2, reg_op3):
        """
        MADD.

        Multiply-Add multiplies two register values, adds a third register
        value, and writes the result to the destination register.

        This instruction is used by the alias MUL.

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        :param reg_op3: source register.
        """
        assert res_op.type  is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG
        assert reg_op3.type is cs.arm64.ARM64_OP_REG

        insn_rx  = '[01]'     # sf
        insn_rx += '00'
        insn_rx += '11011'
        insn_rx += '000'
        insn_rx += '[01]{5}'  # Rm
        insn_rx += '0'        # o0
        insn_rx += '[01]{5}'  # Ra
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '[01]{5}'  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg1 = reg_op1.read()
        reg2 = reg_op2.read()
        reg3 = reg_op3.read()

        result = reg3 + (reg1 * reg2)
        res_op.write(UInt(result, res_op.size))

    @instruction
    def MOV(cpu, dst, src):
        """
        Combines MOV (to/from SP), MOV (inverted wide immediate), MOV (wide
        immediate), MOV (bitmask immediate), and MOV (register).

        :param dst: destination register.
        :param src: source register or immediate.
        """
        assert dst.type is cs.arm64.ARM64_OP_REG
        assert src.type in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]

        # Fake a register operand.
        if dst.size == 32:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_WZR)
        elif dst.size == 64:
            zr = Aarch64Operand.make_reg(cpu, cs.arm64.ARM64_REG_XZR)
        else:
            raise Aarch64InvalidInstruction

        opc = cpu.insn_bit_str[1:3]  # 'op S' for MOV (to/from SP)

        if src.type is cs.arm64.ARM64_OP_REG:
            # MOV (to/from SP).
            if opc == '00':
                # Fake an immediate operand.
                zero = Aarch64Operand.make_imm(cpu, 0)

                # The 'instruction' decorator advances PC, so call the original
                # method.
                cpu.ADD.__wrapped__(cpu, dst, src, zero)


            # MOV (register).
            elif opc == '01':
                # The 'instruction' decorator advances PC, so call the original
                # method.
                cpu.ORR.__wrapped__(cpu, dst, zr, src)

            else:
                raise Aarch64InvalidInstruction

        elif src.type is cs.arm64.ARM64_OP_IMM:
            # MOV (inverted wide immediate).
            if opc == '00':
                # The 'instruction' decorator advances PC, so call the original
                # method.
                cpu.MOVN.__wrapped__(cpu, dst, src)

            # MOV (wide immediate).
            elif opc == '10':
                # The 'instruction' decorator advances PC, so call the original
                # method.
                cpu.MOVZ.__wrapped__(cpu, dst, src)

            # MOV (bitmask immediate).
            elif opc == '01':
                # The 'instruction' decorator advances PC, so call the original
                # method.
                cpu.ORR.__wrapped__(cpu, dst, zr, src)

            else:
                raise Aarch64InvalidInstruction

        else:
            raise Aarch64InvalidInstruction

    @instruction
    def MOVK(cpu, res_op, imm_op):
        """
        MOVK.

        Move wide with keep moves an optionally-shifted 16-bit immediate value
        into a register, keeping other bits unchanged.

        :param res_op: destination register.
        :param imm_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx  = '[01]'      # sf
        insn_rx += '11'        # opc
        insn_rx += '100101'
        insn_rx += '[01]{2}'   # hw
        insn_rx += '[01]{16}'  # imm16
        insn_rx += '[01]{5}'   # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        res = res_op.read()
        imm = imm_op.op.imm
        sft = imm_op.op.shift.value

        if imm_op.is_shifted():
            assert imm_op.op.shift.type == cs.arm64.ARM64_SFT_LSL

        assert imm >= 0 and imm <= 65535
        assert (
            (res_op.size == 32 and sft in [0, 16]) or
            (res_op.size == 64 and sft in [0, 16, 32, 48])
        )

        imm = LSL(imm, sft, res_op.size)
        mask = LSL(65535, sft, res_op.size)
        result = (res & ~mask) | imm
        res_op.write(result)

    @instruction
    def MOVN(cpu, dst, src):
        """
        MOVN.

        Move wide with NOT moves the inverse of an optionally-shifted 16-bit
        immediate value to a register.

        This instruction is used by the alias MOV (inverted wide immediate).

        :param dst: destination register.
        :param src: immediate.
        """
        assert dst.type is cs.arm64.ARM64_OP_REG
        assert src.type is cs.arm64.ARM64_OP_IMM

        insn_rx  = '[01]'      # sf
        insn_rx += '00'        # opc
        insn_rx += '100101'
        insn_rx += '[01]{2}'   # hw
        insn_rx += '[01]{16}'  # imm16
        insn_rx += '[01]{5}'   # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        imm = src.op.imm
        sft = src.op.shift.value

        if src.is_shifted():
            assert src.op.shift.type == cs.arm64.ARM64_SFT_LSL

        assert imm >= 0 and imm <= 65535
        assert (
            (dst.size == 32 and sft in [0, 16]) or
            (dst.size == 64 and sft in [0, 16, 32, 48])
        )

        result = UInt(~LSL(imm, sft, dst.size), dst.size)
        dst.write(result)

    @instruction
    def MOVZ(cpu, dst, src):
        """
        MOVZ.

        Move wide with zero moves an optionally-shifted 16-bit immediate value
        to a register.

        This instruction is used by the alias MOV (wide immediate).

        :param dst: destination register.
        :param src: immediate.
        """
        assert dst.type is cs.arm64.ARM64_OP_REG
        assert src.type is cs.arm64.ARM64_OP_IMM

        insn_rx  = '[01]'      # sf
        insn_rx += '10'        # opc
        insn_rx += '100101'
        insn_rx += '[01]{2}'   # hw
        insn_rx += '[01]{16}'  # imm16
        insn_rx += '[01]{5}'   # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        imm = src.op.imm
        sft = src.op.shift.value

        if src.is_shifted():
            assert src.op.shift.type == cs.arm64.ARM64_SFT_LSL

        assert imm >= 0 and imm <= 65535
        assert (
            (dst.size == 32 and sft in [0, 16]) or
            (dst.size == 64 and sft in [0, 16, 32, 48])
        )

        result = UInt(LSL(imm, sft, dst.size), dst.size)
        dst.write(result)

    @instruction
    def MSUB(cpu, res_op, reg_op1, reg_op2, reg_op3):
        """
        MSUB.

        Multiply-Subtract multiplies two register values, subtracts the product
        from a third register value, and writes the result to the destination
        register.

        This instruction is used by the alias MNEG.

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        :param reg_op3: source register.
        """
        assert res_op.type  is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG
        assert reg_op3.type is cs.arm64.ARM64_OP_REG

        insn_rx  = '[01]'     # sf
        insn_rx += '00'
        insn_rx += '11011'
        insn_rx += '000'
        insn_rx += '[01]{5}'  # Rm
        insn_rx += '1'        # o0
        insn_rx += '[01]{5}'  # Ra
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '[01]{5}'  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg1 = reg_op1.read()
        reg2 = reg_op2.read()
        reg3 = reg_op3.read()

        result = reg3 - (reg1 * reg2)
        res_op.write(UInt(result, res_op.size))

    @instruction
    def MUL(cpu, res_op, reg_op1, reg_op2):
        """
        MUL.

        Multiply: Rd = Rn * Rm.

        This instruction is an alias of the MADD instruction.

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type  is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx  = '[01]'     # sf
        insn_rx += '00'
        insn_rx += '11011'
        insn_rx += '000'
        insn_rx += '[01]{5}'  # Rm
        insn_rx += '0'        # o0
        insn_rx += '1{5}'     # Ra
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '[01]{5}'  # Rd

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

    @instruction
    def NOP(cpu):
        """
        NOP.

        No Operation does nothing, other than advance the value of the program
        counter by 4.  This instruction can be used for instruction alignment
        purposes.
        """
        insn_rx  = '1101010100'
        insn_rx += '0'
        insn_rx += '00'
        insn_rx += '011'
        insn_rx += '0010'
        insn_rx += '0000'        # CRm
        insn_rx += '000'         # op2
        insn_rx += '11111'

        assert re.match(insn_rx, cpu.insn_bit_str)

    def _ORR_immediate(cpu, res_op, reg_op, imm_op):
        """
        ORR (immediate).

        Bitwise OR (immediate) performs a bitwise (inclusive) OR of a register
        value and an immediate value, and writes the result to the
        destination register.

        This instruction is used by the alias MOV (bitmask immediate).

        :param res_op: destination register.
        :param reg_op: source register.
        :param imm_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx  = '[01]'     # sf
        insn_rx += '01'       # opc
        insn_rx += '100100'
        insn_rx += '[01]'     # N
        insn_rx += '[01]{6}'  # immr
        insn_rx += '[01]{6}'  # imms
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '[01]{5}'  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        imm = imm_op.op.imm
        result = UInt(reg | imm, res_op.size)
        res_op.write(result)

    def _ORR_shifted_register(cpu, res_op, reg_op1, reg_op2):
        """
        ORR (shifted register).

        Bitwise OR (shifted register) performs a bitwise (inclusive) OR of a
        register value and an optionally-shifted register value, and writes the
        result to the destination register.

        This instruction is used by the alias MOV (register).

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type  is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx  = '[01]'     # sf
        insn_rx += '01'       # opc
        insn_rx += '01010'
        insn_rx += '[01]{2}'  # shift
        insn_rx += '0'        # N
        insn_rx += '[01]{5}'  # Rm
        insn_rx += '[01]{6}'  # imm6
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '[01]{5}'  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        cpu._shifted_register(
            res_op = res_op,
            reg_op1 = reg_op1,
            reg_op2 = reg_op2,
            action = lambda x, y: x | y,
            shifts = [
                cs.arm64.ARM64_SFT_LSL,
                cs.arm64.ARM64_SFT_LSR,
                cs.arm64.ARM64_SFT_ASR,
                cs.arm64.ARM64_SFT_ROR
            ])

    @instruction
    def ORR(cpu, res_op, op1, op2):
        """
        Combines ORR (immediate) and ORR (shifted register).

        :param res_op: destination register.
        :param op1: source register.
        :param op2: source register or immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert op1.type    is cs.arm64.ARM64_OP_REG
        assert op2.type    in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]

        if op2.type == cs.arm64.ARM64_OP_IMM:
            cpu._ORR_immediate(res_op, op1, op2)

        elif op2.type == cs.arm64.ARM64_OP_REG:
            cpu._ORR_shifted_register(res_op, op1, op2)

        else:
            raise Aarch64InvalidInstruction

    @instruction
    def RBIT(cpu, res_op, reg_op):
        """
        RBIT.

        Reverse Bits reverses the bit order in a register.

        :param res_op: destination register.
        :param reg_op: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx  = '[01]'     # sf
        insn_rx += '1'
        insn_rx += '0'
        insn_rx += '11010110'
        insn_rx += '0{5}'
        insn_rx += '0{4}'
        insn_rx += '0{2}'
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '[01]{5}'  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        size = reg_op.size

        result = 0
        for pos in range(size):
            bit = Operators.EXTRACT(reg, pos, 1)
            result <<= 1
            result |= bit

        res_op.write(result)

    @instruction
    def RET(cpu, reg_op=None):
        """
        RET.

        Return from subroutine branches unconditionally to an address in a
        register, with a hint that this is a subroutine return.

        :param reg_op: None or register.
        """
        assert not reg_op or reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx  = '1101011'
        insn_rx += '0'        # Z
        insn_rx += '0'
        insn_rx += '10'       # op
        insn_rx += '1{5}'
        insn_rx += '0{4}'
        insn_rx += '0'        # A
        insn_rx += '0'        # M
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '0{5}'     # Rm

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

        Reverse Bytes reverses the byte order in a register.

        This instruction is used by the pseudo-instruction REV64.

        :param res_op: destination register.
        :param reg_op: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx  = '[01]'     # sf
        insn_rx += '1'
        insn_rx += '0'
        insn_rx += '11010110'
        insn_rx += '0{5}'
        insn_rx += '0{4}'
        insn_rx += '1[01]'    # opc
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '[01]{5}'  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        size = reg_op.size

        result = 0
        step = 8
        for pos in range(0, size, step):
            byte = Operators.EXTRACT(reg, pos, step)
            result <<= step
            result |= byte

        res_op.write(result)

    def _STR_immediate(cpu, reg_op, mem_op, mimm_op):
        """
        STR (immediate).

        Store Register (immediate) stores a word or a doubleword from a register
        to memory.  The address that is used for the store is calculated from a
        base register and an immediate offset.

        :param reg_op: source register.
        :param mem_op: memory.
        :param mimm_op: None or immediate.
        """
        cpu._ldr_str_immediate(reg_op, mem_op, mimm_op, ldr=False)

    def _STR_register(cpu, reg_op, mem_op):
        """
        STR (register).

        Store Register (register) calculates an address from a base register
        value and an offset register value, and stores a 32-bit word or a 64-bit
        doubleword to the calculated address, from a register.

        The instruction uses an offset addressing mode, that calculates the
        address used for the memory access from a base register value and an
        offset register value.  The offset can be optionally shifted and
        extended.

        :param reg_op: source register.
        :param mem_op: memory.
        """
        cpu._ldr_str_register(reg_op, mem_op, ldr=False)

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

    @instruction
    def STUR(cpu, reg_op, mem_op):
        """
        STUR.

        Store Register (unscaled) calculates an address from a base register
        value and an immediate offset, and stores a 32-bit word or a 64-bit
        doubleword to the calculated address, from a register.

        :param reg_op: source register.
        :param mem_op: memory.
        """
        cpu._ldur_stur(reg_op, mem_op, ldur=False)

    @instruction
    def SVC(cpu, imm_op):
        """
        SVC.

        Supervisor Call causes an exception to be taken to EL1.  On executing an
        SVC instruction, the PE records the exception as a Supervisor Call
        exception in ESR_ELx, using the EC value 0x15, and the value of the
        immediate argument.

        :param imm_op: immediate.
        """
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        imm = imm_op.op.imm
        assert imm >= 0 and imm <= 65535

        if imm != 0:
            raise InstructionNotImplementedError(f'SVC #{imm}')
        raise Interruption(imm)

    @instruction
    def TBNZ(cpu, reg_op, imm_op, lab_op):
        """
        TBNZ.

        Test bit and Branch if Nonzero compares the value of a bit in a
        general-purpose register with zero, and conditionally branches to a
        label at a PC-relative offset if the comparison is not equal.  It
        provides a hint that this is not a subroutine call or return.  This
        instruction does not affect condition flags.

        :param reg_op: register.
        :param imm_op: immediate.
        :param lab_op: immediate.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM
        assert lab_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx  = '[01]'      # b5
        insn_rx += '011011'
        insn_rx += '1'         # op
        insn_rx += '[01]{5}'   # b40
        insn_rx += '[01]{14}'  # imm14
        insn_rx += '[01]{5}'   # Rt

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        imm = imm_op.op.imm
        lab = lab_op.op.imm

        assert imm in range(reg_op.size)

        if Operators.EXTRACT(reg, imm, 1) != 0:
            cpu.PC = lab

    @instruction
    def TBZ(cpu, reg_op, imm_op, lab_op):
        """
        TBZ.

        Test bit and Branch if Zero compares the value of a test bit with zero,
        and conditionally branches to a label at a PC-relative offset if the
        comparison is equal.  It provides a hint that this is not a subroutine
        call or return.  This instruction does not affect condition flags.

        :param reg_op: register.
        :param imm_op: immediate.
        :param lab_op: immediate.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM
        assert lab_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx  = '[01]'      # b5
        insn_rx += '011011'
        insn_rx += '0'         # op
        insn_rx += '[01]{5}'   # b40
        insn_rx += '[01]{14}'  # imm14
        insn_rx += '[01]{5}'   # Rt

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg = reg_op.read()
        imm = imm_op.op.imm
        lab = lab_op.op.imm

        assert imm in range(reg_op.size)

        if Operators.EXTRACT(reg, imm, 1) == 0:
            cpu.PC = lab

    def _TST_immediate(cpu, reg_op, imm_op):
        """
        TST (immediate).

        Test bits (immediate), setting the condition flags and discarding the
        result: Rn AND imm.

        This instruction is an alias of the ANDS (immediate) instruction.

        :param reg_op: source register.
        :param imm_op: immediate.
        """
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert imm_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx  = '[01]'     # sf
        insn_rx += '11'       # opc
        insn_rx += '100100'
        insn_rx += '[01]'     # N
        insn_rx += '[01]{6}'  # immr
        insn_rx += '[01]{6}'  # imms
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '1{5}'     # Rd

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

        Test (shifted register) performs a bitwise AND operation on a register
        value and an optionally-shifted register value.  It updates the
        condition flags based on the result, and discards the result.

        This instruction is an alias of the ANDS (shifted register) instruction.

        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx  = '[01]'     # sf
        insn_rx += '11'       # opc
        insn_rx += '01010'
        insn_rx += '[01]{2}'  # shift
        insn_rx += '0'        # N
        insn_rx += '[01]{5}'  # Rm
        insn_rx += '[01]{6}'  # imm6
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '1{5}'     # Rd

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
    def TST(cpu, op1, op2):
        """
        Combines TST (immediate) and TST (shifted register).

        :param op1: source register.
        :param op2: source register or immediate.
        """
        assert op1.type is cs.arm64.ARM64_OP_REG
        assert op2.type in [cs.arm64.ARM64_OP_REG, cs.arm64.ARM64_OP_IMM]

        if op2.type == cs.arm64.ARM64_OP_REG:
            cpu._TST_shifted_register(op1, op2)

        elif op2.type == cs.arm64.ARM64_OP_IMM:
            cpu._TST_immediate(op1, op2)

        else:
            raise Aarch64InvalidInstruction

    @instruction
    def UBFIZ(cpu, res_op, reg_op, lsb_op, width_op):
        """
        UBFIZ.

        Unsigned Bitfield Insert in Zeros copies a bitfield of <width> bits from
        the least significant bits of the source register to bit position <lsb>
        of the destination register, setting the destination bits above and
        below the bitfield to zero.

        This instruction is an alias of the UBFM instruction.

        :param res_op: destination register.
        :param reg_op: source register.
        :param lsb_op: immediate.
        :param width_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert lsb_op.type is cs.arm64.ARM64_OP_IMM
        assert width_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx  = '[01]'     # sf
        insn_rx += '10'       # opc
        insn_rx += '100110'
        insn_rx += '[01]'     # N
        insn_rx += '[01]{6}'  # immr
        insn_rx += '[01]{6}'  # imms
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '[01]{5}'  # Rd

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

        Unigned Bitfield Move is usually accessed via one of its aliases, which
        are always preferred for disassembly.

        If <imms> is greater than or equal to <immr>, this copies a bitfield of
        (<imms>-<immr>+1) bits starting from bit position <immr> in the source
        register to the least significant bits of the destination register.

        If <imms> is less than <immr>, this copies a bitfield of (<imms>+1) bits
        from the least significant bits of the source register to bit position
        (regsize-<immr>) of the destination register, where regsize is the
        destination register size of 32 or 64 bits.

        In both cases the destination bits below and above the bitfield are set
        to zero.

        This instruction is used by the aliases LSL (immediate), LSR
        (immediate), UBFIZ, UBFX, UXTB, and UXTH.

        :param res_op: destination register.
        :param reg_op: source register.
        :param immr_op: immediate.
        :param imms_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert immr_op.type is cs.arm64.ARM64_OP_IMM
        assert imms_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx  = '[01]'     # sf
        insn_rx += '10'       # opc
        insn_rx += '100110'
        insn_rx += '[01]'     # N
        insn_rx += '[01]{6}'  # immr
        insn_rx += '[01]{6}'  # imms
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '[01]{5}'  # Rd

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

        Unsigned Bitfield Extract copies a bitfield of <width> bits starting
        from bit position <lsb> in the source register to the least significant
        bits of the destination register, and sets destination bits above the
        bitfield to zero.

        This instruction is an alias of the UBFM instruction.

        :param res_op: destination register.
        :param reg_op: source register.
        :param lsb_op: immediate.
        :param width_op: immediate.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG
        assert lsb_op.type is cs.arm64.ARM64_OP_IMM
        assert width_op.type is cs.arm64.ARM64_OP_IMM

        insn_rx  = '[01]'     # sf
        insn_rx += '10'       # opc
        insn_rx += '100110'
        insn_rx += '[01]'     # N
        insn_rx += '[01]{6}'  # immr
        insn_rx += '[01]{6}'  # imms
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '[01]{5}'  # Rd

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

        Unsigned Divide divides an unsigned integer register value by another
        unsigned integer register value, and writes the result to the
        destination register.  The condition flags are not affected.

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type  is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx  = '[01]'      # sf
        insn_rx += '0'
        insn_rx += '0'
        insn_rx += '11010110'
        insn_rx += '[01]{5}'   # Rm
        insn_rx += '00001'
        insn_rx += '0'         # o1
        insn_rx += '[01]{5}'   # Rn
        insn_rx += '[01]{5}'   # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg1 = UInt(reg_op1.read(), reg_op1.size)
        reg2 = UInt(reg_op2.read(), reg_op2.size)

        if reg2 == 0:
            result = 0
        else:
            result = int(Decimal(reg1) / Decimal(reg2))  # round toward zero

        res_op.write(result)

    @instruction
    def UMULH(cpu, res_op, reg_op1, reg_op2):
        """
        UMULH.

        Unsigned Multiply High multiplies two 64-bit register values, and writes
        bits[127:64] of the 128-bit result to the 64-bit destination register.

        :param res_op: destination register.
        :param reg_op1: source register.
        :param reg_op2: source register.
        """
        assert res_op.type  is cs.arm64.ARM64_OP_REG
        assert reg_op1.type is cs.arm64.ARM64_OP_REG
        assert reg_op2.type is cs.arm64.ARM64_OP_REG

        insn_rx  = '1'
        insn_rx += '00'
        insn_rx += '11011'
        insn_rx += '1'        # U
        insn_rx += '10'
        insn_rx += '[01]{5}'  # Rm
        insn_rx += '0'
        insn_rx += '1{5}'     # Ra
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '[01]{5}'  # Rd

        assert re.match(insn_rx, cpu.insn_bit_str)

        reg1 = UInt(reg_op1.read(), reg_op1.size)
        reg2 = UInt(reg_op2.read(), reg_op2.size)

        result = Operators.EXTRACT(reg1 * reg2, 64, 128)
        res_op.write(result)

    @instruction
    def UXTB(cpu, res_op, reg_op):
        """
        UXTB.

        Unsigned Extend Byte extracts an 8-bit value from a register,
        zero-extends it to the size of the register, and writes the result to
        the destination register.

        This instruction is an alias of the UBFM instruction.

        :param res_op: destination register.
        :param reg_op: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx  = '0'        # sf
        insn_rx += '10'       # opc
        insn_rx += '100110'
        insn_rx += '0'        # N
        insn_rx += '0{6}'     # immr
        insn_rx += '000111'   # imms
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '[01]{5}'  # Rd

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

        Unsigned Extend Halfword extracts a 16-bit value from a register,
        zero-extends it to the size of the register, and writes the result to
        the destination register.

        This instruction is an alias of the UBFM instruction.

        :param res_op: destination register.
        :param reg_op: source register.
        """
        assert res_op.type is cs.arm64.ARM64_OP_REG
        assert reg_op.type is cs.arm64.ARM64_OP_REG

        insn_rx  = '0'        # sf
        insn_rx += '10'       # opc
        insn_rx += '100110'
        insn_rx += '0'        # N
        insn_rx += '0{6}'     # immr
        insn_rx += '001111'   # imms
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '[01]{5}'  # Rd

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


# XXX: Update/rewrite this.
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
