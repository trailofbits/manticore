import warnings

import capstone as cs
import collections
import re
import struct

from .abstractcpu import (
    Cpu, CpuException, RegisterFile, Abi, SyscallAbi, Operand, instruction
)
from .arm import HighBit, Armv7Operand
from .bitwise import SInt, UInt, ASR, LSL, LSR, ROR
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
        name = insn.insn_name().upper()
        # XXX: Check if a Capstone bug that incorrectly labels some instructions
        # is still there.
        assert name.lower() == insn.mnemonic

        name = OP_NAME_MAP.get(name, name)
        ops = insn.operands

        # Make sure MOV (bitmask immediate) and MOV (register) go through 'MOV'.
        if (name == 'ORR' and len(ops) == 3 and
            ops[1].type == cs.arm64.ARM64_OP_REG and
            ops[1].reg in ['WZR', 'XZR'] and
            not ops[2].is_shifted()
           ):
            name = 'MOV'
            del ops[1]

        return name

    @property
    def insn_bit_str(self):
        # XXX: Hardcoded endianness and instruction size.
        insn = struct.unpack("<I", self.instruction.bytes)[0]
        return f'{insn:032b}'

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

    def _LDR_immediate(cpu, dst, src, rest):
        """
        LDR (immediate).

        Load Register (immediate) loads a word or doubleword from memory and
        writes it to a register.  The address that is used for the load is
        calculated from a base register and an immediate offset.

        :param dst: destination register.
        :param src: memory (source register and immediate).
        :param rest: None or immediate.
        """
        assert dst.type is cs.arm64.ARM64_OP_REG
        assert src.type is cs.arm64.ARM64_OP_MEM
        assert not rest or rest.type is cs.arm64.ARM64_OP_IMM

        post_index_rx  = '1[01]'    # size
        post_index_rx += '111'
        post_index_rx += '0'
        post_index_rx += '00'
        post_index_rx += '01'       # opc
        post_index_rx += '0'
        post_index_rx += '[01]{9}'  # imm9
        post_index_rx += '01'
        post_index_rx += '[01]{5}'  # Rn
        post_index_rx += '[01]{5}'  # Rt

        pre_index_rx  = '1[01]'     # size
        pre_index_rx += '111'
        pre_index_rx += '0'
        pre_index_rx += '00'
        pre_index_rx += '01'        # opc
        pre_index_rx += '0'
        pre_index_rx += '[01]{9}'   # imm9
        pre_index_rx += '11'
        pre_index_rx += '[01]{5}'   # Rn
        pre_index_rx += '[01]{5}'   # Rt

        unsigned_offset_rx  = '1[01]'     # size
        unsigned_offset_rx += '111'
        unsigned_offset_rx += '0'
        unsigned_offset_rx += '01'
        unsigned_offset_rx += '01'        # opc
        unsigned_offset_rx += '[01]{12}'  # imm12
        unsigned_offset_rx += '[01]{5}'   # Rn
        unsigned_offset_rx += '[01]{5}'   # Rt

        assert (
            re.match(post_index_rx, cpu.insn_bit_str) or
            re.match(pre_index_rx, cpu.insn_bit_str) or
            re.match(unsigned_offset_rx, cpu.insn_bit_str)
        )

        base = cpu.regfile.read(src.mem.base)
        imm = src.mem.disp

        if rest:  # post-indexed
            wback = rest.op.imm
        else:
            wback = imm  # use it for writeback if applicable

        result = cpu.read_int(base + imm, dst.size)
        dst.write(result)

        if cpu.instruction.writeback:
            cpu.regfile.write(src.mem.base, base + wback)

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

    def _LDR_register(cpu, dst, src):
        """
        LDR (register).

        Load Register (register) calculates an address from a base register
        value and an offset register value, loads a word from memory, and writes
        it to a register.  The offset register value can optionally be shifted
        and extended.

        :param dst: destination register.
        :param src: memory: register offset or extended register offset.
        """
        assert dst.type is cs.arm64.ARM64_OP_REG
        assert src.type is cs.arm64.ARM64_OP_MEM

        insn_rx  = '1[01]'    # size
        insn_rx += '111'
        insn_rx += '0'
        insn_rx += '00'
        insn_rx += '01'       # opc
        insn_rx += '1'
        insn_rx += '[01]{5}'  # Rm
        insn_rx += '[01]{3}'  # option
        insn_rx += '[01]'     # S
        insn_rx += '10'
        insn_rx += '[01]{5}'  # Rn
        insn_rx += '[01]{5}'  # Rt

        assert re.match(insn_rx, cpu.insn_bit_str)

        base = cpu.regfile.read(src.mem.base)
        index = cpu.regfile.read(src.mem.index)
        index_size = cpu.regfile.size(src.mem.index)

        if src.is_extended():
            ext = src.op.ext

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

        if src.is_shifted():
            shift = src.op.shift
            assert shift.type == cs.arm64.ARM64_SFT_LSL
            index = LSL(index, shift.value, index_size)

        base = UInt(base, cpu.address_bit_size)
        index = SInt(index, cpu.address_bit_size)
        result = cpu.read_int(base + index, dst.size)
        dst.write(result)

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
        zr = cs.arm64.Arm64Op()

        if dst.size == 32:
            zr.value.reg = cs.arm64.ARM64_REG_WZR
        elif dst.size == 64:
            zr.value.reg = cs.arm64.ARM64_REG_XZR
        else:
            raise Aarch64InvalidInstruction

        zr.type = cs.arm64.ARM64_OP_REG
        zr = Aarch64Operand(cpu, zr)

        opc = cpu.insn_bit_str[1:3]  # 'op S' for MOV (to/from SP)

        if src.type is cs.arm64.ARM64_OP_REG:
            # MOV (to/from SP).
            if opc == '00':
                # Fake an immediate operand.
                zero = cs.arm64.Arm64Op()
                zero.value.imm = 0
                zero.type = cs.arm64.ARM64_OP_IMM
                zero = Aarch64Operand(cpu, zero)

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
