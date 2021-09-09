from copy import copy
from functools import wraps
from inspect import signature as inspect_signature
import logging
import struct

import capstone as cs
import operator as ops

from .abstractcpu import Abi, Cpu, Interruption, Operand, RegisterFile, SyscallAbi
from .abstractcpu import instruction as abstract_instruction
from .bitwise import *
from .register import Register
from ...core.smtlib import Operators, BitVecConstant, issymbolic

from typing import NamedTuple

logger = logging.getLogger(__name__)

# map different instructions to a single impl here
OP_NAME_MAP = {"MOVW": "MOV"}


def HighBit(n):
    return Bit(n, 31)


ARMV7_CPU_ADDRESS_BIT_SIZE = 32


def instruction(instruction_body=None, *, can_take_denormalized_mod_imm: bool = False):
    """
    This decorator is used to annotate Armv7Cpu methods as
    instruction-implementing methods.

    This centralizes some common ARM-specific logic about CPU flags in one place.

    Additionally, this optionally adds /modified immediate normalization/ logic
    to the wrapped method.

    This decorator works both as `@instruction` and as
    `@instruction(can_take_denormalized_mod_imm=True)`.


    What is this normalization logic?

    First, it helps to understand how ARM encodes immediate constants.
    In encoded ARM instructions, immediate constant values are encoded as an
    8-bit unsigned number and a 4-bit rotation value; you can read about the
    details in the ARM Architecture Reference Manual, ARMv7-A and ARMv7-R
    edition, section A5.2.3, "Data-processing (immediate)".

    Second, it turns out that the Capstone disassembler we use will sometimes
    disassemble an ARM immediate constant value into /two/ immediate operand
    values, explicitly representing the 8-bit unsigned number and two times the
    4-bit shift.  In particular, it seems that Capstone uses this explicit
    representation when the modified immediate value is encoded in a
    non-canonical form.  A blog post has some more explanation around this:

        https://alisdair.mcdiarmid.org/arm-immediate-value-encoding/

    So, finally, the /modified immediate normalization/ logic that this
    decorator adds converts an explicitly-represented unsigned number and
    rotation into a single immediate operand-like value (`_ImmediatePseudoOperand`)
    that has the appropriate integer value, so that the actual implementation
    of an ARM instruction here can expect only normalized immediates, and not
    have to concern itself with this quirk of Capstone.
    """

    def decorator(body):
        if can_take_denormalized_mod_imm:
            # Need to possibly normalize a modified immediate argument that's
            # been explicitly split by Capstone into (number, rotation)
            # components.

            body_sig = inspect_signature(body)
            # subtract 1 to account for the first parameter (`cpu`), present in
            # all instruction methods.
            num_body_params = len(body_sig.parameters) - 1
            assert num_body_params > 0

            def normalize_mod_imm_arg(args):
                if len(args) == num_body_params + 1:
                    # We got 1 more argument than the wrapped function expects;
                    # this is the case of a modified immediate represented
                    # explicitly as 2 immediate operands.
                    # Normalize the two into one!
                    args = list(args)
                    rot = args.pop()
                    assert rot.type == "immediate"
                    num = args.pop()
                    assert num.type == "immediate"
                    imm = ROR(num.imm, rot.imm, ARMV7_CPU_ADDRESS_BIT_SIZE)
                    args.append(_ImmediatePseudoOperand(imm))
                return args

        else:
            # No normalization of a modified immediate required; return what's given.
            def normalize_mod_imm_arg(args):
                return args

        @wraps(body)
        def instruction_implementation(cpu, *args, **kwargs):
            should_execute = cpu.should_execute_conditional()

            if cpu._at_symbolic_conditional == cpu.instruction.address:
                cpu._at_symbolic_conditional = None
                should_execute = True
            else:
                if issymbolic(should_execute):
                    # Let's remember next time we get here we should not do this again
                    cpu._at_symbolic_conditional = cpu.instruction.address
                    i_size = cpu.instruction.size
                    cpu.PC = Operators.ITEBV(
                        cpu.address_bit_size, should_execute, cpu.PC - i_size, cpu.PC
                    )
                    return

            if should_execute:
                ret = body(cpu, *normalize_mod_imm_arg(args), **kwargs)
            else:
                ret = None

            if cpu.should_commit_flags():
                cpu.commit_flags()

            return ret

        return abstract_instruction(instruction_implementation)

    # Here's where we support using this decorator both like
    # `@instruction` and like `@instruction(can_take_denormalized_mod_imm=True)`.
    # See https://stackoverflow.com/questions/3888158/making-decorators-with-optional-arguments
    # for some decorator-fu.
    if instruction_body is not None:
        return decorator(instruction_body)
    else:
        return decorator


class _ImmediatePseudoOperand(NamedTuple):
    """
    This is a hacky class that is used to represent an object that looks close
    enough to an Armv7Operand to be used in the places where immediate operands
    are used.

    See the `instruction` decorator for more detail.
    """

    imm: int

    def read(self, with_carry: bool = False):
        if with_carry:
            return self.imm, 0
        else:
            return self.imm


_TYPE_MAP = {
    cs.arm.ARM_OP_REG: "register",
    cs.arm.ARM_OP_MEM: "memory",
    cs.arm.ARM_OP_IMM: "immediate",
    cs.arm.ARM_OP_PIMM: "coprocessor",
    cs.arm.ARM_OP_CIMM: "immediate",
}


class Armv7Operand(Operand):
    def __init__(self, cpu, op, **kwargs):
        super().__init__(cpu, op, **kwargs)
        self.__type = _TYPE_MAP[self.op.type]

    @property
    def type(self):
        """
        Corresponds to capstone's `operand.type` (cs.arm.ARM_OP_*).
        """
        return self.__type

    @property
    def size(self):
        assert self.__type == "register"
        if cs.arm.ARM_REG_D0 <= self.op.reg <= cs.arm.ARM_REG_D31:
            return 64
        else:
            # FIXME check other types of operand sizes
            return 32

    def read(self, nbits=None, with_carry=False):
        carry = self.cpu.regfile.read("APSR_C")
        if self.__type == "register":
            value = self.cpu.regfile.read(self.reg)
            # PC in this case has to be set to the instruction after next. PC at this point
            # is already pointing to next instruction; we bump it one more.
            if self.reg in ("PC", "R15"):
                value += self.cpu.instruction.size
            if self.is_shifted():
                shift = self.op.shift
                # XXX: This is unnecessary repetition.
                if shift.type in range(cs.arm.ARM_SFT_ASR_REG, cs.arm.ARM_SFT_RRX_REG + 1):
                    if self.cpu.mode == cs.CS_MODE_THUMB:
                        amount = shift.value.read()
                    else:
                        src_reg = self.cpu.instruction.reg_name(shift.value).upper()
                        amount = self.cpu.regfile.read(src_reg)
                else:
                    amount = shift.value
                value, carry = self.cpu._shift(value, shift.type, amount, carry)
            if self.op.subtracted:
                value = -value
            if with_carry:
                return value, carry
            return value
        elif self.__type == "immediate":
            imm = self.op.imm
            if self.op.subtracted:
                imm = -imm
            if with_carry:
                return imm, self._get_expand_imm_carry(carry)
            return imm
        elif self.__type == "coprocessor":
            imm = self.op.imm
            return imm
        elif self.__type == "memory":
            val = self.cpu.read_int(self.address(), nbits)
            if with_carry:
                return val, carry
            return val
        else:
            raise NotImplementedError("readOperand unknown type", self.op.type)

    def write(self, value, nbits=None):
        if self.__type == "register":
            self.cpu.regfile.write(self.reg, value)
        elif self.__type == "memory":
            raise NotImplementedError("need to impl arm store mem")
        else:
            raise NotImplementedError("writeOperand unknown type", self.op.type)

    def writeback(self, value):
        if self.__type == "register":
            self.write(value)
        elif self.__type == "memory":
            self.cpu.regfile.write(self.mem.base, value)
        else:
            raise NotImplementedError("writeback Operand unknown type", self.op.type)

    def is_shifted(self):
        """
        In ARM some of the operands may have an additional metadata which means they can be shifted
        with either a register or immediate value.

        See:
        * https://github.com/aquynh/capstone/blob/fdebc371ba0568acde007e08dad2cc3c9333e3fa/include/arm.h#L22-L34

        * 11.5 Syntax of Operand2 as a register with optional shift
            http://infocenter.arm.com/help/index.jsp?topic=/com.arm.doc.dui0473m/dom1361289852638.html

        :return: True if operand is shifted, otherwise False.
        """
        return self.op.shift.type != cs.arm.ARM_SFT_INVALID

    def address(self):
        assert self.__type == "memory"
        addr = self.get_mem_base_addr() + self.get_mem_offset()
        return addr & Mask(self.cpu.address_bit_size)

    def get_mem_offset(self):
        assert self.__type == "memory"

        off = 0
        if self.mem.index is not None:
            idx = self.mem.scale * self.cpu.regfile.read(self.mem.index)
            carry = self.cpu.regfile.read("APSR_C")
            if self.is_shifted():
                shift = self.op.shift
                idx, carry = self.cpu._shift(idx, shift.type, shift.value, carry)
            off = -idx if self.op.subtracted else idx
        else:
            off = self.mem.disp
        return off

    def get_mem_base_addr(self):
        assert self.__type == "memory"

        base = self.cpu.regfile.read(self.mem.base)

        # PC relative addressing is fun in ARM:
        # In ARM mode, the spec defines the base value as current insn + 8
        # In thumb mode, the spec defines the base value as ALIGN(current insn address) + 4,
        # where ALIGN(current insn address) => <current insn address> & 0xFFFFFFFC
        #
        # Regardless of mode, our implementation of read(PC) will return the address
        # of the instruction following the next instruction.
        if self.mem.base in ("PC", "R15"):
            if self.cpu.mode == cs.CS_MODE_ARM:
                logger.debug(f"ARM mode PC relative addressing: PC + offset: 0x{base:x} + 0x{4:x}")
                return base + 4
            else:
                # base currently has the value PC + len(current_instruction)
                # we need (PC & 0xFFFFFFFC) + 4
                # thus:
                new_base = (base - self.cpu.instruction.size) & 0xFFFFFFFC
                logger.debug(
                    f"THUMB mode PC relative addressing: ALIGN(PC) + offset => 0x{new_base:x} + 0x{4:x}"
                )
                return new_base + 4
        else:
            return base

    def _get_expand_imm_carry(self, carryIn):
        """Manually compute the carry bit produced by expanding an immediate operand (see ARMExpandImm_C)"""
        insn = struct.unpack("<I", self.cpu.instruction.bytes)[0]
        unrotated = insn & Mask(8)
        shift = Operators.EXTRACT(insn, 8, 4)
        _, carry = self.cpu._shift(unrotated, cs.arm.ARM_SFT_ROR, 2 * shift, carryIn)
        return carry


class Armv7RegisterFile(RegisterFile):
    def __init__(self):
        """
        ARM Register file abstraction. GPRs use ints for read/write. APSR
        flags allow writes of bool/{1, 0} but always read bools.
        """
        super().__init__(
            {
                "SB": "R9",
                "SL": "R10",
                "FP": "R11",
                "IP": "R12",
                "STACK": "R13",
                "SP": "R13",
                "LR": "R14",
                "PC": "R15",
            }
        )
        # 32 bit registers
        for reg_name in (
            "R0",
            "R1",
            "R2",
            "R3",
            "R4",
            "R5",
            "R6",
            "R7",
            "R8",
            "R9",
            "R10",
            "R11",
            "R12",
            "R13",
            "R14",
            "R15",
        ):
            self._registers[reg_name] = Register(32)
        # 64 bit registers
        for reg_name in (
            "D0",
            "D1",
            "D2",
            "D3",
            "D4",
            "D5",
            "D6",
            "D7",
            "D8",
            "D9",
            "D10",
            "D11",
            "D12",
            "D13",
            "D14",
            "D15",
            "D16",
            "D17",
            "D18",
            "D19",
            "D20",
            "D21",
            "D22",
            "D23",
            "D24",
            "D25",
            "D26",
            "D27",
            "D28",
            "D29",
            "D30",
            "D31",
        ):
            self._registers[reg_name] = Register(64)
        # Flags
        self._registers["APSR_N"] = Register(1)
        self._registers["APSR_Z"] = Register(1)
        self._registers["APSR_C"] = Register(1)
        self._registers["APSR_V"] = Register(1)
        self._registers["APSR_GE"] = Register(4)

        # MMU Coprocessor  -- to support MCR/MRC for TLS
        self._registers["P15_C13"] = Register(32)

    def _read_APSR(self):
        def make_apsr_flag(flag_expr, offset):
            """Helper for constructing an expression for the APSR register"""
            return Operators.ITEBV(
                32, flag_expr, BitVecConstant(32, 1 << offset), BitVecConstant(32, 0)
            )

        apsr = 0
        N = self.read("APSR_N")
        Z = self.read("APSR_Z")
        C = self.read("APSR_C")
        V = self.read("APSR_V")

        if any(issymbolic(x) for x in [N, Z, C, V]):
            apsr = (
                make_apsr_flag(N, 31)
                | make_apsr_flag(Z, 30)
                | make_apsr_flag(C, 29)
                | make_apsr_flag(V, 28)
            )
        else:
            if N:
                apsr |= 1 << 31
            if Z:
                apsr |= 1 << 30
            if C:
                apsr |= 1 << 29
            if V:
                apsr |= 1 << 28
        return apsr

    def _write_APSR(self, apsr):
        """Auxiliary function - Writes flags from a full APSR (only 4 msb used)"""
        V = Operators.EXTRACT(apsr, 28, 1)
        C = Operators.EXTRACT(apsr, 29, 1)
        Z = Operators.EXTRACT(apsr, 30, 1)
        N = Operators.EXTRACT(apsr, 31, 1)

        self.write("APSR_V", V)
        self.write("APSR_C", C)
        self.write("APSR_Z", Z)
        self.write("APSR_N", N)

    def read(self, register):
        assert register in self
        if register == "APSR":
            return self._read_APSR()
        register = self._alias(register)
        return self._registers[register].read()

    def write(self, register, value):
        assert register in self
        if register == "APSR":
            return self._write_APSR(value)
        register = self._alias(register)
        self._registers[register].write(value)

    @property
    def all_registers(self):
        return super().all_registers + (
            "R0",
            "R1",
            "R2",
            "R3",
            "R4",
            "R5",
            "R6",
            "R7",
            "R8",
            "R9",
            "R10",
            "R11",
            "R12",
            "R13",
            "R14",
            "R15",
            "D0",
            "D1",
            "D2",
            "D3",
            "D4",
            "D5",
            "D6",
            "D7",
            "D8",
            "D9",
            "D10",
            "D11",
            "D12",
            "D13",
            "D14",
            "D15",
            "D16",
            "D17",
            "D18",
            "D19",
            "D20",
            "D21",
            "D22",
            "D23",
            "D24",
            "D25",
            "D26",
            "D27",
            "D28",
            "D29",
            "D30",
            "D31",
            "APSR",
            "APSR_N",
            "APSR_Z",
            "APSR_C",
            "APSR_V",
            "APSR_GE",
            "P15_C13",
        )

    @property
    def canonical_registers(self):
        return (
            "R0",
            "R1",
            "R2",
            "R3",
            "R4",
            "R5",
            "R6",
            "R7",
            "R8",
            "R9",
            "R10",
            "R11",
            "R12",
            "R13",
            "R14",
            "R15",
            "APSR",
        )

    def __copy__(self):
        cls = self.__class__
        result = cls.__new__(cls)
        result.__dict__.update(self.__dict__)
        result._registers = {k: copy(v) for k, v in self._registers.items()}
        return result


class Armv7LinuxSyscallAbi(SyscallAbi):
    """ARMv7 Linux system call ABI"""

    # EABI standards:
    #  syscall # is in R7
    #  arguments are passed in R0-R6
    #  retval is passed in R0
    def syscall_number(self):
        return self._cpu.R7

    def get_arguments(self):
        for i in range(6):
            yield f"R{i}"

    def get_result_reg(self):
        return "R0"

    def write_result(self, result):
        self._cpu.R0 = result


class Armv7CdeclAbi(Abi):
    """ARMv7 Cdecl function call ABI"""

    def get_arguments(self):
        # First four passed via R0-R3, then on stack
        for reg in ("R0", "R1", "R2", "R3"):
            yield reg

        for address in self.values_from(self._cpu.STACK):
            yield address

    def write_result(self, result):
        self._cpu.R0 = result

    def ret(self):
        self._cpu.PC = self._cpu.LR


class Armv7Cpu(Cpu):
    """
    Cpu specialization handling the ARMv7 architecture.

    Note: In this implementation, PC contains address of current
    instruction + 4. However, official spec defines PC to be address of
    current instruction + 8 (section A2.3).
    """

    address_bit_size = ARMV7_CPU_ADDRESS_BIT_SIZE
    max_instr_width = 4
    machine = "armv7"
    arch = cs.CS_ARCH_ARM
    # 'mode' is usually defined here as a class member, but it can change, so
    # it's an instance property.

    def __init__(self, memory):
        self._it_conditional = list()
        self._last_flags = {"C": 0, "V": 0, "N": 0, "Z": 0, "GE": 0}
        self._at_symbolic_conditional = None
        self._mode = cs.CS_MODE_ARM
        super().__init__(Armv7RegisterFile(), memory)

    def __getstate__(self):
        state = super().__getstate__()
        state["_last_flags"] = self._last_flags
        state["at_symbolic_conditional"] = self._at_symbolic_conditional
        state["_it_conditional"] = self._it_conditional
        state["_mode"] = self._mode
        return state

    def __setstate__(self, state):
        self._last_flags = state["_last_flags"]
        self._at_symbolic_conditional = state["at_symbolic_conditional"]
        self._it_conditional = state["_it_conditional"]
        self._mode = state["_mode"]
        super().__setstate__(state)

    @property
    def mode(self):
        return self._mode

    @mode.setter
    def mode(self, new_mode):
        assert new_mode in (cs.CS_MODE_ARM, cs.CS_MODE_THUMB)

        if self._mode != new_mode:
            logger.debug(f'swapping into {"ARM" if new_mode == cs.CS_MODE_ARM else "THUMB"} mode')

        self._mode = new_mode
        self.disasm.disasm.mode = new_mode

    def _set_mode_by_val(self, val):
        new_mode = Operators.ITEBV(
            self.address_bit_size, (val & 0x1) == 0x1, cs.CS_MODE_THUMB, cs.CS_MODE_ARM
        )

        if issymbolic(new_mode):
            from ..state import Concretize

            def set_concrete_mode(state, value):
                state.cpu.mode = value

            raise Concretize(
                "Concretizing ARMv7 mode", expression=new_mode, setstate=set_concrete_mode
            )

        self.mode = new_mode

    def _swap_mode(self):
        """Toggle between ARM and Thumb mode"""
        assert self.mode in (cs.CS_MODE_ARM, cs.CS_MODE_THUMB)
        if self.mode == cs.CS_MODE_ARM:
            self.mode = cs.CS_MODE_THUMB
        else:
            self.mode = cs.CS_MODE_ARM

    # Flags that are the result of arithmetic instructions. Unconditionally
    # set, but conditionally committed.
    #
    # Register file has the actual CPU flags
    def set_flags(self, **flags):
        """
        Note: For any unmodified flags, update _last_flags with the most recent
        committed value. Otherwise, for example, this could happen:

            overflow=0
            instr1 computes overflow=1, updates _last_flags, doesn't commit
            instr2 updates all flags in _last_flags except overflow (overflow remains 1 in _last_flags)
            instr2 commits all in _last_flags
            now overflow=1 even though it should still be 0
        """
        unupdated_flags = self._last_flags.keys() - flags.keys()
        for flag in unupdated_flags:
            flag_name = f"APSR_{flag}"
            self._last_flags[flag] = self.regfile.read(flag_name)
        self._last_flags.update(flags)

    def commit_flags(self):
        # XXX: capstone incorrectly sets .update_flags for adc
        if self.instruction.mnemonic == "adc":
            return
        for flag, val in self._last_flags.items():
            flag_name = f"APSR_{flag}"
            self.regfile.write(flag_name, val)

    def _shift(cpu, value, _type, amount, carry):
        """See Shift() and Shift_C() in the ARM manual"""
        assert cs.arm.ARM_SFT_INVALID < _type <= cs.arm.ARM_SFT_RRX_REG

        # XXX: Capstone should set the value of an RRX shift to 1, which is
        # asserted in the manual, but it sets it to 0, so we have to check
        if _type in (cs.arm.ARM_SFT_RRX, cs.arm.ARM_SFT_RRX_REG) and amount != 1:
            amount = 1

        elif _type in range(cs.arm.ARM_SFT_ASR_REG, cs.arm.ARM_SFT_RRX_REG + 1):
            amount = Operators.EXTRACT(amount, 0, 8)

        if amount == 0:
            return value, carry

        width = cpu.address_bit_size

        if _type in (cs.arm.ARM_SFT_ASR, cs.arm.ARM_SFT_ASR_REG):
            return ASR_C(value, amount, width)
        elif _type in (cs.arm.ARM_SFT_LSL, cs.arm.ARM_SFT_LSL_REG):
            return LSL_C(value, amount, width)
        elif _type in (cs.arm.ARM_SFT_LSR, cs.arm.ARM_SFT_LSR_REG):
            return LSR_C(value, amount, width)
        elif _type in (cs.arm.ARM_SFT_ROR, cs.arm.ARM_SFT_ROR_REG):
            return ROR_C(value, amount, width)
        elif _type in (cs.arm.ARM_SFT_RRX, cs.arm.ARM_SFT_RRX_REG):
            return RRX_C(value, carry, width)

        raise NotImplementedError("Bad shift value")

    # TODO add to abstract cpu, and potentially remove stacksub/add from it?
    def stack_push(self, data, nbytes=None):
        if isinstance(data, int):
            nbytes = nbytes or self.address_bit_size // 8
            self.SP -= nbytes
            self.write_int(self.SP, data, nbytes * 8)
        elif isinstance(data, BitVec):
            self.SP -= data.size // 8
            self.write_int(self.SP, data, data.size)
        elif isinstance(data, str):
            self.SP -= len(data)
            self.write(self.SP, data)
        else:
            raise NotImplementedError("unsupported type for stack push data")
        return self.SP

    def stack_peek(self, nbytes=4):
        return self.read(self.SP, nbytes)

    def stack_pop(self, nbytes=4):
        # TODO is the distinction between load and read really in the op size?
        nbits = nbytes * 8
        if nbits == self.address_bit_size:
            val = self.read_int(self.SP, nbits)
        else:
            val = self.read(self.SP, nbytes)
        self.SP += nbytes
        return val

    def read(self, addr, nbytes):
        return self.read_bytes(addr, nbytes)

    def write(self, addr, data):
        return self.write_bytes(addr, data)

    def set_arm_tls(self, data):
        self.regfile.write("P15_C13", data)

    @staticmethod
    def canonicalize_instruction_name(instr):
        name = instr.insn_name().upper()
        # FIXME: Workaround https://github.com/aquynh/capstone/issues/1630
        if instr.mnemonic == "addw":
            return "ADDW"
        elif instr.mnemonic == "subw":
            return "SUBW"
        return OP_NAME_MAP.get(name, name)

    def _wrap_operands(self, operands):
        return [Armv7Operand(self, op) for op in operands]

    def should_commit_flags(cpu):
        # workaround for a capstone bug (issue #980);
        # the bug has been fixed the 'master' and 'next' branches of capstone as of 2017-07-31
        if cpu.instruction.id == cs.arm.ARM_INS_UADD8:
            return True

        return cpu.instruction.update_flags

    def should_execute_conditional(cpu):
        # for the IT instruction, the cc applies to the subsequent instructions,
        # so the IT instruction should be executed regardless of its cc
        if cpu.instruction.id == cs.arm.ARM_INS_IT:
            return True

        # support for the it[x[y[z]]] <op> instructions
        if cpu._it_conditional:
            return cpu._it_conditional.pop(0)

        cc = cpu.instruction.cc
        return cpu._evaluate_conditional(cc)

    def _evaluate_conditional(cpu, cc):
        C = cpu.regfile.read("APSR_C")
        N = cpu.regfile.read("APSR_N")
        V = cpu.regfile.read("APSR_V")
        Z = cpu.regfile.read("APSR_Z")

        if cc == cs.arm.ARM_CC_AL:
            ret = True
        elif cc == cs.arm.ARM_CC_EQ:
            ret = Z
        elif cc == cs.arm.ARM_CC_NE:
            ret = Operators.NOT(Z)
        elif cc == cs.arm.ARM_CC_HS:
            ret = C
        elif cc == cs.arm.ARM_CC_LO:
            ret = Operators.NOT(C)
        elif cc == cs.arm.ARM_CC_MI:
            ret = N
        elif cc == cs.arm.ARM_CC_PL:
            ret = Operators.NOT(N)
        elif cc == cs.arm.ARM_CC_VS:
            ret = V
        elif cc == cs.arm.ARM_CC_VC:
            ret = Operators.NOT(V)
        elif cc == cs.arm.ARM_CC_HI:
            ret = Operators.AND(C, Operators.NOT(Z))
        elif cc == cs.arm.ARM_CC_LS:
            ret = Operators.OR(Operators.NOT(C), Z)
        elif cc == cs.arm.ARM_CC_GE:
            ret = N == V
        elif cc == cs.arm.ARM_CC_LT:
            ret = N != V
        elif cc == cs.arm.ARM_CC_GT:
            ret = Operators.AND(Operators.NOT(Z), N == V)
        elif cc == cs.arm.ARM_CC_LE:
            ret = Operators.OR(Z, N != V)
        else:
            raise NotImplementedError("Bad conditional tag")

        return ret

    @instruction
    def IT(cpu):
        cc = cpu.instruction.cc
        true_case = cpu._evaluate_conditional(cc)
        # this is incredibly hacky--how else does capstone expose this?
        # TODO: find a better way than string parsing the mnemonic -GR, 2017-07-13
        for c in cpu.instruction.mnemonic[1:]:
            if c == "t":
                cpu._it_conditional.append(true_case)
            elif c == "e":
                cpu._it_conditional.append(not true_case)

    @instruction
    def UADD8(cpu, dest, src, op):
        op1 = src.read()
        op2 = op.read()
        sums = list()
        carries = list()
        for i in range(4):
            uo1 = UInt(Operators.ZEXTEND(Operators.EXTRACT(op1, (8 * i), 8), 9), 9)
            uo2 = UInt(Operators.ZEXTEND(Operators.EXTRACT(op2, (8 * i), 8), 9), 9)
            byte = uo1 + uo2
            carry = Operators.EXTRACT(byte, 8, 1)
            sums.append(Operators.EXTRACT(byte, 0, 8))
            carries.append(carry)
        dest.write(Operators.CONCAT(32, *reversed(sums)))
        cpu.set_flags(GE=Operators.CONCAT(4, *reversed(carries)))

    @instruction
    def SEL(cpu, dest, op1, op2):
        op1val = op1.read()
        op2val = op2.read()
        result = list()
        GE = cpu.regfile.read("APSR_GE")
        for i in range(4):
            bit = Operators.EXTRACT(GE, i, 1)
            result.append(
                Operators.ITEBV(
                    8, bit, Operators.EXTRACT(op1val, i * 8, 8), Operators.EXTRACT(op2val, i * 8, 8)
                )
            )
        dest.write(Operators.CONCAT(32, *reversed(result)))

    @instruction(can_take_denormalized_mod_imm=True)
    def MOV(cpu, dest, src):
        """
        Implement the MOV{S} instruction.

        Note: If src operand is PC, temporarily release our logical PC
        view and conform to the spec, which dictates PC = curr instr + 8

        :param Armv7Operand dest: The destination operand; register.
        :param Armv7Operand src: The source operand; register or immediate.
        """
        if cpu.mode == cs.CS_MODE_ARM:
            result, carry_out = src.read(with_carry=True)
            dest.write(result)
            cpu.set_flags(C=carry_out, N=HighBit(result), Z=(result == 0))
        else:
            # thumb mode cannot do wonky things to the operand, so no carry calculation
            result = src.read()
            dest.write(result)
            cpu.set_flags(N=HighBit(result), Z=(result == 0))

    @instruction
    def MOVT(cpu, dest, src):
        """
        MOVT writes imm16 to Rd[31:16]. The write does not affect Rd[15:0].

        :param Armv7Operand dest: The destination operand; register
        :param Armv7Operand src: The source operand; 16-bit immediate
        """
        assert src.type == "immediate"
        imm = src.read()
        low_halfword = dest.read() & Mask(16)
        dest.write((imm << 16) | low_halfword)

    @instruction
    def MRC(cpu, coprocessor, opcode1, dest, coprocessor_reg_n, coprocessor_reg_m, opcode2):
        """
        MRC moves to ARM register from coprocessor.

        :param Armv7Operand coprocessor: The name of the coprocessor; immediate
        :param Armv7Operand opcode1: coprocessor specific opcode; 3-bit immediate
        :param Armv7Operand dest: the destination operand: register
        :param Armv7Operand coprocessor_reg_n: the coprocessor register; immediate
        :param Armv7Operand coprocessor_reg_m: the coprocessor register; immediate
        :param Armv7Operand opcode2: coprocessor specific opcode; 3-bit immediate
        """
        assert coprocessor.type == "coprocessor"
        assert opcode1.type == "immediate"
        assert opcode2.type == "immediate"
        assert dest.type == "register"
        imm_coprocessor = coprocessor.read()
        imm_opcode1 = opcode1.read()
        imm_opcode2 = opcode2.read()
        coprocessor_n_name = coprocessor_reg_n.read()
        coprocessor_m_name = coprocessor_reg_m.read()

        if 15 == imm_coprocessor:  # MMU
            if 0 == imm_opcode1:
                if 13 == coprocessor_n_name:
                    if 3 == imm_opcode2:
                        dest.write(cpu.regfile.read("P15_C13"))
                        return
        raise NotImplementedError(
            "MRC: unimplemented combination of coprocessor, opcode, and coprocessor register"
        )

    @instruction
    def LDRD(cpu, dest1, dest2, src, offset=None):
        """Loads double width data from memory."""
        assert dest1.type == "register"
        assert dest2.type == "register"
        assert src.type == "memory"
        mem1 = cpu.read_int(src.address(), 32)
        mem2 = cpu.read_int(src.address() + 4, 32)
        writeback = cpu._compute_writeback(src, offset)
        dest1.write(mem1)
        dest2.write(mem2)
        cpu._cs_hack_ldr_str_writeback(src, offset, writeback)

    @instruction
    def STRD(cpu, src1, src2, dest, offset=None):
        """Writes the contents of two registers to memory."""
        assert src1.type == "register"
        assert src2.type == "register"
        assert dest.type == "memory"
        val1 = src1.read()
        val2 = src2.read()
        writeback = cpu._compute_writeback(dest, offset)
        cpu.write_int(dest.address(), val1, 32)
        cpu.write_int(dest.address() + 4, val2, 32)
        cpu._cs_hack_ldr_str_writeback(dest, offset, writeback)

    @instruction
    def LDREX(cpu, dest, src, offset=None):
        """
        LDREX loads data from memory.
        * If the physical address has the shared TLB attribute, LDREX
          tags the physical address as exclusive access for the current
          processor, and clears any exclusive access tag for this
          processor for any other physical address.
        * Otherwise, it tags the fact that the executing processor has
          an outstanding tagged physical address.

        :param Armv7Operand dest: the destination register; register
        :param Armv7Operand src: the source operand: register
        """
        # TODO: add lock mechanism to underlying memory --GR, 2017-06-06
        cpu._LDR(dest, src, 32, False, offset)

    @instruction
    def STREX(cpu, status, *args):
        """
        STREX performs a conditional store to memory.
        :param Armv7Operand status: the destination register for the returned status; register
        """
        # TODO: implement conditional return with appropriate status --GR, 2017-06-06
        status.write(0)
        return cpu._STR(cpu.address_bit_size, *args)

    def _UXT(cpu, dest, src, src_width):
        """
        Helper for UXT* family of instructions.

        :param ARMv7Operand dest: the destination register; register
        :param ARMv7Operand dest: the source register; register
        :param int src_width: bits to consider of the src operand
        """
        val = GetNBits(src.read(), src_width)
        word = Operators.ZEXTEND(val, cpu.address_bit_size)
        dest.write(word)

    @instruction
    def UXTB(cpu, dest, src):
        """
        UXTB extracts an 8-bit value from a register, zero-extends
        it to the size of the register, and writes the result to the destination register.

        :param ARMv7Operand dest: the destination register; register
        :param ARMv7Operand dest: the source register; register
        """
        cpu._UXT(dest, src, 8)

    @instruction
    def UXTH(cpu, dest, src):
        """
        UXTH extracts an 16-bit value from a register, zero-extends
        it to the size of the register, and writes the result to the destination register.

        :param ARMv7Operand dest: the destination register; register
        :param ARMv7Operand dest: the source register; register
        """
        cpu._UXT(dest, src, 16)

    @instruction
    def PLD(cpu, addr, offset=None):
        """PLD instructs the cpu that the address at addr might be loaded soon."""

    def _compute_writeback(cpu, operand, offset):
        if offset:
            off = offset.read()
        else:
            off = operand.get_mem_offset()
        wbaddr = operand.get_mem_base_addr() + off
        return wbaddr

    def _cs_hack_ldr_str_writeback(cpu, operand, offset, val):
        # capstone bug doesn't set writeback correctly for postindex reg
        if cpu.instruction.writeback or offset:
            operand.writeback(val)

    def _STR(cpu, width, src, dest, offset=None):
        val = src.read()
        writeback = cpu._compute_writeback(dest, offset)
        cpu.write_int(dest.address(), val, width)
        cpu._cs_hack_ldr_str_writeback(dest, offset, writeback)

    @instruction
    def STR(cpu, *args):
        return cpu._STR(cpu.address_bit_size, *args)

    @instruction
    def STRB(cpu, *args):
        return cpu._STR(8, *args)

    @instruction
    def STRH(cpu, *args):
        return cpu._STR(16, *args)

    def _LDR(cpu, dest, src, width, is_signed, offset):
        mem = cpu.read_int(src.address(), width)
        writeback = cpu._compute_writeback(src, offset)
        if is_signed:
            word = Operators.SEXTEND(mem, width, cpu.address_bit_size)
        else:
            word = Operators.ZEXTEND(mem, cpu.address_bit_size)
        if dest.reg in ("PC", "R15"):
            cpu._set_mode_by_val(word)
            word &= ~0x1
            logger.debug(f"LDR writing 0x{word:x} -> PC")
        dest.write(word)
        cpu._cs_hack_ldr_str_writeback(src, offset, writeback)

    @instruction
    def LDR(cpu, dest, src, offset=None):
        cpu._LDR(dest, src, 32, False, offset)

    @instruction
    def LDRH(cpu, dest, src, offset=None):
        cpu._LDR(dest, src, 16, False, offset)

    @instruction
    def LDRSH(cpu, dest, src, offset=None):
        cpu._LDR(dest, src, 16, True, offset)

    @instruction
    def LDRB(cpu, dest, src, offset=None):
        cpu._LDR(dest, src, 8, False, offset)

    @instruction
    def LDRSB(cpu, dest, src, offset=None):
        cpu._LDR(dest, src, 8, True, offset)

    def _ADD(cpu, _op1, _op2, carry=0):
        W = cpu.address_bit_size
        # masking to 32 because sometimes capstone's op.imm field is negative.
        # this converts it back to unsigned
        _op2 = Operators.ZEXTEND(_op2, W)

        uo1 = UInt(_op1, W * 2)
        uo2 = UInt(_op2, W * 2)
        c = UInt(carry, W * 2)
        unsigned_sum = uo1 + uo2 + c

        so1 = SInt(Operators.SEXTEND(_op1, W, W * 2), W * 2)
        so2 = SInt(Operators.SEXTEND(_op2, W, W * 2), W * 2)
        signed_sum = so1 + so2 + c

        result = GetNBits(unsigned_sum, W)

        carry_out = UInt(result, W * 2) != unsigned_sum
        overflow = SInt(Operators.SEXTEND(result, W, W * 2), W * 2) != signed_sum

        cpu.set_flags(C=carry_out, V=overflow, N=HighBit(result), Z=result == 0)

        return result, carry_out, overflow

    @instruction(can_take_denormalized_mod_imm=True)
    def ADC(cpu, dest, op1, op2=None):
        carry = cpu.regfile.read("APSR_C")
        if op2 is not None:
            result, carry, overflow = cpu._ADD(op1.read(), op2.read(), carry)
        else:
            result, carry, overflow = cpu._ADD(dest.read(), op1.read(), carry)
        dest.write(result)
        return result, carry, overflow

    @instruction(can_take_denormalized_mod_imm=True)
    def ADD(cpu, dest, src, add=None):
        if add is not None:
            result, carry, overflow = cpu._ADD(src.read(), add.read())
        else:
            # support for the thumb mode version of adds <dest>, <immediate>
            result, carry, overflow = cpu._ADD(dest.read(), src.read())
        dest.write(result)
        return result, carry, overflow

    @instruction(can_take_denormalized_mod_imm=True)
    def RSB(cpu, dest, src, add):
        inv_src = GetNBits(~src.read(), cpu.address_bit_size)
        result, carry, overflow = cpu._ADD(inv_src, add.read(), 1)
        dest.write(result)
        return result, carry, overflow

    @instruction(can_take_denormalized_mod_imm=True)
    def RSC(cpu, dest, src, add):
        carry = cpu.regfile.read("APSR_C")
        inv_src = GetNBits(~src.read(), cpu.address_bit_size)
        result, carry, overflow = cpu._ADD(inv_src, add.read(), carry)
        dest.write(result)
        return result, carry, overflow

    @instruction(can_take_denormalized_mod_imm=True)
    def SUB(cpu, dest, src, add=None):
        if add is not None:
            result, carry, overflow = cpu._ADD(src.read(), ~add.read(), 1)
        else:
            # support for the thumb mode version of sub <dest>, <immediate>
            result, carry, overflow = cpu._ADD(dest.read(), ~src.read(), 1)

        dest.write(result)
        return result, carry, overflow

    @instruction(can_take_denormalized_mod_imm=True)
    def SBC(cpu, dest, op1, op2=None):
        carry = cpu.regfile.read("APSR_C")
        if op2 is not None:
            result, carry, overflow = cpu._ADD(op1.read(), ~op2.read(), carry)
        else:
            result, carry, overflow = cpu._ADD(dest.read(), ~op1.read(), carry)
        dest.write(result)
        return result, carry, overflow

    @instruction
    def ADR(cpu, dest, src):
        """
        Address to Register adds an immediate value to the PC value, and writes the result to the destination register.

        :param ARMv7Operand dest: Specifies the destination register.
        :param ARMv7Operand src:
            Specifies the label of an instruction or literal data item whose address is to be loaded into
            <Rd>. The assembler calculates the required value of the offset from the Align(PC,4)
            value of the ADR instruction to this label.
        """
        aligned_pc = (cpu.instruction.address + 4) & 0xFFFFFFFC
        dest.write(aligned_pc + src.read())

    @instruction
    def ADDW(cpu, dest, src, add):
        """
        This instruction adds an immediate value to a register value, and writes the result to the destination register.
        It doesn't update the condition flags.

        :param ARMv7Operand dest: Specifies the destination register. If omitted, this register is the same as src.
        :param ARMv7Operand src:
            Specifies the register that contains the first operand. If the SP is specified for dest, see ADD (SP plus
            immediate). If the PC is specified for dest, see ADR.
        :param ARMv7Operand add:
            Specifies the immediate value to be added to the value obtained from src. The range of allowed values is
            0-4095.
        """
        aligned_pc = (cpu.instruction.address + 4) & 0xFFFFFFFC
        if src.type == "register" and src.reg in ("PC", "R15"):
            src = aligned_pc
        else:
            src = src.read()
        dest.write(src + add.read())

    @instruction
    def SUBW(cpu, dest, src, add):
        """
        This instruction subtracts an immediate value from a register value, and writes the result to the destination
        register. It can optionally update the condition flags based on the result.

        :param ARMv7Operand dest: Specifies the destination register. If omitted, this register is the same as src.
        :param ARMv7Operand src:
            Specifies the register that contains the first operand. If the SP is specified for dest, see ADD (SP plus
            immediate). If the PC is specified for dest, see ADR.
        :param ARMv7Operand add:
            Specifies the immediate value to be added to the value obtained from src. The range of allowed values is
            0-4095.
        """
        aligned_pc = (cpu.instruction.address + 4) & 0xFFFFFFFC
        if src.type == "register" and src.reg in ("PC", "R15"):
            src = aligned_pc
        else:
            src = src.read()
        dest.write(src - add.read())

    @instruction
    def B(cpu, dest):
        cpu.PC = dest.read()

    @instruction
    def BX(cpu, dest):
        dest_val = dest.read()
        cpu._set_mode_by_val(dest_val)
        cpu.PC = dest_val & ~1

    @instruction
    def BLE(cpu, dest):
        cpu.PC = Operators.ITEBV(
            cpu.address_bit_size, cpu.regfile.read("APSR_Z"), dest.read(), cpu.PC
        )

    @instruction
    def CBZ(cpu, op, dest):
        """
        Compare and Branch on Zero compares the value in a register with zero, and conditionally branches forward
        a constant value. It does not affect the condition flags.

        :param ARMv7Operand op: Specifies the register that contains the first operand.
        :param ARMv7Operand dest:
            Specifies the label of the instruction that is to be branched to. The assembler calculates the
            required value of the offset from the PC value of the CBZ instruction to this label, then
            selects an encoding that will set imm32 to that offset. Allowed offsets are even numbers in
            the range 0 to 126.
        """
        cpu.PC = Operators.ITEBV(cpu.address_bit_size, op.read(), cpu.PC, dest.read())

    @instruction
    def CBNZ(cpu, op, dest):
        """
        Compare and Branch on Non-Zero compares the value in a register with zero, and conditionally branches
        forward a constant value. It does not affect the condition flags.

        :param ARMv7Operand op: Specifies the register that contains the first operand.
        :param ARMv7Operand dest:
            Specifies the label of the instruction that is to be branched to. The assembler calculates the
            required value of the offset from the PC value of the CBNZ instruction to this label, then
            selects an encoding that will set imm32 to that offset. Allowed offsets are even numbers in
            the range 0 to 126.
        """
        cpu.PC = Operators.ITEBV(cpu.address_bit_size, op.read(), dest.read(), cpu.PC)

    @instruction
    def BL(cpu, label):
        next_instr_addr = cpu.regfile.read("PC")
        if cpu.mode == cs.CS_MODE_THUMB:
            cpu.regfile.write("LR", next_instr_addr + 1)
        else:
            cpu.regfile.write("LR", next_instr_addr)
        cpu.regfile.write("PC", label.read())

    @instruction
    def BLX(cpu, dest):
        address = cpu.PC
        target = dest.read()
        next_instr_addr = cpu.regfile.read("PC")
        if cpu.mode == cs.CS_MODE_THUMB:
            cpu.regfile.write("LR", next_instr_addr + 1)
        else:
            cpu.regfile.write("LR", next_instr_addr)
        cpu.regfile.write("PC", target & ~1)

        # The `blx <label>` form of this instruction forces a mode swap
        # Otherwise check the lsb of the destination and set the mode
        if dest.type == "immediate":
            logger.debug(f"swapping mode due to BLX at inst 0x{address:x}")
            cpu._swap_mode()
        elif dest.type == "register":
            cpu._set_mode_by_val(dest.read())

    @instruction
    def TBB(cpu, dest):
        """
        Table Branch Byte causes a PC-relative forward branch using a table of single byte offsets. A base register
        provides a pointer to the table, and a second register supplies an index into the table. The branch length is
        twice the value of the byte returned from the table.

        :param ARMv7Operand dest: see below; register
        """
        # Capstone merges the two registers values into one operand, so we need to extract them back

        # Specifies the base register. This contains the address of the table of branch lengths. This
        # register is allowed to be the PC. If it is, the table immediately follows this instruction.
        base_addr = dest.get_mem_base_addr()
        if dest.mem.base in ("PC", "R15"):
            base_addr = cpu.PC

        # Specifies the index register. This contains an integer pointing to a single byte within the
        # table. The offset within the table is the value of the index.
        offset = cpu.read_int(base_addr + dest.get_mem_offset(), 8)
        offset = Operators.ZEXTEND(offset, cpu.address_bit_size)

        cpu.PC += offset << 1

    @instruction
    def TBH(cpu, dest):
        """
        Table Branch Halfword causes a PC-relative forward branch using a table of single halfword offsets. A base
        register provides a pointer to the table, and a second register supplies an index into the table. The branch
        length is twice the value of the halfword returned from the table.

        :param ARMv7Operand dest: see below; register
        """
        # Capstone merges the two registers values into one operand, so we need to extract them back

        # Specifies the base register. This contains the address of the table of branch lengths. This
        # register is allowed to be the PC. If it is, the table immediately follows this instruction.
        base_addr = dest.get_mem_base_addr()
        if dest.mem.base in ("PC", "R15"):
            base_addr = cpu.PC

        # Specifies the index register. This contains an integer pointing to a halfword within the table.
        # The offset within the table is twice the value of the index.
        offset = cpu.read_int(base_addr + dest.get_mem_offset(), 16)
        offset = Operators.ZEXTEND(offset, cpu.address_bit_size)

        cpu.PC += offset << 1

    @instruction(can_take_denormalized_mod_imm=True)
    def CMP(cpu, reg, compare):
        notcmp = ~compare.read() & Mask(cpu.address_bit_size)
        cpu._ADD(reg.read(), notcmp, 1)

    @instruction
    def POP(cpu, *regs):
        for reg in regs:
            val = cpu.stack_pop(cpu.address_bit_size // 8)
            if reg.reg in ("PC", "R15"):
                cpu._set_mode_by_val(val)
                val = val & ~0x1
            reg.write(val)

    @instruction
    def PUSH(cpu, *regs):
        high_to_low_regs = [r.read() for r in regs[::-1]]
        for reg in high_to_low_regs:
            cpu.stack_push(reg)

    @instruction
    def CLZ(cpu, dest, src):

        # Check if the |pos| bit is 1, pos being the offset from the MSB
        value = src.read()
        msb = cpu.address_bit_size - 1
        result = 32

        for pos in range(cpu.address_bit_size):
            cond = Operators.EXTRACT(value, pos, 1) == 1
            result = Operators.ITEBV(cpu.address_bit_size, cond, msb - pos, result)

        dest.write(result)

    @instruction
    def NOP(cpu):
        pass

    @instruction
    def REV(cpu, dest, op):
        opval = op.read()
        _bytes = list()
        for i in range(4):
            _bytes.append(Operators.EXTRACT(opval, i * 8, 8))
        dest.write(Operators.CONCAT(32, *_bytes))

    @instruction
    def SXTH(cpu, dest, op):
        _op = op.read()
        dest.write(Operators.SEXTEND(Operators.EXTRACT(_op, 0, 16), 16, 32))

    def _LDM(cpu, insn_id, base, regs):
        """
        LDM (Load Multiple) loads a non-empty subset, or possibly all, of the general-purpose registers from
        sequential memory locations. It is useful for block loads, stack operations and procedure exit sequences.

        :param int insn_id: should be one of ARM_INS_LDM, ARM_INS_LDMIB, ARM_INS_LDMDA, ARM_INS_LDMDB
        :param Armv7Operand base: Specifies the base register.
        :param list[Armv7Operand] regs:
            Is a list of registers. It specifies the set of registers to be loaded by the LDM instruction.
            The registers are loaded in sequence, the lowest-numbered register from the lowest memory
            address (start_address), through to the highest-numbered register from the highest memory
            address (end_address). If the PC is specified in the register list (opcode bit[15] is set),
            the instruction causes a branch to the address (data) loaded into the PC.

        It's technically UNKNOWN if you writeback to a register you loaded into, but we let it slide.
        """
        if cpu.instruction.usermode:
            raise NotImplementedError("Use of the S bit is not supported")

        increment = insn_id in (cs.arm.ARM_INS_LDM, cs.arm.ARM_INS_LDMIB)
        after = insn_id in (cs.arm.ARM_INS_LDM, cs.arm.ARM_INS_LDMDA)

        address = base.read()

        for reg in regs:
            if not after:
                address += (1 if increment else -1) * (reg.size // 8)

            reg.write(cpu.read_int(address, reg.size))
            if reg.reg in ("PC", "R15"):
                # The general-purpose registers loaded can include the PC. If they do, the word loaded for the PC is
                # treated as an address and a branch occurs to that address. In ARMv5 and above, bit[0] of the loaded
                # value determines whether execution continues after this branch in ARM state or in Thumb state, as
                # though a BX instruction had been executed.
                cpu._set_mode_by_val(cpu.PC)
                cpu.PC = cpu.PC & ~1

            if after:
                address += (1 if increment else -1) * (reg.size // 8)

        if cpu.instruction.writeback:
            base.writeback(address)

    @instruction
    def LDM(cpu, base, *regs):
        cpu._LDM(cs.arm.ARM_INS_LDM, base, regs)

    @instruction
    def LDMIB(cpu, base, *regs):
        cpu._LDM(cs.arm.ARM_INS_LDMIB, base, regs)

    @instruction
    def LDMDA(cpu, base, *regs):
        cpu._LDM(cs.arm.ARM_INS_LDMDA, base, regs)

    @instruction
    def LDMDB(cpu, base, *regs):
        cpu._LDM(cs.arm.ARM_INS_LDMDB, base, regs)

    def _STM(cpu, insn_id, base, regs):
        """
        STM (Store Multiple) stores a non-empty subset (or possibly all) of the general-purpose registers to
        sequential memory locations.

        :param int insn_id: should be one of ARM_INS_STM, ARM_INS_STMIB, ARM_INS_STMDA, ARM_INS_STMDB
        :param Armv7Operand base: Specifies the base register.
        :param list[Armv7Operand] regs:
            Is a list of registers. It specifies the set of registers to be stored by the STM instruction.
            The registers are stored in sequence, the lowest-numbered register to the lowest
            memory address (start_address), through to the highest-numbered register to the
            highest memory address (end_address).
        """
        if cpu.instruction.usermode:
            raise NotImplementedError("Use of the S bit is not supported")

        increment = insn_id in (cs.arm.ARM_INS_STM, cs.arm.ARM_INS_STMIB)
        after = insn_id in (cs.arm.ARM_INS_STM, cs.arm.ARM_INS_STMDA)

        address = base.read()

        for reg in regs:
            if not after:
                address += (1 if increment else -1) * (reg.size // 8)

            cpu.write_int(address, reg.read(), reg.size)

            if after:
                address += (1 if increment else -1) * (reg.size // 8)

        if cpu.instruction.writeback:
            base.writeback(address)

    @instruction
    def STM(cpu, base, *regs):
        cpu._STM(cs.arm.ARM_INS_STM, base, regs)

    @instruction
    def STMIB(cpu, base, *regs):
        cpu._STM(cs.arm.ARM_INS_STMIB, base, regs)

    @instruction
    def STMDA(cpu, base, *regs):
        cpu._STM(cs.arm.ARM_INS_STMDA, base, regs)

    @instruction
    def STMDB(cpu, base, *regs):
        cpu._STM(cs.arm.ARM_INS_STMDB, base, regs)

    def _bitwise_instruction(cpu, operation, dest, op1, op2=None):
        if op2:
            op2_val, carry = op2.read(with_carry=True)
            result = operation(op1.read(), op2_val)
        else:
            # We _do_ use this form, contrary to what LGTM says
            op1_val, carry = op1.read(with_carry=True)  # lgtm [py/call/wrong-arguments]
            result = operation(op1_val)
        if dest is not None:
            dest.write(result)
        cpu.set_flags(C=carry, N=HighBit(result), Z=(result == 0))

    @instruction(can_take_denormalized_mod_imm=True)
    def ORR(cpu, dest, op1, op2=None):
        if op2 is not None:
            cpu._bitwise_instruction(ops.or_, dest, op1, op2)
        else:
            cpu._bitwise_instruction(ops.or_, dest, dest, op1)

    @instruction(can_take_denormalized_mod_imm=True)
    def ORN(cpu, dest, op1, op2=None):
        if op2 is not None:
            cpu._bitwise_instruction(lambda x, y: x | ~y, dest, op1, op2)
        else:
            cpu._bitwise_instruction(lambda x, y: x | ~y, dest, dest, op1)

    @instruction(can_take_denormalized_mod_imm=True)
    def EOR(cpu, dest, op1, op2=None):
        if op2 is not None:
            cpu._bitwise_instruction(ops.xor, dest, op1, op2)
        else:
            cpu._bitwise_instruction(ops.xor, dest, dest, op1)

    @instruction(can_take_denormalized_mod_imm=True)
    def AND(cpu, dest, op1, op2=None):
        if op2 is not None:
            cpu._bitwise_instruction(ops.and_, dest, op1, op2)
        else:
            cpu._bitwise_instruction(ops.and_, dest, dest, op1)

    @instruction(can_take_denormalized_mod_imm=True)
    def TEQ(cpu, op1, op2=None):
        cpu._bitwise_instruction(ops.xor, None, op1, op2)
        cpu.commit_flags()

    @instruction(can_take_denormalized_mod_imm=True)
    def TST(cpu, op1, op2):
        shifted, carry = op2.read(with_carry=True)
        result = op1.read() & shifted
        cpu.set_flags(N=HighBit(result), Z=(result == 0), C=carry)

    @instruction
    def SVC(cpu, op):
        if op.read() != 0:
            logger.warning(f"Bad SVC number: {op.read():08}")
        raise Interruption(0)

    @instruction(can_take_denormalized_mod_imm=True)
    def CMN(cpu, src, add):
        result, carry, overflow = cpu._ADD(src.read(), add.read())
        return result, carry, overflow

    def _SR(cpu, insn_id, dest, op, *rest):
        """
        Notes on Capstone behavior:
        - In ARM mode, _SR reg has `rest`, but _SR imm does not, its baked into `op`.
        - In ARM mode, `lsr r1, r2` will have a `rest[0]`
        - In Thumb mode, `lsr r1, r2` will have an empty `rest`
        - In ARM mode, something like `lsr r1, 3` will not have `rest` and op will be
            the immediate.
        """
        assert insn_id in (cs.arm.ARM_INS_ASR, cs.arm.ARM_INS_LSL, cs.arm.ARM_INS_LSR)

        if insn_id == cs.arm.ARM_INS_ASR:
            if rest and rest[0].type == "immediate":
                srtype = cs.arm.ARM_SFT_ASR
            else:
                srtype = cs.arm.ARM_SFT_ASR_REG
        elif insn_id == cs.arm.ARM_INS_LSL:
            if rest and rest[0].type == "immediate":
                srtype = cs.arm.ARM_SFT_LSL
            else:
                srtype = cs.arm.ARM_SFT_LSL_REG
        elif insn_id == cs.arm.ARM_INS_LSR:
            if rest and rest[0].type == "immediate":
                srtype = cs.arm.ARM_SFT_LSR
            else:
                srtype = cs.arm.ARM_SFT_LSR_REG

        carry = cpu.regfile.read("APSR_C")
        if rest and rest[0].type == "register":
            # FIXME we should make Operand.op private (and not accessible)
            src_reg = cpu.instruction.reg_name(rest[0].op.reg).upper()
            amount = cpu.regfile.read(src_reg)
            result, carry = cpu._shift(op.read(), srtype, amount, carry)
        elif rest and rest[0].type == "immediate":
            amount = rest[0].read()
            result, carry = cpu._shift(op.read(), srtype, amount, carry)
        elif cpu.mode == cs.CS_MODE_THUMB:
            amount = op.read()
            result, carry = cpu._shift(dest.read(), srtype, amount, carry)
        else:
            result, carry = op.read(with_carry=True)
        dest.write(result)

        cpu.set_flags(N=HighBit(result), Z=(result == 0), C=carry)

    @instruction
    def ASR(cpu, dest, op, *rest):
        cpu._SR(cs.arm.ARM_INS_ASR, dest, op, *rest)

    @instruction
    def LSL(cpu, dest, op, *rest):
        cpu._SR(cs.arm.ARM_INS_LSL, dest, op, *rest)

    @instruction
    def LSR(cpu, dest, op, *rest):
        cpu._SR(cs.arm.ARM_INS_LSR, dest, op, *rest)

    @instruction
    def UMULL(cpu, rdlo, rdhi, rn, rm):
        result = UInt(rn.read(), cpu.address_bit_size * 2) * UInt(
            rm.read(), cpu.address_bit_size * 2
        )
        rdhi.write(Operators.EXTRACT(result, cpu.address_bit_size, cpu.address_bit_size))
        rdlo.write(GetNBits(result, cpu.address_bit_size))
        cpu.set_flags(N=Bit(result, 63), Z=(result == 0))

    @instruction
    def MUL(cpu, dest, src1, src2):
        width = cpu.address_bit_size
        op1 = SInt(src1.read(), width)
        op2 = SInt(src2.read(), width)
        result = op1 * op2
        dest.write(result & Mask(width))
        cpu.set_flags(N=HighBit(result), Z=(result == 0))

    @instruction(can_take_denormalized_mod_imm=True)
    def MVN(cpu, dest, op):
        cpu._bitwise_instruction(lambda x: ~x, dest, op)

    @instruction
    def MLA(cpu, dest, op1, op2, addend):
        width = cpu.address_bit_size
        op1_val = SInt(op1.read(), width)
        op2_val = SInt(op2.read(), width)
        add_val = SInt(addend.read(), width)
        result = op1_val * op2_val + add_val

        dest.write(result & Mask(cpu.address_bit_size))
        cpu.set_flags(N=HighBit(result), Z=(result == 0))

    @instruction(can_take_denormalized_mod_imm=True)
    def BIC(cpu, dest, op1, op2=None):
        if op2 is not None:
            result = (op1.read() & ~op2.read()) & Mask(cpu.address_bit_size)
        else:
            result = (dest.read() & ~op1.read()) & Mask(cpu.address_bit_size)
        dest.write(result)
        cpu.set_flags(N=HighBit(result), Z=(result == 0))

    def _VSTM(cpu, address, *regs):
        for reg in regs:
            cpu.write_int(address, reg.read(), reg.size)
            address += reg.size // 8

        return address

    @instruction
    def VSTMIA(cpu, base, *regs):
        updated_address = cpu._VSTM(base.read(), *regs)
        if cpu.instruction.writeback:
            base.writeback(updated_address)

    @instruction
    def VSTMDB(cpu, base, *regs):
        address = base.read() - cpu.address_bit_size // 8 * len(regs)
        updated_address = cpu._VSTM(address, *regs)
        if cpu.instruction.writeback:
            base.writeback(updated_address)

    @instruction
    def VLDMIA(cpu, base, *regs):
        cpu._LDM(cs.arm.ARM_INS_LDM, base, regs)

    @instruction
    def STCL(cpu, *operands):
        pass

    @instruction
    def DMB(cpu, *operands):
        """
        Used by the the __kuser_dmb ARM Linux user-space handler. This is a nop
        under Manticore's memory and execution model.
        """

    @instruction
    def LDCL(cpu, *operands):
        """Occasionally used in glibc (longjmp in ld.so). Nop under our execution model."""

    @instruction
    def UQSUB8(cpu, dest, op1, op2):
        src1 = op1.read()
        src2 = op2.read()
        result = []
        for offset in reversed(range(0, op1.size, 8)):
            byte1 = Operators.EXTRACT(src1, offset, 8)
            byte2 = Operators.EXTRACT(src2, offset, 8)
            byte_diff = byte1 - byte2
            result.append(Operators.ITEBV(8, byte_diff < 0, 0, byte_diff))
        dest.write(Operators.CONCAT(dest.size, *result))
