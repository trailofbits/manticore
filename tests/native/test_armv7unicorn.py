import unittest

import os
import struct
from capstone import CS_MODE_THUMB, CS_MODE_ARM
from functools import wraps
import logging
from unicorn import UC_QUERY_MODE, UC_MODE_THUMB

from manticore.native.cpu.abstractcpu import ConcretizeRegister
from manticore.native.cpu.arm import Armv7Cpu as Cpu, Mask, Interruption
from manticore.core.smtlib import ConstraintSet
from manticore.native.state import State
from manticore.native.memory import ConcretizeMemory, Memory32
from manticore.platforms import linux
from manticore.utils.fallback_emulator import UnicornEmulator
import binascii

ks = None
ks_thumb = None

logger = logging.getLogger("ARM_TESTS")

__doc__ = """
Test the Unicorn emulation stub.  Armv7UnicornInstructions includes all
semantics from ARM tests to ensure that they match. UnicornConcretization tests
to make sure symbolic values get properly concretized.
"""

# This is a cache of assembled instructions.
# This exists so that Manticore's tests can run without requiring that the
# Keystone dependency be installed.
# If additional test cases are added that require new instructions, this cache
# will need to be updated.
assembly_cache = {
    CS_MODE_ARM: {
        "adc r3, r1, r2": b"0230a1e0",
        "adc r3, r1, r2, ror #3": b"e231a1e0",
        "add r3, r1, 0x1000000": b"013481e2",
        "add r3, r1, 0xff000000": b"ff3481e2",
        "add r3, r1, 0x100": b"013c81e2",
        "add r3, r1, 55": b"373081e2",
        "add r3, r1, 0x1": b"013081e2",
        "add r3, r1, r2": b"023081e0",
        "add r3, r1, r2, asr #3": b"c23181e0",
        "add r3, r1, r2, asr r4": b"523481e0",
        "add r3, r1, r2, lsl #3": b"823181e0",
        "add r3, r1, r2, lsl r4": b"123481e0",
        "add r3, r1, r2, lsr #3": b"a23181e0",
        "add r3, r1, r2, lsr r4": b"323481e0",
        "add r3, r1, r2, ror #3": b"e23181e0",
        "add r3, r1, r2, ror r4": b"723481e0",
        "add r3, r1, r2, rrx": b"623081e0",
        "adds r3, r1, 0x1000000": b"013491e2",
        "adds r3, r1, 0x80000000": b"023191e2",
        "adds r3, r1, 0xff000000": b"ff3491e2",
        "adds r3, r1, 0x100": b"013c91e2",
        "adds r3, r1, 55": b"373091e2",
        "adds r3, r1, 0x1": b"013091e2",
        "adds r3, r3, 0x0": b"003093e2",
        "adds r3, r1, r2": b"023091e0",
        "adds r3, r1, r2, asr #3": b"c23191e0",
        "adds r3, r1, r2, rrx": b"623091e0",
        "and r2, r2, #1": b"012002e2",
        "and r1, r1, r2": b"021001e0",
        "BIC R2, R1, #0x10": b"1020c1e3",
        "bl 0x170": b"5a0000eb",
        "bl #-4": b"fdffffeb",
        "BLX R1": b"31ff2fe1",
        "bx r1": b"11ff2fe1",
        "clz r1, r2": b"121f6fe1",
        "cmp r0, 0": b"000050e3",
        "cmp r0, 0x40000000": b"010150e3",
        "cmp r0, 3": b"030050e3",
        "cmp r0, 2": b"020050e3",
        "cmp r0, 5": b"050050e3",
        "cmp r0, 0xa0000000": b"0a0250e3",
        "eor r2, r3, #5": b"052023e2",
        "eor r2, r3, r4": b"042023e0",
        "eor r2, r3, r4, LSL #4": b"042223e0",
        "eors r2, r3": b"032032e0",
        "adds r2, r1, #0x1": b"012091e2",
        "tst r3, r1": b"010013e1",
        "ldm sp, {r1, r2, r3}": b"0e009de8",
        "ldm sp!, {r1, r2, r3}": b"0e00bde8",
        "ldr r1, [sp, #-4]": b"04101de5",
        "ldr r1, [sp]": b"00109de5",
        "ldr r1, [sp, #4]": b"04109de5",
        "ldr r1, [sp], #-5": b"05101de4",
        "ldr r1, [sp], #5": b"05109de4",
        "ldr r1, [sp, #-4]!": b"04103de5",
        "ldr r1, [sp, #4]!": b"0410bde5",
        "ldr r1, [sp, r2]": b"02109de7",
        "ldr r1, [sp, -r2]": b"02101de7",
        "ldr r1, [sp, -r2, lsl #3]": b"82111de7",
        "ldr r1, [sp, r2, lsl #3]": b"82119de7",
        "ldr r1, [sp], r2": b"02109de6",
        "ldr r1, [sp], -r2, lsl #3": b"82111de6",
        "ldr r1, [sp, r2]!": b"0210bde7",
        "ldr r1, [sp, -r2, lsl #3]!": b"82113de7",
        "ldrb r1, [sp]": b"0010dde5",
        "ldrb r1, [sp, r2]": b"0210dde7",
        "ldrh r1, [sp]": b"b010dde1",
        "ldrh r1, [sp, r2]": b"b2109de1",
        "ldrsb r1, [sp]": b"d010dde1",
        "ldrsb r1, [sp, r2]": b"d2109de1",
        "ldrsh r1, [sp]": b"f010dde1",
        "ldrsh r1, [sp, r2]": b"f2109de1",
        "lsls r4, r3, 31": b"834fb0e1",
        "lsls r4, r3, 1": b"8340b0e1",
        "lsls r4, r3, r2": b"1342b0e1",
        "lsr r0, r0, r2": b"3002a0e1",
        "lsr r0, r0, #3": b"a001a0e1",
        "MLA R1, R2, R3, R4": b"924321e0",
        "mov r0, 0x0": b"0000a0e3",
        "mov r0, 0xff000000": b"ff04a0e3",
        "mov r0, 0x100": b"010ca0e3",
        "mov r0, 42": b"2a00a0e3",
        "mov r0, r1": b"0100a0e1",
        "movs r0, 0": b"0000b0e3",
        "movs r0, 0xff000000": b"ff04b0e3",
        "movs r0, 0x100": b"010cb0e3",
        "movs r0, 0x0e000000": b"0e04b0e3",
        "movs r0, 42": b"2a00b0e3",
        "movs r0, r1": b"0100b0e1",
        "movw r0, 0xffff": b"ff0f0fe3",
        "movw r0, 0": b"000000e3",
        "MUL R1, R2": b"910201e0",
        "MUL R3, R1, R2": b"910203e0",
        "orr r2, r3, #5": b"052083e3",
        "orr r2, r3, r4": b"042083e1",
        "orr r2, r3, r4, LSL #4": b"042283e1",
        "orr r2, r3": b"032082e1",
        "orrs r2, r3": b"032092e1",
        "pop {r1, r2, r3}": b"0e00bde8",
        "pop {r1}": b"04109de4",
        "push {r1, r2, r3}": b"0e002de9",
        "push {r1}": b"04102de5",
        "RSB r2, r2, #31": b"1f2062e2",
        "sbc r3, r1, #5": b"0530c1e2",
        "stm sp, {r1, r2, r3}": b"0e008de8",
        "stm sp!, {r1, r2, r3}": b"0e00ade8",
        "stmib   r3, {r2, r4}": b"140083e9",
        "str SP, [R1]": b"00d081e5",
        "str R1, [R2, R3]": b"031082e7",
        "str R1, [R2, R3, LSL #3]": b"831182e7",
        "str R1, [R2, #3]!": b"0310a2e5",
        "str R1, [R2], #3": b"031082e4",
        "sub r3, r1, r2": b"023041e0",
        "sub r3, r1, #5": b"053041e2",
        "svc #0": b"000000ef",
        "UMULLS R1, R2, R1, R2": b"911292e0",
        "ldr r0, [pc, #-4]": b"04001fe5",
        "mov r1, r2": b"0210a0e1",
        "mov r1, r21, r2": b"0230a1e0",
    },
    CS_MODE_THUMB: {"add r0, r1, r2": b"01eb0200"},
}


def _ks_assemble(asm: str, mode=CS_MODE_ARM) -> bytes:
    """Assemble the given string using Keystone using the specified CPU mode."""
    # Explicitly uses late importing so that Keystone will only be imported if this is called.
    # This lets us avoid requiring installation of Keystone for running tests.
    global ks, ks_thumb
    from keystone import Ks, KS_ARCH_ARM, KS_MODE_ARM, KS_MODE_THUMB

    if ks is None:
        ks = Ks(KS_ARCH_ARM, KS_MODE_ARM)
    if ks_thumb is None:
        ks_thumb = Ks(KS_ARCH_ARM, KS_MODE_THUMB)

    if CS_MODE_ARM == mode:
        ords = ks.asm(asm)[0]
    elif CS_MODE_THUMB == mode:
        ords = ks_thumb.asm(asm)[0]
    else:
        raise Exception(f"bad processor mode for assembly: {mode}")
    if not ords:
        raise Exception(f"bad assembly: {asm}")
    return binascii.hexlify(bytearray(ords))


def assemble(asm: str, mode=CS_MODE_ARM) -> bytes:
    """
    Assemble the given string.
    
    An assembly cache is first checked, and if there is no entry there, then Keystone is used.
    """
    if asm in assembly_cache[mode]:
        return binascii.unhexlify(assembly_cache[mode][asm])
    return binascii.unhexlify(_ks_assemble(asm, mode=mode))


def emulate_next(cpu):
    "Read the next instruction and emulate it with Unicorn "
    cpu.decode_instruction(cpu.PC)
    emu = UnicornEmulator(cpu)
    emu.emulate(cpu.instruction)
    return emu


def itest(asm):
    def instr_dec(assertions_func):
        @wraps(assertions_func)
        def wrapper(self):
            self._setupCpu(asm)
            emulate_next(self.cpu)
            assertions_func(self)

        return wrapper

    return instr_dec


def itest_setregs(*preds):
    def instr_dec(custom_func):
        @wraps(custom_func)
        def wrapper(self):
            for p in preds:
                dest, src = p.split("=")

                try:
                    src = int(src, 0)
                except ValueError:
                    pass

                self.rf.write(dest.upper(), src)
            custom_func(self)

        return wrapper

    return instr_dec


def itest_custom(asm):
    def instr_dec(custom_func):
        @wraps(custom_func)
        def wrapper(self):
            self._setupCpu(asm)
            custom_func(self)

        return wrapper

    return instr_dec


class Armv7UnicornInstructions(unittest.TestCase):
    """
    Import all of the tests from ARM, but execute with Unicorn to verify that
    all semantics match.
    """

    _multiprocess_can_split_ = True

    def setUp(self):
        self.cpu = Cpu(Memory32())
        self.mem = self.cpu.memory
        self.rf = self.cpu.regfile

    def _setupCpu(self, asm, mode=CS_MODE_ARM):
        self.code = self.mem.mmap(0x1000, 0x1000, "rwx")
        self.data = self.mem.mmap(0xD000, 0x1000, "rw")
        self.stack = self.mem.mmap(0xF000, 0x1000, "rw")
        start = self.code + 4
        self.mem.write(start, assemble(asm, mode))
        self.rf.write("PC", start)
        self.rf.write("SP", self.stack + 0x1000)
        self.cpu.mode = mode

    def _checkFlagsNZCV(self, n, z, c, v):
        self.assertEqual(self.rf.read("APSR_N"), n)
        self.assertEqual(self.rf.read("APSR_Z"), z)
        self.assertEqual(self.rf.read("APSR_C"), c)
        self.assertEqual(self.rf.read("APSR_V"), v)

    # MOV

    @itest("mov r0, 0x0")
    def test_mov_imm_min(self):
        self.assertEqual(self.rf.read("R0"), 0x0)

    @itest("mov r0, 42")
    def test_mov_imm_norm(self):
        self.assertEqual(self.rf.read("R0"), 42)

    @itest("mov r0, 0x100")
    def test_mov_imm_modified_imm_min(self):
        self.assertEqual(self.rf.read("R0"), 0x100)

    @itest("mov r0, 0xff000000")
    def test_mov_imm_modified_imm_max(self):
        self.assertEqual(self.rf.read("R0"), 0xFF000000)

    @itest_custom("mov r0, r1")
    def test_mov_immreg(self):
        self.rf.write("R1", 0)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R0"), 0)

    @itest_custom("mov r0, r1")
    def test_mov_immreg1(self):
        self.rf.write("R1", 2 ** 32)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R0"), 0)

    @itest_custom("mov r0, r1")
    def test_mov_immreg2(self):
        self.rf.write("R1", 0xFFFFFFFF)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R0"), 0xFFFFFFFF)

    @itest_custom("mov r0, r1")
    def test_mov_immreg3(self):
        self.rf.write("R1", 42)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R0"), 42)

    # MOVW

    @itest("movw r0, 0")
    def test_movw_imm_min(self):
        self.assertEqual(self.rf.read("R0"), 0x0)

    @itest("movw r0, 0xffff")
    def test_movw_imm_max(self):
        self.assertEqual(self.rf.read("R0"), 0xFFFF)

    # MOVS

    @itest_custom("movs r0, 0")
    def test_movs_imm_min(self):
        pre_c = self.rf.read("APSR_C")
        pre_v = self.rf.read("APSR_V")
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R0"), 0)
        self._checkFlagsNZCV(0, 1, pre_c, pre_v)

    @itest_custom("movs r0, 42")
    def test_movs_imm_norm(self):
        pre_c = self.rf.read("APSR_C")
        pre_v = self.rf.read("APSR_V")
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R0"), 42)
        self._checkFlagsNZCV(0, 0, pre_c, pre_v)

    @itest_custom("movs r0, 0x100")
    def test_movs_imm_modified_imm_min(self):
        pre_c = self.rf.read("APSR_C")
        pre_v = self.rf.read("APSR_V")
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R0"), 0x100)
        self._checkFlagsNZCV(0, 0, pre_c, pre_v)

    @itest_custom("movs r0, 0xff000000")
    def test_movs_imm_modified_imm_max(self):
        pre_v = self.rf.read("APSR_V")
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R0"), 0xFF000000)
        self._checkFlagsNZCV(1, 0, 1, pre_v)

    @itest_custom("movs r0, 0x0e000000")
    def test_movs_imm_modified_imm_sans_carry(self):
        pre_v = self.rf.read("APSR_V")
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R0"), 0x0E000000)
        self._checkFlagsNZCV(0, 0, 0, pre_v)

    @itest_custom("movs r0, r1")
    def test_movs_reg(self):
        self.rf.write("R1", 0)
        pre_c = self.rf.read("APSR_C")
        pre_v = self.rf.read("APSR_V")
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R0"), 0)
        self._checkFlagsNZCV(0, 1, pre_c, pre_v)

    @itest_custom("movs r0, r1")
    def test_movs_reg1(self):
        self.rf.write("R1", 2 ** 32)
        pre_c = self.rf.read("APSR_C")
        pre_v = self.rf.read("APSR_V")
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R0"), 0)
        self._checkFlagsNZCV(0, 1, pre_c, pre_v)

    @itest_custom("movs r0, r1")
    def test_movs_reg2(self):
        self.rf.write("R1", 2 ** 32 - 1)
        pre_c = self.rf.read("APSR_C")
        pre_v = self.rf.read("APSR_V")
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R0"), 2 ** 32 - 1)
        self._checkFlagsNZCV(1, 0, pre_c, pre_v)

    @itest_custom("movs r0, r1")
    def test_movs_reg3(self):
        self.rf.write("R1", 42)
        pre_c = self.rf.read("APSR_C")
        pre_v = self.rf.read("APSR_V")
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R0"), 42)
        self._checkFlagsNZCV(0, 0, pre_c, pre_v)

    # ADD

    @itest_custom("add r3, r1, 55")
    def test_add_imm_norm(self):
        self.rf.write("R1", 44)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 99)

    @itest_custom("add r3, r1, 0x100")
    def test_add_imm_mod_imm_min(self):
        self.rf.write("R1", 44)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 44 + 0x100)

    @itest_custom("add r3, r1, 0xff000000")
    def test_add_imm_mod_imm_max(self):
        self.rf.write("R1", 44)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 44 + 0xFF000000)

    @itest_custom("add r3, r1, 0x1000000")
    def test_add_imm_carry(self):
        self.rf.write("R1", 0xFF000001)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 1)

    @itest_custom("add r3, r1, 0x1")
    def test_add_imm_overflow(self):
        self.rf.write("R1", (2 ** 31 - 1))
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 0x80000000)

    @itest_custom("add r3, r1, r2")
    def test_add_reg_norm(self):
        self.rf.write("R1", 44)
        self.rf.write("R2", 55)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 99)

    @itest_custom("add r3, r1, r2")
    def test_add_reg_mod_imm_min(self):
        self.rf.write("R1", 44)
        self.rf.write("R2", 0x100)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 44 + 0x100)

    @itest_custom("add r3, r1, r2")
    def test_add_reg_mod_imm_max(self):
        self.rf.write("R1", 44)
        self.rf.write("R2", 0xFF000000)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 44 + 0xFF000000)

    @itest_custom("add r3, r1, r2")
    def test_add_reg_carry(self):
        self.rf.write("R1", 0x1000000)
        self.rf.write("R2", 0xFF000001)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 1)

    @itest_custom("add r3, r1, r2")
    def test_add_reg_overflow(self):
        self.rf.write("R1", (2 ** 31 - 1))
        self.rf.write("R2", 1)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), (1 << 31))

    @itest_custom("add r3, r1, r2, lsl #3")
    def test_add_reg_sft_lsl(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 0x1)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), (1 << 3))

    @itest_custom("add r3, r1, r2, lsr #3")
    def test_add_reg_sft_lsr(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 0x8)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), (0x8 >> 3))

    @itest_custom("add r3, r1, r2, asr #3")
    def test_add_reg_sft_asr(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 0x80000000)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 0xF0000000)

    @itest_custom("add r3, r1, r2, asr #3")
    def test_add_reg_sft_asr2(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 0x40000000)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), (0x40000000 >> 3))

    @itest_custom("add r3, r1, r2, ror #3")
    def test_add_reg_sft_ror_norm(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 0x8)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 0x1)

    @itest_custom("add r3, r1, r2, ror #3")
    def test_add_reg_sft_ror(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 0x3)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 0x60000000)

    @itest_custom("adc r3, r1, r2")
    @itest_setregs("R1=1", "R2=2", "APSR_C=1")
    def test_adc_basic(self):
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 4)

    @itest_custom("adc r3, r1, r2, ror #3")
    @itest_setregs("R1=1", "R2=2", "APSR_C=1")
    def test_adc_reg_sft_ror(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 0x3)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 0x60000001)

    # TODO what is shifter_carry_out in the manual, A8-291? it gets set to
    # Bit[0] presumably, but i have no clue what it is. Not mentioned again in
    # manual.
    @itest_custom("add r3, r1, r2, rrx")
    def test_add_reg_sft_rrx(self):
        self.rf.write("APSR_C", 0x0)
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 2 ** 32 - 1)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 2 ** 31 - 1)

    @itest_custom("add r3, r1, r2, rrx")
    def test_add_reg_sft_rrx2(self):
        self.rf.write("APSR_C", 0x1)
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 2 ** 32 - 1)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 2 ** 32 - 1)

    @itest_custom("add r3, r1, r2, lsl r4")
    def test_add_reg_sft_lsl_reg(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R4", 0x3)
        self.rf.write("R2", 0x1)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), (1 << 3))

    @itest_custom("add r3, r1, r2, lsr r4")
    def test_add_reg_sft_lsr_reg(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R4", 0x3)
        self.rf.write("R2", 0x8)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), (0x8 >> 3))

    @itest_custom("add r3, r1, r2, asr r4")
    def test_add_reg_sft_asr_reg(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R4", 0x3)
        self.rf.write("R2", 0x80000000)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 0xF0000000)

    @itest_custom("add r3, r1, r2, asr r4")
    def test_add_reg_sft_asr2_reg(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R4", 0x3)
        self.rf.write("R2", 0x40000000)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), (0x40000000 >> 3))

    @itest_custom("add r3, r1, r2, ror r4")
    def test_add_reg_sft_ror_norm_reg(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R4", 0x3)
        self.rf.write("R2", 0x8)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 1)

    @itest_custom("add r3, r1, r2, ror r4")
    def test_add_reg_sft_ror_reg(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R4", 0x3)
        self.rf.write("R2", 0x3)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 0x60000000)

    @itest_custom("add r3, r1, r2, rrx")
    def test_add_reg_sft_rrx_reg(self):
        self.rf.write("R1", 0x0)
        self.rf.write("APSR_C", 0x0)
        self.rf.write("R2", 2 ** 32 - 1)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 2 ** 31 - 1)

    @itest_custom("add r3, r1, r2, rrx")
    def test_add_reg_sft_rrx2_reg(self):
        self.rf.write("R1", 0x0)
        self.rf.write("APSR_C", 0x1)
        self.rf.write("R2", 2 ** 32 - 1)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 2 ** 32 - 1)

    # ADDS

    @itest_custom("adds r3, r1, 55")
    def test_adds_imm_norm(self):
        self.rf.write("R1", 44)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 99)
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_custom("adds r3, r1, 0x100")
    def test_adds_imm_mod_imm_min(self):
        self.rf.write("R1", 44)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 44 + 0x100)
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_custom("adds r3, r1, 0xff000000")
    def test_adds_imm_mod_imm_max(self):
        self.rf.write("R1", 44)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 44 + 0xFF000000)
        self._checkFlagsNZCV(1, 0, 0, 0)

    @itest_custom("adds r3, r1, 0x1000000")
    def test_adds_imm_carry(self):
        self.rf.write("R1", 0xFF000001)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 1)
        self._checkFlagsNZCV(0, 0, 1, 0)

    @itest_custom("adds r3, r1, 0x80000000")
    def test_adds_imm_carry_overflow(self):
        self.rf.write("R1", 0x80000001)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 1)
        self._checkFlagsNZCV(0, 0, 1, 1)

    @itest_custom("adds r3, r1, 0x1")
    def test_adds_imm_overflow(self):
        self.rf.write("R1", (2 ** 31 - 1))
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 0x80000000)
        self._checkFlagsNZCV(1, 0, 0, 1)

    @itest_custom("adds r3, r3, 0x0")
    def test_adds_imm_zf(self):
        self.rf.write("R3", 0)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 0)
        self._checkFlagsNZCV(0, 1, 0, 0)

    @itest_custom("adds r3, r1, r2")
    def test_adds_reg_norm(self):
        self.rf.write("R1", 44)
        self.rf.write("R2", 55)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 99)
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_custom("adds r3, r1, r2")
    def test_adds_reg_mod_imm_min(self):
        self.rf.write("R1", 44)
        self.rf.write("R2", 0x100)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 44 + 0x100)
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_custom("adds r3, r1, r2")
    def test_adds_reg_mod_imm_max(self):
        self.rf.write("R1", 44)
        self.rf.write("R2", 0xFF000000)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 44 + 0xFF000000)
        self._checkFlagsNZCV(1, 0, 0, 0)

    @itest_custom("adds r3, r1, r2")
    def test_adds_reg_carry(self):
        self.rf.write("R1", 0x1000000)
        self.rf.write("R2", 0xFF000001)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 1)
        self._checkFlagsNZCV(0, 0, 1, 0)

    @itest_custom("adds r3, r1, r2")
    def test_adds_reg_overflow(self):
        self.rf.write("R1", (2 ** 31 - 1))
        self.rf.write("R2", 1)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), (1 << 31))
        self._checkFlagsNZCV(1, 0, 0, 1)

    @itest_custom("adds r3, r1, r2")
    def test_adds_reg_carry_overflow(self):
        self.rf.write("R1", 0x80000001)
        self.rf.write("R2", 0x80000000)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 1)
        self._checkFlagsNZCV(0, 0, 1, 1)

    @itest_custom("adds r3, r1, r2")
    def test_adds_reg_zf(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 0x0)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 0)
        self._checkFlagsNZCV(0, 1, 0, 0)

    @itest_custom("adds r3, r1, r2, asr #3")
    def test_adds_reg_sft_asr(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 0x80000000)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 0xF0000000)
        self._checkFlagsNZCV(1, 0, 0, 0)

    @itest_custom("adds r3, r1, r2, asr #3")
    def test_adds_reg_sft_asr2(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 0x40000000)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), (0x40000000 >> 3))
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_custom("adds r3, r1, r2, rrx")
    def test_adds_reg_sft_rrx(self):
        self.rf.write("APSR_C", 0x0)
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 2 ** 32 - 1)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 2 ** 31 - 1)
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_custom("adds r3, r1, r2, rrx")
    def test_adds_reg_sft_rrx2(self):
        self.rf.write("APSR_C", 0x1)
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 2 ** 32 - 1)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 2 ** 32 - 1)
        self._checkFlagsNZCV(1, 0, 0, 0)

    # LDR imm

    @itest_custom("ldr r1, [sp]")
    def test_ldr_imm_off_none(self):
        self.cpu.stack_push(42)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 42)

    @itest_custom("ldr r1, [sp, #4]")
    def test_ldr_imm_off_pos(self):
        self.cpu.stack_push(42)
        self.cpu.stack_push(41)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 42)

    @itest_custom("ldr r1, [sp, #-4]")
    def test_ldr_imm_off_neg(self):
        self.cpu.stack_push(42)
        self.cpu.stack_push(41)
        self.cpu.STACK += 4
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 41)

    @itest_custom("ldr r1, [sp, #4]!")
    def test_ldr_imm_preind_pos(self):
        self.cpu.stack_push(42)
        self.cpu.stack_push(41)
        pre_stack = self.cpu.STACK
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 42)
        self.assertEqual(self.rf.read("SP"), pre_stack + 4)

    @itest_custom("ldr r1, [sp, #-4]!")
    def test_ldr_imm_preind_neg(self):
        self.cpu.stack_push(42)
        self.cpu.stack_push(41)
        self.cpu.STACK += 4
        pre_stack = self.cpu.STACK
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 41)
        self.assertEqual(self.rf.read("SP"), pre_stack - 4)

    @itest_custom("ldr r1, [sp], #5")
    def test_ldr_imm_postind_pos(self):
        self.cpu.stack_push(42)
        pre_stack = self.cpu.STACK
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 42)
        self.assertEqual(self.rf.read("SP"), pre_stack + 5)

    @itest_custom("ldr r1, [sp], #-5")
    def test_ldr_imm_postind_neg(self):
        self.cpu.stack_push(42)
        pre_stack = self.cpu.STACK
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 42)
        self.assertEqual(self.rf.read("SP"), pre_stack - 5)

    # LDR reg

    @itest_custom("ldr r1, [sp, r2]")
    def test_ldr_reg_off(self):
        self.cpu.regfile.write("R2", 4)
        self.cpu.stack_push(42)
        self.cpu.stack_push(48)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 42)

    @itest_custom("ldr r1, [sp, -r2]")
    def test_ldr_reg_off_neg(self):
        self.cpu.regfile.write("R2", 4)
        self.cpu.stack_push(42)
        self.cpu.stack_push(48)
        self.cpu.STACK += 4
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 48)

    @itest_custom("ldr r1, [sp, r2, lsl #3]")
    def test_ldr_reg_off_shift(self):
        self.cpu.regfile.write("R2", 1)
        self.cpu.stack_push(42)
        self.cpu.stack_push(48)
        self.cpu.stack_push(40)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 42)

    @itest_custom("ldr r1, [sp, -r2, lsl #3]")
    def test_ldr_reg_off_neg_shift(self):
        self.cpu.regfile.write("R2", 1)
        self.cpu.stack_push(42)
        self.cpu.stack_push(48)
        self.cpu.STACK += 8
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 48)

    @itest_custom("ldr r1, [sp, r2]!")
    def test_ldr_reg_preind(self):
        self.cpu.regfile.write("R2", 4)
        self.cpu.stack_push(42)
        self.cpu.stack_push(48)
        pre_stack = self.cpu.STACK
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 42)
        self.assertEqual(self.rf.read("SP"), pre_stack + 4)

    @itest_custom("ldr r1, [sp, -r2, lsl #3]!")
    def test_ldr_reg_preind_shift(self):
        self.cpu.regfile.write("R2", 1)
        self.cpu.stack_push(42)
        self.cpu.stack_push(48)
        self.cpu.STACK += 8
        pre_stack = self.cpu.STACK
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 48)
        self.assertEqual(self.rf.read("SP"), pre_stack - 8)

    @itest_custom("ldr r1, [sp], r2")
    def test_ldr_reg_postind(self):
        self.cpu.regfile.write("R2", 4)
        self.cpu.stack_push(42)
        pre_stack = self.cpu.STACK
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 42)
        self.assertEqual(self.rf.read("SP"), pre_stack + 4)

    @itest_custom("ldr r1, [sp], -r2, lsl #3")
    def test_ldr_reg_postind_neg_shift(self):
        self.cpu.regfile.write("R2", 1)
        self.cpu.stack_push(42)
        pre_stack = self.cpu.STACK
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 42)
        self.assertEqual(self.rf.read("SP"), pre_stack - 8)

    @itest_custom("pop {r1}")
    def test_pop_one_reg(self):
        self.cpu.stack_push(0x55)
        pre_stack = self.cpu.STACK
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 0x55)
        self.assertEqual(self.rf.read("SP"), pre_stack + 4)

    @itest_custom("pop {r1, r2, r3}")
    def test_pop_multops(self):
        vals = [0x01, 0x55, 0xAA]
        for v in vals:
            self.cpu.stack_push(v)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 0xAA)
        self.assertEqual(self.rf.read("R2"), 0x55)
        self.assertEqual(self.rf.read("R3"), 0x01)

    @itest_custom("push {r1}")
    @itest_setregs("R1=3")
    def test_push_one_reg(self):
        emulate_next(self.cpu)
        self.assertCountEqual(b"".join(self.cpu.stack_peek()), struct.pack("<I", 3))

    @itest_custom("push {r1, r2, r3}")
    @itest_setregs("R1=3", "R2=0x55", "R3=0xffffffff")
    def test_push_multi_reg(self):
        pre_sp = self.cpu.STACK
        emulate_next(self.cpu)
        sp = self.cpu.STACK
        self.assertEqual(self.rf.read("SP"), pre_sp - (3 * 4))
        self.assertCountEqual(b"".join(self.cpu.stack_peek()), struct.pack("<I", 3))
        self.assertEqual(self.cpu.read_int(sp + 4, self.cpu.address_bit_size), 0x55)
        self.assertEqual(self.cpu.read_int(sp + 8, self.cpu.address_bit_size), 0xFFFFFFFF)

    @itest_custom("str SP, [R1]")
    @itest_setregs("R1=0xd000")
    def test_str_basic(self):
        r1 = self.rf.read("R1")
        sp = self.rf.read("SP")
        emulate_next(self.cpu)
        dr1 = self.cpu.read_int(r1, self.cpu.address_bit_size)
        self.assertEqual(sp, dr1)

    @itest_custom("str R1, [R2, R3]")
    @itest_setregs("R1=34", "R2=0xD000", "R3=8")
    def test_str_index(self):
        r1 = self.rf.read("R1")
        r2 = self.rf.read("R2")
        r3 = self.rf.read("R3")
        emulate_next(self.cpu)
        retrieved = self.cpu.read_int(r2 + r3, self.cpu.address_bit_size)
        self.assertEqual(retrieved, r1)

    @itest_custom("str R1, [R2, R3, LSL #3]")
    @itest_setregs("R1=34", "R2=0xD000", "R3=1")
    def test_str_index_w_shift(self):
        r1 = self.rf.read("R1")
        r2 = self.rf.read("R2")
        r3 = self.rf.read("R3")
        r3 = r3 << 3
        emulate_next(self.cpu)
        retrieved = self.cpu.read_int(r2 + r3, self.cpu.address_bit_size)
        self.assertEqual(retrieved, r1)

    @itest_custom("str R1, [R2], #3")
    @itest_setregs("R1=34", "R2=0xD000")
    def test_str_postindex(self):
        r1 = self.rf.read("R1")
        r2 = self.rf.read("R2")
        emulate_next(self.cpu)
        # check store results
        data = self.cpu.read_int(r2, self.cpu.address_bit_size)
        self.assertEqual(data, r1)
        # check writeback results
        new_r2 = self.rf.read("R2")
        self.assertEqual(new_r2, r2 + 3)

    @itest_custom("str R1, [R2, #3]!")
    @itest_setregs("R1=34", "R2=0xD000")
    def test_str_index_writeback(self):
        r1 = self.rf.read("R1")
        r2 = self.rf.read("R2")
        emulate_next(self.cpu)
        # check store results
        data = self.cpu.read_int(r2 + 3, self.cpu.address_bit_size)
        self.assertEqual(data, r1)
        # check writeback results
        new_r2 = self.rf.read("R2")
        self.assertEqual(new_r2, r2 + 3)

    # BL

    @itest_custom("bl 0x170")
    def test_bl(self):
        pre_pc = self.rf.read("PC")
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("PC"), pre_pc + 0x170)
        self.assertEqual(self.rf.read("LR"), pre_pc + 4)

    @itest_custom("bl #-4")
    def test_bl_neg(self):
        pre_pc = self.rf.read("PC")
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("PC"), pre_pc - 4)
        self.assertEqual(self.rf.read("LR"), pre_pc + 4)

    # CMP

    @itest_setregs("R0=3")
    @itest("cmp r0, 3")
    def test_cmp_eq(self):
        self._checkFlagsNZCV(0, 1, 1, 0)

    @itest_setregs("R0=3")
    @itest("cmp r0, 5")
    def test_cmp_lt(self):
        self._checkFlagsNZCV(1, 0, 0, 0)

    @itest_setregs("R0=3")
    @itest("cmp r0, 2")
    def test_cmp_gt(self):
        self._checkFlagsNZCV(0, 0, 1, 0)

    @itest_setregs("R0=0")
    @itest("cmp r0, 0")
    def test_cmp_carry(self):
        self._checkFlagsNZCV(0, 1, 1, 0)

    @itest_setregs("R0=0x40000000")
    @itest("cmp r0, 0xa0000000")
    def test_cmp_ovf(self):
        self._checkFlagsNZCV(1, 0, 0, 1)

    @itest_setregs("R0=0x80000000")
    @itest("cmp r0, 0x40000000")
    def test_cmp_carry_ovf(self):
        self._checkFlagsNZCV(0, 0, 1, 1)

    # CLZ

    @itest_custom("clz r1, r2")
    @itest_setregs("R2=0xFFFF")
    def test_clz_sixteen_zeroes(self):
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 16)

    @itest_custom("clz r1, r2")
    @itest_setregs("R2=0")
    def test_clz_all_zero(self):
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), self.cpu.address_bit_size)

    @itest_custom("clz r1, r2")
    @itest_setregs("R2=0xffffffff")
    def test_clz_no_leading_zeroes(self):
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 0)

    @itest_custom("clz r1, r2")
    @itest_setregs("R2=0x7fffffff")
    def test_clz_one_leading_zero(self):
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 1)

    @itest_custom("clz r1, r2")
    @itest_setregs("R2=0x7f7fffff")
    def test_clz_lead_zero_then_more_zeroes(self):
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 1)

    @itest_custom("sub r3, r1, r2")
    @itest_setregs("R1=4", "R2=2")
    def test_sub_basic(self):
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 2)

    @itest_custom("sub r3, r1, #5")
    @itest_setregs("R1=10")
    def test_sub_imm(self):
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 5)

    @itest_custom("sbc r3, r1, #5")
    @itest_setregs("R1=10")
    def test_sbc_imm(self):
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R3"), 4)

    @itest_custom("ldm sp, {r1, r2, r3}")
    def test_ldm(self):
        self.cpu.stack_push(0x41414141)
        self.cpu.stack_push(2)
        self.cpu.stack_push(42)
        pre_sp = self.cpu.STACK
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 42)
        self.assertEqual(self.rf.read("R2"), 2)
        self.assertEqual(self.rf.read("R3"), 0x41414141)
        self.assertEqual(self.cpu.STACK, pre_sp)

    @itest_custom("ldm sp!, {r1, r2, r3}")
    def test_ldm_wb(self):
        self.cpu.stack_push(0x41414141)
        self.cpu.stack_push(2)
        self.cpu.stack_push(42)
        pre_sp = self.cpu.STACK
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 42)
        self.assertEqual(self.rf.read("R2"), 2)
        self.assertEqual(self.rf.read("R3"), 0x41414141)
        self.assertEqual(self.cpu.STACK, pre_sp + 12)

    @itest_setregs("R1=2", "R2=42", "R3=0x42424242")
    @itest_custom("stm sp, {r1, r2, r3}")
    def test_stm(self):
        self.cpu.STACK -= 12
        pre_sp = self.cpu.STACK
        emulate_next(self.cpu)
        self.assertEqual(self.cpu.read_int(pre_sp, self.cpu.address_bit_size), 2)
        self.assertEqual(self.cpu.read_int(pre_sp + 4, self.cpu.address_bit_size), 42)
        self.assertEqual(self.cpu.read_int(pre_sp + 8, self.cpu.address_bit_size), 0x42424242)
        self.assertEqual(self.cpu.STACK, pre_sp)

    @itest_setregs("R1=2", "R2=42", "R3=0x42424242")
    @itest_custom("stm sp!, {r1, r2, r3}")
    def test_stm_wb(self):
        self.cpu.STACK -= 12
        pre_sp = self.cpu.STACK
        emulate_next(self.cpu)
        self.assertEqual(self.cpu.read_int(pre_sp, self.cpu.address_bit_size), 2)
        self.assertEqual(self.cpu.read_int(pre_sp + 4, self.cpu.address_bit_size), 42)
        self.assertEqual(self.cpu.read_int(pre_sp + 8, self.cpu.address_bit_size), 0x42424242)
        self.assertEqual(self.cpu.STACK, pre_sp + 12)

    @itest_custom("stmib   r3, {r2, r4}")
    @itest_setregs("R1=1", "R2=2", "R4=4", "R3=0xd100")
    def test_stmib_basic(self):
        emulate_next(self.cpu)
        addr = self.rf.read("R3")
        self.assertEqual(self.cpu.read_int(addr + 4, self.cpu.address_bit_size), 2)
        self.assertEqual(self.cpu.read_int(addr + 8, self.cpu.address_bit_size), 4)

    @itest_custom("bx r1")
    @itest_setregs("R1=0x1008")
    def test_bx_basic(self):
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("PC"), 0x1008)

    @itest_custom("bx r1")
    @itest_setregs("R1=0x1009")
    def test_bx_thumb(self):
        pre_pc = self.rf.read("PC")
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("PC"), pre_pc + 4)

    # ORR

    @itest_custom("orr r2, r3, #5")
    @itest_setregs("R3=0x1000")
    def test_orr_imm(self):
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R2"), 0x1005)

    @itest_custom("orrs r2, r3")
    @itest_setregs("R2=0x5", "R3=0x80000000")
    def test_orrs_imm_flags(self):
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R2"), 0x80000005)
        self.assertEqual(self.rf.read("APSR_N"), True)

    @itest_custom("orr r2, r3")
    @itest_setregs("R2=0x5", "R3=0x80000000")
    def test_orr_reg_w_flags(self):
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R2"), 0x80000005)
        # self.assertEqual(self.rf.read('APSR_N'), 1)

    @itest_custom("orr r2, r3, r4")
    @itest_setregs("R3=0x5", "R4=0x80000000")
    def test_orr_reg_two_op(self):
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R2"), 0x80000005)
        # self.assertEqual(self.rf.read('APSR_N'), 1)

    @itest_custom("orr r2, r3, r4, LSL #4")
    @itest_setregs("R3=0x5", "R4=0xF")
    def test_orr_reg_two_op_shifted(self):
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R2"), 0xF5)

    # EOR

    @itest_custom("eor r2, r3, #5")
    @itest_setregs("R3=0xA")
    def test_eor_imm(self):
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R2"), 0xF)

    @itest_custom("eors r2, r3")
    @itest_setregs("R2=0xAA", "R3=0x80000000")
    def test_eors_imm_flags(self):
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R2"), 0x800000AA)
        self.assertEqual(self.rf.read("APSR_N"), True)

    @itest_custom("eors r2, r3")
    @itest_setregs("R2=0x5", "R3=0x80000005")
    def test_eor_reg_w_flags(self):
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R2"), 0x80000000)
        self.assertEqual(self.rf.read("APSR_N"), 1)

    @itest_custom("eor r2, r3, r4")
    @itest_setregs("R3=0x80000005", "R4=0x80000005")
    def test_eor_reg_two_op(self):
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R2"), 0)

    @itest_custom("eor r2, r3, r4, LSL #4")
    @itest_setregs("R3=0x55", "R4=0x5")
    def test_eor_reg_two_op_shifted(self):
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R2"), 0x5)

    # LDRH - see also LDR tests

    @itest_custom("ldrh r1, [sp]")
    def test_ldrh_imm_off_none(self):
        self.cpu.stack_push(0x41410041)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 0x41)

    @itest_custom("ldrh r1, [sp, r2]")
    @itest_setregs("R2=4")
    def test_ldrh_reg_off(self):
        self.cpu.stack_push(0x41410041)
        self.cpu.stack_push(48)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 0x41)

    # LDRSH - see also LDR tests

    @itest_custom("ldrsh r1, [sp]")
    def test_ldrsh_imm_off_none_neg(self):
        self.cpu.stack_push(0x2FF0F)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 0xFFFFFF0F)

    @itest_custom("ldrsh r1, [sp]")
    def test_ldrsh_imm_off_none_pos(self):
        self.cpu.stack_push(0xFF0FFF)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 0x0FFF)

    @itest_custom("ldrsh r1, [sp, r2]")
    @itest_setregs("R2=4")
    def test_ldrsh_reg_off_neg(self):
        self.cpu.stack_push(0x2FF0F)
        self.cpu.stack_push(48)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 0xFFFFFF0F)

    @itest_custom("ldrsh r1, [sp, r2]")
    @itest_setregs("R2=4")
    def test_ldrsh_reg_off_pos(self):
        self.cpu.stack_push(0xFF0FFF)
        self.cpu.stack_push(48)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 0x0FFF)

    # LDRB - see also LDR tests

    @itest_custom("ldrb r1, [sp]")
    def test_ldrb_imm_off_none(self):
        self.cpu.stack_push(0x41)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 0x41)

    @itest_custom("ldrb r1, [sp, r2]")
    @itest_setregs("R2=4")
    def test_ldrb_reg_off(self):
        self.cpu.stack_push(0x41)
        self.cpu.stack_push(48)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 0x41)

    # LDRSB - see also LDR tests

    @itest_custom("ldrsb r1, [sp]")
    def test_ldrsb_imm_off_none_neg(self):
        self.cpu.stack_push(0x2FF)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), Mask(32))

    @itest_custom("ldrsb r1, [sp]")
    def test_ldrsb_imm_off_none_pos(self):
        self.cpu.stack_push(0xFF0F)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 0xF)

    @itest_custom("ldrsb r1, [sp, r2]")
    @itest_setregs("R2=4")
    def test_ldrsb_reg_off_neg(self):
        self.cpu.stack_push(0x2FF)
        self.cpu.stack_push(48)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), Mask(32))

    @itest_custom("ldrsb r1, [sp, r2]")
    @itest_setregs("R2=4")
    def test_ldrsb_reg_off_pos(self):
        self.cpu.stack_push(0xFF0F)
        self.cpu.stack_push(48)
        emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R1"), 0xF)

    # TST
    @itest_setregs("R1=1", "R3=0")
    @itest("tst r3, r1")
    def test_tst(self):
        self._checkFlagsNZCV(0, 1, 0, 0)

    # AND
    @itest_setregs("R2=5")
    @itest("and r2, r2, #1")
    def test_and_imm(self):
        self.assertEqual(self.rf.read("R2"), 1)

    @itest_setregs("R1=5", "R2=3")
    @itest("and r1, r1, r2")
    def test_and_reg(self):
        self.assertEqual(self.rf.read("R1"), 3 & 5)

    @itest_setregs("R1=5", "R2=3", "APSR_C=1")
    @itest("and r1, r1, r2")
    def test_and_reg_carry(self):
        self.assertEqual(self.rf.read("R1"), 3 & 5)
        self.assertEqual(self.rf.read("APSR_C"), 1)

    # svc

    def test_svc(self):
        with self.assertRaises(Interruption):
            self._setupCpu("svc #0")
            emulate_next(self.cpu)

    # lsl

    @itest_setregs("R3=0x11")
    @itest("lsls r4, r3, 1")
    def test_lsl_imm_min(self):
        self.assertEqual(self.rf.read("R4"), 0x11 << 1)
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_setregs("R3=0x11")
    @itest("lsls r4, r3, 31")
    def test_lsl_imm_max(self):
        self.assertEqual(self.rf.read("R4"), 1 << 31)
        self._checkFlagsNZCV(1, 0, 0, 0)

    @itest_setregs("R3=0x11", "R2=0xff01")
    @itest("lsls r4, r3, r2")
    def test_lsl_reg_min(self):
        self.assertEqual(self.rf.read("R4"), 0x11 << 1)
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_setregs("R3=0x11", "R2=0xff1f")
    @itest("lsls r4, r3, r2")
    def test_lsl_reg_max(self):
        self.assertEqual(self.rf.read("R4"), 0x1 << 31)
        self._checkFlagsNZCV(1, 0, 0, 0)

    # lsr
    @itest_setregs("R0=0x1000", "R2=3")
    @itest("lsr r0, r0, r2")
    def test_lsr_reg(self):
        self.assertEqual(self.rf.read("R0"), 0x1000 >> 3)

    @itest_setregs("R0=0x1000")
    @itest("lsr r0, r0, #3")
    def test_lsr_reg_imm(self):
        self.assertEqual(self.rf.read("R0"), 0x1000 >> 3)

    @itest_setregs("R2=29")
    @itest("RSB r2, r2, #31")
    def test_rsb_imm(self):
        # Diverging instruction from trace
        self.assertEqual(self.rf.read("R2"), 2)

    def test_flag_state_continuity(self):
        """If an instruction only partially updates flags, cpu.set_flags should
        ensure unupdated flags are preserved.

        For example:
        r1 = 2**31 - 1
        add r2, r1, 0x1 // overflow = 1
        mov r1, 1
        mov r3, 0
        tst r3, r1 // does not change overflow flag
        // ovf should still be 1
        """

        self.rf.write("R1", (2 ** 31 - 1))
        self._setupCpu("adds r2, r1, #0x1")
        emulate_next(self.cpu)
        self.rf.write("R1", 1)
        self.rf.write("R3", 0)
        self.mem.write(self.cpu.PC, assemble("tst r3, r1"))
        emulate_next(self.cpu)
        self._checkFlagsNZCV(0, 1, 0, 1)

    @itest_setregs("R1=30", "R2=10")
    @itest("MUL R1, R2")
    def test_mul_reg(self):
        self.assertEqual(self.rf.read("R1"), 300)

    @itest_setregs("R1=30", "R2=10")
    @itest("MUL R3, R1, R2")
    def test_mul_reg_w_dest(self):
        self.assertEqual(self.rf.read("R3"), 300)

    @itest_setregs("R2=10", "R3=15", "R4=7")
    @itest("MLA R1, R2, R3, R4")
    def test_mla_reg(self):
        self.assertEqual(self.rf.read("R1"), 157)

    @itest_setregs("R1=0xFF")
    @itest("BIC R2, R1, #0x10")
    def test_bic_reg_imm(self):
        self.assertEqual(self.rf.read("R2"), 0xEF)

    @itest_setregs("R1=0x1008")
    @itest("BLX R1")
    def test_blx_reg(self):
        self.assertEqual(self.rf.read("PC"), 0x1008)
        self.assertEqual(self.rf.read("LR"), 0x1008)

    @itest_setregs("R1=0x1009")
    @itest("BLX R1")
    def test_blx_reg_thumb(self):
        self.assertEqual(self.rf.read("PC"), 0x1008)
        self.assertEqual(self.rf.read("LR"), 0x1008)

    @itest_setregs("R1=0xffffffff", "R2=2")
    @itest("UMULLS R1, R2, R1, R2")
    def test_umull(self):
        mul = 0xFFFFFFFF * 2
        pre_c = self.rf.read("APSR_C")
        pre_v = self.rf.read("APSR_V")
        self.assertEqual(self.rf.read("R1"), mul & Mask(32))
        self.assertEqual(self.rf.read("R2"), mul >> 32)
        self._checkFlagsNZCV(0, 0, pre_c, pre_v)

    @itest_setregs("R1=2", "R2=2")
    @itest("UMULLS R1, R2, R1, R2")
    def test_umull_still32(self):
        mul = 2 * 2
        pre_c = self.rf.read("APSR_C")
        pre_v = self.rf.read("APSR_V")
        self.assertEqual(self.rf.read("R1"), mul & Mask(32))
        self.assertEqual(self.rf.read("R2"), mul >> 32)
        self._checkFlagsNZCV(0, 0, pre_c, pre_v)

    @itest_setregs("R1=0xfffffffe", "R2=0xfffffffe")
    @itest("UMULLS R1, R2, R1, R2")
    def test_umull_max(self):
        mul = 0xFFFFFFFE ** 2
        pre_c = self.rf.read("APSR_C")
        pre_v = self.rf.read("APSR_V")
        self.assertEqual(self.rf.read("R1"), mul & Mask(32))
        self.assertEqual(self.rf.read("R2"), mul >> 32)
        self._checkFlagsNZCV(1, 0, pre_c, pre_v)

    @itest_setregs("R1=3", "R2=0")
    @itest("UMULLS R1, R2, R1, R2")
    def test_umull_z(self):
        mul = 3 * 0
        pre_c = self.rf.read("APSR_C")
        pre_v = self.rf.read("APSR_V")
        self.assertEqual(self.rf.read("R1"), mul & Mask(32))
        self.assertEqual(self.rf.read("R2"), (mul >> 32) & Mask(32))
        self._checkFlagsNZCV(0, 1, pre_c, pre_v)

    def test_thumb_mode_emulation(self):
        asm = "add r0, r1, r2"
        self._setupCpu(asm, mode=CS_MODE_THUMB)
        self.rf.write("R0", 0)
        self.rf.write("R1", 0x1234)
        self.rf.write("R2", 0x5678)
        emu = emulate_next(self.cpu)
        self.assertEqual(self.rf.read("R0"), 0x1234 + 0x5678)
        self.assertEqual(emu._emu.query(UC_QUERY_MODE), UC_MODE_THUMB)


class UnicornConcretization(unittest.TestCase):
    """
    Test the ability of Unicorn-based emulation to correctly request certain
    locations to be concretized.
    """

    cpu = None
    state = None

    @classmethod
    def get_state(cls):
        if cls.cpu is None:
            constraints = ConstraintSet()
            dirname = os.path.dirname(__file__)
            platform = linux.SLinux(os.path.join(dirname, "binaries", "basic_linux_amd64"))
            cls.state = State(constraints, platform)
            cls.cpu = platform._mk_proc("armv7")
        return (cls.cpu, cls.state)

    def setUp(self):
        self.cpu, self.state = self.__class__.get_state()
        self.mem = self.cpu.memory
        self.rf = self.cpu.regfile
        for r in self.cpu.regfile.canonical_registers:
            self.cpu.write_register(r, 0)

    def _setupCpu(self, asm):
        self.code = self.mem.mmap(0x1000, 0x1000, "rwx")
        self.data = self.mem.mmap(0xD000, 0x1000, "rw")
        self.stack = self.mem.mmap(0xF000, 0x1000, "rw")
        start = self.code + 4
        self.mem.write(start, assemble(asm))
        self.rf.write("PC", start)
        self.rf.write("SP", self.stack + 0xFFC)

    @itest_custom("ldr r1, [sp]")
    def test_load_symbolic(self):
        self.cpu.STACK -= 4

        val = self.state.symbolicate_buffer("++++", wildcard="+")
        self.cpu.write_bytes(self.rf.read("SP"), val)
        with self.assertRaises(ConcretizeMemory) as e:
            emulate_next(self.cpu)

    @itest_custom("ldr r1, [sp]")
    def test_load_symbolic_correct_address(self):
        self.cpu.STACK -= 4

        val = self.state.symbolicate_buffer("++++", wildcard="+")
        sp = self.rf.read("SP")
        self.cpu.write_bytes(sp, val)
        try:
            emulate_next(self.cpu)
            # Make sure we raise
            self.assertFalse(True)
        except ConcretizeMemory as e:
            sp = self.rf.read("SP")
            self.assertTrue(e.address in range(sp, sp + len(val)))

    @itest_custom("mov r1, r2")
    def test_load_symbolic_from_register(self):
        val = self.state.new_symbolic_value(32)
        self.rf.write("R2", val)

        try:
            emulate_next(self.cpu)
            # Make sure we raise
            self.assertFalse(True)
        except ConcretizeRegister as e:
            self.assertEqual(e.reg_name, "R2")

    def test_arm_constant(self):
        self.code = self.mem.mmap(0x1000, 0x1000, "rwx")
        self.data = self.mem.mmap(0xD000, 0x1000, "rw")
        self.stack = self.mem.mmap(0xF000, 0x1000, "rw")
        start = self.code + 4
        constant = 0x42424242

        asm = "ldr r0, [pc, #-4]"

        code = assemble(asm)
        code += b"\x78\x56\x34\x12"

        self.mem.write(start, code)

        self.rf.write("PC", start)
        self.rf.write("SP", self.stack + 0x1000)

        emulate_next(self.cpu)

        self.assertEqual(self.rf.read("PC"), self.code + 8)
        self.assertEqual(self.rf.read("R0"), 0x12345678)

    @itest_custom("mov r1, r2")
    def test_concretize_register_isnt_consumed(self):
        val = self.state.new_symbolic_value(32)
        self.rf.write("R2", val)

        with self.assertRaises(ConcretizeRegister):
            self.cpu.emulate(self.cpu.decode_instruction(self.cpu.PC))
