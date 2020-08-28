import unittest

import struct
import binascii
from capstone import CS_MODE_THUMB, CS_MODE_ARM
from functools import wraps

from manticore.native.cpu.abstractcpu import ConcretizeRegister
from manticore.native.cpu.arm import Armv7Cpu as Cpu, Mask, Interruption
from manticore.core.smtlib import *
from manticore.core.state import Concretize
from manticore.core.smtlib.solver import Z3Solver
from manticore.native.memory import SMemory32
from manticore.utils.helpers import pickle_dumps

ks = None
ks_thumb = None

import logging

logger = logging.getLogger("ARM_TESTS")
solver = Z3Solver.instance()

# This is a cache of assembled instructions.
# This exists so that Manticore's tests can run without requiring that the
# Keystone dependency be installed.
# If additional test cases are added that require new instructions, this cache
# will need to be updated.
assembly_cache = {
    CS_MODE_ARM: {
        "adc r3, r1, r2": b"0230a1e0",
        "adc r3, r1, #0x18000": b"0639a1e2",
        "adc r3, r1, #24, 20": b"183aa1e2",
        "adc r3, r1, r2, ror #3": b"e231a1e0",
        "add r3, r1, 0x1000000": b"013481e2",
        "add r3, r1, 0x18000": b"063981e2",
        "add r3, r1, 24, 20": b"183a81e2",
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
        "add pc, pc, r1": b"01f08fe0",
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
        "adr r0, #16": b"10008fe2",
        "add r0, PC, #0x10": b"10008fe2",
        "add r0, PC, #1, 28": b"10008fe2",
        "and r2, r2, #1": b"012002e2",
        "and r2, r2, #0x18000": b"062902e2",
        "and r2, r2, #24, 20": b"182a02e2",
        "and r1, r1, r2": b"021001e0",
        "BIC R2, R1, #0x10": b"1020c1e3",
        "BIC R2, R1, #0x18000": b"0629c1e3",
        "BIC R2, R1, #24, 20": b"182ac1e3",
        "bl 0x170": b"5a0000eb",
        "bl #-4": b"fdffffeb",
        "BLX R1": b"31ff2fe1",
        "blx  r1": b"31ff2fe1",
        "bx r1": b"11ff2fe1",
        "clz r1, r2": b"121f6fe1",
        "cmn r0, #0x18000": b"060970e3",
        "cmn r0, #24, 20": b"180a70e3",
        "cmp r0, 0": b"000050e3",
        "cmp r0, 0x40000000": b"010150e3",
        "cmp r0, 3": b"030050e3",
        "cmp r0, #0x18000": b"060950e3",
        "cmp r0, #24, 20": b"180a50e3",
        "cmp r0, 2": b"020050e3",
        "cmp r0, 5": b"050050e3",
        "cmp r0, 0xa0000000": b"0a0250e3",
        "dmb ish": b"5bf07ff5",
        "eor r2, r3, #5": b"052023e2",
        "eor r2, r3, #0x18000": b"062923e2",
        "eor r2, r3, #24, 20": b"182a23e2",
        "eor r2, r3, r4": b"042023e0",
        "eor r2, r3, r4, LSL #4": b"042223e0",
        "eors r2, r3": b"032032e0",
        "adds r2, r1, #0x1": b"012091e2",
        "tst r3, r1": b"010013e1",
        "ldm sp, {r1, r2, r3}": b"0e009de8",
        "ldm sp!, {r1, r2, r3}": b"0e00bde8",
        "ldmda r0!, {r1, r2, r3}": b"0e0030e8",
        "ldmdb r0!, {r1, r2, r3}": b"0e0030e9",
        "ldmia r0!, {r1, r2, r3}": b"0e00b0e8",
        "ldmib r0!, {r1, r2, r3}": b"0e00b0e9",
        "ldr r1, [sp, #-4]": b"04101de5",
        "ldr r1, [sp]": b"00109de5",
        "ldr pc, [sp]": b"00f09de5",
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
        "ldrd r2, [sp]": b"d020cde1",
        "ldrh r1, [sp]": b"b010dde1",
        "ldrh r1, [sp, r2]": b"b2109de1",
        "ldrsb r1, [sp]": b"d010dde1",
        "ldrsb r1, [sp, r2]": b"d2109de1",
        "ldrsh r1, [sp]": b"f010dde1",
        "ldrsh r1, [sp, r2]": b"f2109de1",
        "lsls r2, r2, #0x1f": b"822fb0e1",
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
        "mov r0, #0x18000": b"0609a0e3",
        "mov r0, #24, 20": b"180aa0e3",
        "movs r0, 0": b"0000b0e3",
        "movs r0, 0xff000000": b"ff04b0e3",
        "movs r0, 0x100": b"010cb0e3",
        "movs r0, 0x0e000000": b"0e04b0e3",
        "movs r0, 42": b"2a00b0e3",
        "movs r0, r1": b"0100b0e1",
        "movt R3, #9": b"093040e3",
        "movw r0, 0xffff": b"ff0f0fe3",
        "movw r0, 0": b"000000e3",
        "mrc p15, #0, r2, c13, c0, #3": b"702f1dee",
        "MUL R1, R2": b"910201e0",
        "MUL R3, R1, R2": b"910203e0",
        "mvn r0, #0xFFFFFFFF": b"0000a0e3",
        "mvn r0, #0x0": b"0000e0e3",
        "mvn r0, #0x18000": b"0609e0e3",
        "mvn r0, #24, 20": b"180ae0e3",
        "orr r2, r3, #5": b"052083e3",
        "orr r2, r3, #0x18000": b"062983e3",
        "orr r2, r3, #24, 20": b"182a83e3",
        "orr r2, r3, r4": b"042083e1",
        "orr r2, r3, r4, LSL #4": b"042283e1",
        "orr r2, r3": b"032082e1",
        "orrs r2, r3": b"032092e1",
        "pop {r1, r2, r3}": b"0e00bde8",
        "pop {r1}": b"04109de4",
        "push {r1, r2, r3}": b"0e002de9",
        "push {r1}": b"04102de5",
        "rev r2, r1": b"312fbfe6",
        "RSB r2, r2, #31": b"1f2062e2",
        "RSB r2, r2, #0x18000": b"062962e2",
        "RSB r2, r2, #24, 20": b"182a62e2",
        "RSBS r8, r6, #0": b"008076e2",
        "rsc r3, r1, #0x18000": b"0639e1e2",
        "rsc r3, r1, #24, 20": b"183ae1e2",
        "sbc r3, r1, #5": b"0530c1e2",
        "sbc r3, r1, #0x18000": b"0639c1e2",
        "sbc r3, r1, #24, 20": b"183ac1e2",
        "stm sp, {r1, r2, r3}": b"0e008de8",
        "stm sp!, {r1, r2, r3}": b"0e00ade8",
        "stmda r0!, {r1, r2, r3}": b"0e0020e8",
        "stmdb r0!, {r1, r2, r3}": b"0e0020e9",
        "stmia r0!, {r1, r2, r3}": b"0e00a0e8",
        "stmib r0!, {r1, r2, r3}": b"0e00a0e9",
        "str R2, [R1]": b"002081e5",
        "str SP, [R1]": b"00d081e5",
        "str R1, [R2, R3]": b"031082e7",
        "str R1, [R2, R3, LSL #3]": b"831182e7",
        "str R1, [R2, #3]!": b"0310a2e5",
        "str R1, [R2], #3": b"031082e4",
        "strd R2, [R1]": b"f020c1e1",
        "sub r3, r1, r2": b"023041e0",
        "sub r3, r1, #5": b"053041e2",
        "sub r3, r1, #0x18000": b"063941e2",
        "sub r3, r1, #24, 20": b"183a41e2",
        "svc #0": b"000000ef",
        "sxth r1, r2": b"7210bfe6",
        "sxth r3, r4": b"7430bfe6",
        "sxth r5, r4, ROR #8": b"7454bfe6",
        "teq r3, r1": b"010033e1",
        "teq r3, #0x18000": b"060933e3",
        "teq r3, #24, 20": b"180a33e3",
        "BIC R1, #0x10": b"1010c1e3",
        "tst r3, #0x18000": b"060913e3",
        "tst r3, #24, 20": b"180a13e3",
        "UMULLS R1, R2, R1, R2": b"911292e0",
        "uqsub8 r3, r1, r2": b"f23f61e6",
        "uxtb r1, r2": b"7210efe6",
        "uxth r1, r2": b"7210ffe6",
        "vldmia  r1, {d8, d9, d10}": b"068b91ec",
        "vldmia  r1!, {d8, d9, d10}": b"068bb1ec",
    },
    CS_MODE_THUMB: {
        "adds r0, #4": b"0430",
        "addw r0, r1, #0x2a": b"01f22a00",
        "addw r0, pc, #0x2a": b"0ff22a00",
        "adr r0, #16": b"04a0",
        "asr.w R5, R6, #3": b"4feae605",
        "cbnz r0, #0x2a": b"98b9",
        "cbz r0, #0x2a": b"98b1",
        "cmp r1, #1": b"0129",
        "ite ne": b"14bf",
        "mov r2, r12": b"6246",
        "mov r3, r12": b"6346",
        "mov r4, r12": b"6446",
        "itete ne": b"15bf",
        "mov r1, #1": b"4ff00101",
        "mov r2, #1": b"4ff00102",
        "mov r3, #1": b"4ff00103",
        "mov r4, #4": b"4ff00404",
        "itt ne": b"1cbf",
        "lsl.w r5, r6, #3": b"4feac605",
        "lsr.w R5, R6, #3": b"4fead605",
        "lsr.w R0, R0, R2": b"20fa02f0",
        "orn r2, r2, r5": b"62ea0502",
        "sbcs r0, r3": b"9841",
        "sel r4, r5, r6": b"a5fa86f4",
        "subw r0, r1, #0x2a": b"a1f22a00",
        "subw r0, pc, #0x2a": b"aff22a00",
        "  tst r0, r0\n  beq label\n  bne label\nlabel:\n  nop": b"004200d0ffd100bf",
        "tbb [r0, r1]": b"d0e801f0",
        "tbb [pc, r1]": b"dfe801f0",
        "tbh [r0, r1, lsl #1]": b"d0e811f0",
        "tbh [pc, r1, lsl #1]": b"dfe811f0",
        "adcs r3, r4": b"6341",
        "eor r3, #5": b"83f00503",
        "lsrs r1, r2": b"d140",
        "orr r3, #5": b"43f00503",
        "sub r3, #12": b"a3f10c03",
        "uadd8 r2, r2, r3": b"82fa43f2",
    },
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


class Armv7CpuTest(unittest.TestCase):
    _multiprocess_can_split_ = True

    def setUp(self):
        cs = ConstraintSet()
        self.c = Cpu(SMemory32(cs))
        self.rf = self.c.regfile
        self._setupStack()

    def _setupStack(self):
        self.stack = self.c.memory.mmap(0xF000, 0x1000, "rw")
        self.rf.write("SP", self.stack + 0x1000)

    def test_rd(self):
        self.assertEqual(self.rf.read("R0"), 0)

    def test_rd2(self):
        self.c.STACK = 0x1337
        self.assertEqual(self.rf.read("SP"), 0x1337)

    def test_stack_set_get(self):
        self.c.STACK = 0x1337
        self.assertEqual(self.c.STACK, 0x1337)

    def test_rd3(self):
        self.c.STACK = 0x1337 - 1
        self.assertEqual(self.rf.read("SP"), 0x1336)

    def test_rd4(self):
        self.c.STACK = 0x1337 + 1
        self.assertEqual(self.rf.read("SP"), 0x1338)

    def test_stack_push(self):
        self.c.stack_push(42)
        self.c.stack_push(44)
        self.assertEqual(b"".join(self.c.read(self.c.STACK, 4)), b"\x2c\x00\x00\x00")
        self.assertEqual(b"".join(self.c.read(self.c.STACK + 4, 4)), b"\x2a\x00\x00\x00")

    def test_stack_pop(self):
        v = 0x55
        v_bytes = struct.pack("<I", v)
        self.c.stack_push(v)
        val = self.c.stack_pop()
        self.assertEqual(b"".join(self.c.read(self.c.STACK - 4, 4)), v_bytes)

    def test_stack_peek(self):
        self.c.stack_push(42)
        self.assertEqual(b"".join(self.c.stack_peek()), b"\x2a\x00\x00\x00")

    def test_readwrite_int(self):
        self.c.STACK -= 4
        self.c.write_int(self.c.STACK, 0x4242, 32)
        self.assertEqual(self.c.read_int(self.c.STACK), 0x4242)


def itest_failing(asm):
    def instr_dec(assertions_func):
        @wraps(assertions_func)
        def wrapper(self):
            self._setupCpu(asm)
            self.cpu.instruction = "\x00\x00\x00\x00"
            # self.cpu.execute()
            assertions_func(self)

        return wrapper

    return instr_dec


def itest(asm):
    def instr_dec(assertions_func):
        @wraps(assertions_func)
        def wrapper(self):
            self._setupCpu(asm)
            self.cpu.execute()
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
                except Exception:
                    pass

                self.rf.write(dest.upper(), src)
            custom_func(self)

        return wrapper

    return instr_dec


def itest_custom(asm, mode=CS_MODE_ARM):
    def instr_dec(custom_func):
        @wraps(custom_func)
        def wrapper(self):
            self._setupCpu(asm, mode)
            custom_func(self)

        return wrapper

    return instr_dec


def itest_thumb(asm):
    def instr_dec(assertions_func):
        @wraps(assertions_func)
        def wrapper(self):
            self._setupCpu(asm, mode=CS_MODE_THUMB)
            self.cpu.execute()
            assertions_func(self)

        return wrapper

    return instr_dec


def itest_multiple(asms):
    def instr_dec(assertions_func):
        @wraps(assertions_func)
        def wrapper(self):
            self._setupCpu(asms, mode=CS_MODE_ARM, multiple_insts=True)
            for i in range(len(asms)):
                self.cpu.execute()
            assertions_func(self)

        return wrapper

    return instr_dec


def itest_thumb_multiple(asms):
    def instr_dec(assertions_func):
        @wraps(assertions_func)
        def wrapper(self):
            self._setupCpu(asms, mode=CS_MODE_THUMB, multiple_insts=True)
            for i in range(len(asms)):
                self.cpu.execute()
            assertions_func(self)

        return wrapper

    return instr_dec


class Armv7CpuInstructions(unittest.TestCase):
    def setUp(self):
        cs = ConstraintSet()
        self.cpu = Cpu(SMemory32(cs))
        self.mem = self.cpu.memory
        self.rf = self.cpu.regfile

    def _setupCpu(self, asm, mode=CS_MODE_ARM, multiple_insts=False):
        self.code = self.mem.mmap(0x1000, 0x1000, "rwx")
        self.data = self.mem.mmap(0xD000, 0x1000, "rw")
        self.stack = self.mem.mmap(0xF000, 0x1000, "rw")

        # it doesn't really matter what's the starting address of code
        # as long as it's known and constant for all the tests;
        # we start it at +4 as it is convenient for some tests to use pc-4 reference
        # (see e.g. test_bl_neg test)
        start = self.code + 4
        if multiple_insts:
            offset = 0
            for asm_single in asm:
                asm_inst = assemble(asm_single, mode)
                self.mem.write(start + offset, asm_inst)
                offset += len(asm_inst)
        else:
            self.mem.write(start, assemble(asm, mode))
        self.rf.write("PC", start)
        self.rf.write("SP", self.stack + 0x1000)
        self.cpu.mode = mode

    def _checkFlagsNZCV(self, n, z, c, v):
        self.assertEqual(self.rf.read("APSR_N"), n)
        self.assertEqual(self.rf.read("APSR_Z"), z)
        self.assertEqual(self.rf.read("APSR_C"), c)
        self.assertEqual(self.rf.read("APSR_V"), v)

    # MVN
    @itest("mvn r0, #0x0")
    def test_mvn_imm_min(self):
        self.assertEqual(self.rf.read("R0"), 0xFFFFFFFF)

    @itest("mvn r0, #0xFFFFFFFF")
    def test_mvn_imm_max(self):
        self.assertEqual(self.rf.read("R0"), 0x0)

    @itest("mvn r0, #0x18000")
    def test_mvn_mod_imm_1(self):
        self.assertEqual(self.rf.read("R0"), 0xFFFE7FFF)

    @itest("mvn r0, #24, 20")
    def test_mvn_mod_imm_2(self):
        self.assertEqual(self.rf.read("R0"), 0xFFFE7FFF)

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

    @itest("mov r0, #0x18000")
    def test_mov_mod_imm_1(self):
        self.assertEqual(self.rf.read("R0"), 0x18000)

    @itest("mov r0, #24, 20")
    def test_mov_mod_imm_2(self):
        self.assertEqual(self.rf.read("R0"), 0x18000)

    @itest_custom("mov r0, r1")
    def test_mov_immreg(self):
        self.rf.write("R1", 0)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R0"), 0)

    @itest_custom("mov r0, r1")
    def test_mov_immreg1(self):
        self.rf.write("R1", 2 ** 32)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R0"), 0)

    @itest_custom("mov r0, r1")
    def test_mov_immreg2(self):
        self.rf.write("R1", 0xFFFFFFFF)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R0"), 0xFFFFFFFF)

    @itest_custom("mov r0, r1")
    def test_mov_immreg3(self):
        self.rf.write("R1", 42)
        self.cpu.execute()
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
        self.cpu.execute()
        self.assertEqual(self.rf.read("R0"), 0)
        self._checkFlagsNZCV(0, 1, pre_c, pre_v)

    @itest_custom("movs r0, 42")
    def test_movs_imm_norm(self):
        pre_c = self.rf.read("APSR_C")
        pre_v = self.rf.read("APSR_V")
        self.cpu.execute()
        self.assertEqual(self.rf.read("R0"), 42)
        self._checkFlagsNZCV(0, 0, pre_c, pre_v)

    @itest_custom("movs r0, 0x100")
    def test_movs_imm_modified_imm_min(self):
        pre_c = self.rf.read("APSR_C")
        pre_v = self.rf.read("APSR_V")
        self.cpu.execute()
        self.assertEqual(self.rf.read("R0"), 0x100)
        self._checkFlagsNZCV(0, 0, pre_c, pre_v)

    @itest_custom("movs r0, 0xff000000")
    def test_movs_imm_modified_imm_max(self):
        pre_v = self.rf.read("APSR_V")
        self.cpu.execute()
        self.assertEqual(self.rf.read("R0"), 0xFF000000)
        self._checkFlagsNZCV(1, 0, 1, pre_v)

    @itest_custom("movs r0, 0x0e000000")
    def test_movs_imm_modified_imm_sans_carry(self):
        pre_v = self.rf.read("APSR_V")
        self.cpu.execute()
        self.assertEqual(self.rf.read("R0"), 0x0E000000)
        self._checkFlagsNZCV(0, 0, 0, pre_v)

    @itest_custom("movs r0, r1")
    def test_movs_reg(self):
        self.rf.write("R1", 0)
        pre_c = self.rf.read("APSR_C")
        pre_v = self.rf.read("APSR_V")
        self.cpu.execute()
        self.assertEqual(self.rf.read("R0"), 0)
        self._checkFlagsNZCV(0, 1, pre_c, pre_v)

    @itest_custom("movs r0, r1")
    def test_movs_reg1(self):
        self.rf.write("R1", 2 ** 32)
        pre_c = self.rf.read("APSR_C")
        pre_v = self.rf.read("APSR_V")
        self.cpu.execute()
        self.assertEqual(self.rf.read("R0"), 0)
        self._checkFlagsNZCV(0, 1, pre_c, pre_v)

    @itest_custom("movs r0, r1")
    def test_movs_reg2(self):
        self.rf.write("R1", 2 ** 32 - 1)
        pre_c = self.rf.read("APSR_C")
        pre_v = self.rf.read("APSR_V")
        self.cpu.execute()
        self.assertEqual(self.rf.read("R0"), 2 ** 32 - 1)
        self._checkFlagsNZCV(1, 0, pre_c, pre_v)

    @itest_custom("movs r0, r1")
    def test_movs_reg3(self):
        self.rf.write("R1", 42)
        pre_c = self.rf.read("APSR_C")
        pre_v = self.rf.read("APSR_V")
        self.cpu.execute()
        self.assertEqual(self.rf.read("R0"), 42)
        self._checkFlagsNZCV(0, 0, pre_c, pre_v)

    # ADD

    @itest_custom("add r3, r1, 55")
    def test_add_imm_norm(self):
        self.rf.write("R1", 44)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 99)

    @itest_custom("add r3, r1, 0x100")
    def test_add_imm_mod_imm_min(self):
        self.rf.write("R1", 44)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 44 + 0x100)

    @itest_custom("add r3, r1, 0x18000")
    def test_add_imm_mod_imm_case1(self):
        self.rf.write("R1", 44)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 44 + 0x18000)

    @itest_custom("add r3, r1, 24, 20")
    def test_add_imm_mod_imm_case2(self):
        self.rf.write("R1", 44)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 44 + 0x18000)

    @itest_custom("add r3, r1, 0xff000000")
    def test_add_imm_mod_imm_max(self):
        self.rf.write("R1", 44)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 44 + 0xFF000000)

    @itest_custom("add r3, r1, 0x1000000")
    def test_add_imm_carry(self):
        self.rf.write("R1", 0xFF000001)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 1)

    @itest_custom("add r3, r1, 0x1")
    def test_add_imm_overflow(self):
        self.rf.write("R1", (2 ** 31 - 1))
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 0x80000000)

    @itest_custom("add r3, r1, r2")
    def test_add_reg_norm(self):
        self.rf.write("R1", 44)
        self.rf.write("R2", 55)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 99)

    @itest_custom("add r3, r1, r2")
    def test_add_reg_mod_imm_min(self):
        self.rf.write("R1", 44)
        self.rf.write("R2", 0x100)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 44 + 0x100)

    @itest_custom("add r3, r1, r2")
    def test_add_reg_mod_imm_max(self):
        self.rf.write("R1", 44)
        self.rf.write("R2", 0xFF000000)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 44 + 0xFF000000)

    @itest_custom("add r3, r1, r2")
    def test_add_reg_carry(self):
        self.rf.write("R1", 0x1000000)
        self.rf.write("R2", 0xFF000001)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 1)

    @itest_custom("add r3, r1, r2")
    def test_add_reg_overflow(self):
        self.rf.write("R1", (2 ** 31 - 1))
        self.rf.write("R2", 1)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), (1 << 31))

    @itest_custom("add r3, r1, r2, lsl #3")
    def test_add_reg_sft_lsl(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 0x1)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), (1 << 3))

    @itest_custom("add r3, r1, r2, lsr #3")
    def test_add_reg_sft_lsr(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 0x8)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), (0x8 >> 3))

    @itest_custom("add r3, r1, r2, asr #3")
    def test_add_reg_sft_asr(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 0x80000000)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 0xF0000000)

    @itest_custom("add r3, r1, r2, asr #3")
    def test_add_reg_sft_asr2(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 0x40000000)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), (0x40000000 >> 3))

    @itest_custom("add r3, r1, r2, ror #3")
    def test_add_reg_sft_ror_norm(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 0x8)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 0x1)

    @itest_custom("add r3, r1, r2, ror #3")
    def test_add_reg_sft_ror(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 0x3)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 0x60000000)

    # ADCS
    @itest_setregs("R3=0xfffffff6", "R4=10")
    @itest_thumb("adcs r3, r4")
    def test_thumb_adc_basic(self):
        self.assertEqual(self.rf.read("R3"), 0)

    # ADC
    @itest_custom("adc r3, r1, r2")
    @itest_setregs("R1=1", "R2=2", "APSR_C=1")
    def test_adc_basic(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 4)

    @itest_custom("adc r3, r1, r2, ror #3")
    @itest_setregs("R1=1", "R2=2", "APSR_C=1")
    def test_adc_reg_sft_ror(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 0x3)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 0x60000001)

    @itest_custom("adc r3, r1, #0x18000")
    @itest_setregs("R1=1", "APSR_C=1")
    def test_adc_mod_imm_1(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 0x18002)

    @itest_custom("adc r3, r1, #24, 20")
    @itest_setregs("R1=1", "APSR_C=1")
    def test_adc_mod_imm_2(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 0x18002)

    # TODO what is shifter_carry_out in the manual, A8-291? it gets set to
    # Bit[0] presumably, but i have no clue what it is. Not mentioned again in
    # manual.
    @itest_custom("add r3, r1, r2, rrx")
    def test_add_reg_sft_rrx(self):
        self.rf.write("APSR_C", 0x0)
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 2 ** 32 - 1)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 2 ** 31 - 1)

    @itest_custom("add r3, r1, r2, rrx")
    def test_add_reg_sft_rrx2(self):
        self.rf.write("APSR_C", 0x1)
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 2 ** 32 - 1)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 2 ** 32 - 1)

    @itest_custom("add r3, r1, r2, lsl r4")
    def test_add_reg_sft_lsl_reg(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R4", 0x3)
        self.rf.write("R2", 0x1)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), (1 << 3))

    @itest_custom("add r3, r1, r2, lsr r4")
    def test_add_reg_sft_lsr_reg(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R4", 0x3)
        self.rf.write("R2", 0x8)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), (0x8 >> 3))

    @itest_custom("add r3, r1, r2, asr r4")
    def test_add_reg_sft_asr_reg(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R4", 0x3)
        self.rf.write("R2", 0x80000000)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 0xF0000000)

    @itest_custom("add r3, r1, r2, asr r4")
    def test_add_reg_sft_asr2_reg(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R4", 0x3)
        self.rf.write("R2", 0x40000000)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), (0x40000000 >> 3))

    @itest_custom("add r3, r1, r2, ror r4")
    def test_add_reg_sft_ror_norm_reg(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R4", 0x3)
        self.rf.write("R2", 0x8)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 1)

    @itest_custom("add r3, r1, r2, ror r4")
    def test_add_reg_sft_ror_reg(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R4", 0x3)
        self.rf.write("R2", 0x3)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 0x60000000)

    @itest_custom("add r3, r1, r2, rrx")
    def test_add_reg_sft_rrx_reg(self):
        self.rf.write("R1", 0x0)
        self.rf.write("APSR_C", 0x0)
        self.rf.write("R2", 2 ** 32 - 1)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 2 ** 31 - 1)

    @itest_custom("add r3, r1, r2, rrx")
    def test_add_reg_sft_rrx2_reg(self):
        self.rf.write("R1", 0x0)
        self.rf.write("APSR_C", 0x1)
        self.rf.write("R2", 2 ** 32 - 1)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 2 ** 32 - 1)

    # ADDS

    @itest_custom("adds r3, r1, 55")
    def test_adds_imm_norm(self):
        self.rf.write("R1", 44)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 99)
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_custom("adds r3, r1, 0x100")
    def test_adds_imm_mod_imm_min(self):
        self.rf.write("R1", 44)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 44 + 0x100)
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_custom("adds r3, r1, 0xff000000")
    def test_adds_imm_mod_imm_max(self):
        self.rf.write("R1", 44)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 44 + 0xFF000000)
        self._checkFlagsNZCV(1, 0, 0, 0)

    @itest_custom("adds r3, r1, 0x1000000")
    def test_adds_imm_carry(self):
        self.rf.write("R1", 0xFF000001)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 1)
        self._checkFlagsNZCV(0, 0, 1, 0)

    @itest_custom("adds r3, r1, 0x80000000")
    def test_adds_imm_carry_overflow(self):
        self.rf.write("R1", 0x80000001)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 1)
        self._checkFlagsNZCV(0, 0, 1, 1)

    @itest_custom("adds r3, r1, 0x1")
    def test_adds_imm_overflow(self):
        self.rf.write("R1", (2 ** 31 - 1))
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 0x80000000)
        self._checkFlagsNZCV(1, 0, 0, 1)

    @itest_custom("adds r3, r3, 0x0")
    def test_adds_imm_zf(self):
        self.rf.write("R3", 0)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 0)
        self._checkFlagsNZCV(0, 1, 0, 0)

    @itest_custom("adds r3, r1, r2")
    def test_adds_reg_norm(self):
        self.rf.write("R1", 44)
        self.rf.write("R2", 55)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 99)
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_custom("adds r3, r1, r2")
    def test_adds_reg_mod_imm_min(self):
        self.rf.write("R1", 44)
        self.rf.write("R2", 0x100)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 44 + 0x100)
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_custom("adds r3, r1, r2")
    def test_adds_reg_mod_imm_max(self):
        self.rf.write("R1", 44)
        self.rf.write("R2", 0xFF000000)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 44 + 0xFF000000)
        self._checkFlagsNZCV(1, 0, 0, 0)

    @itest_custom("adds r3, r1, r2")
    def test_adds_reg_carry(self):
        self.rf.write("R1", 0x1000000)
        self.rf.write("R2", 0xFF000001)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 1)
        self._checkFlagsNZCV(0, 0, 1, 0)

    @itest_custom("adds r3, r1, r2")
    def test_adds_reg_overflow(self):
        self.rf.write("R1", (2 ** 31 - 1))
        self.rf.write("R2", 1)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), (1 << 31))
        self._checkFlagsNZCV(1, 0, 0, 1)

    @itest_custom("adds r3, r1, r2")
    def test_adds_reg_carry_overflow(self):
        self.rf.write("R1", 0x80000001)
        self.rf.write("R2", 0x80000000)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 1)
        self._checkFlagsNZCV(0, 0, 1, 1)

    @itest_custom("adds r3, r1, r2")
    def test_adds_reg_zf(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 0x0)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 0)
        self._checkFlagsNZCV(0, 1, 0, 0)

    @itest_custom("adds r3, r1, r2, asr #3")
    def test_adds_reg_sft_asr(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 0x80000000)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 0xF0000000)
        self._checkFlagsNZCV(1, 0, 0, 0)

    @itest_custom("adds r3, r1, r2, asr #3")
    def test_adds_reg_sft_asr2(self):
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 0x40000000)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), (0x40000000 >> 3))
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_custom("adds r3, r1, r2, rrx")
    def test_adds_reg_sft_rrx(self):
        self.rf.write("APSR_C", 0x0)
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 2 ** 32 - 1)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 2 ** 31 - 1)
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_custom("adds r3, r1, r2, rrx")
    def test_adds_reg_sft_rrx2(self):
        self.rf.write("APSR_C", 0x1)
        self.rf.write("R1", 0x0)
        self.rf.write("R2", 2 ** 32 - 1)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 2 ** 32 - 1)
        self._checkFlagsNZCV(1, 0, 0, 0)

    @itest_setregs("R0=0")
    @itest_thumb("adds r0, #4")
    def test_adds_thumb_two_op(self):
        self.assertEqual(self.rf.read("R0"), 4)

    # UADD8

    @itest_setregs("R2=0x00FF00FF", "R3=0x00010002")
    @itest_thumb("uadd8 r2, r2, r3")
    def test_uadd8(self):
        self.assertEqual(self.rf.read("R2"), 1)
        self.assertEqual(self.rf.read("APSR_GE"), 5)

    # LDR imm

    @itest_custom("ldr r1, [sp]")
    def test_ldr_imm_off_none(self):
        self.cpu.stack_push(42)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 42)
        self.assertEqual(self.cpu.mode, CS_MODE_ARM)

    @itest_custom("ldr pc, [sp]")
    def test_ldr_imm_off_none_to_thumb(self):
        self.cpu.stack_push(43)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R15"), 42)
        self.assertEqual(self.cpu.mode, CS_MODE_THUMB)

    @itest_custom("ldr r1, [sp, #4]")
    def test_ldr_imm_off_pos(self):
        self.cpu.stack_push(42)
        self.cpu.stack_push(41)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 42)

    @itest_custom("ldr r1, [sp, #-4]")
    def test_ldr_imm_off_neg(self):
        self.cpu.stack_push(42)
        self.cpu.stack_push(41)
        self.cpu.STACK += 4
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 41)

    @itest_custom("ldr r1, [sp, #4]!")
    def test_ldr_imm_preind_pos(self):
        self.cpu.stack_push(42)
        self.cpu.stack_push(41)
        pre_stack = self.cpu.STACK
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 42)
        self.assertEqual(self.rf.read("SP"), pre_stack + 4)

    @itest_custom("ldr r1, [sp, #-4]!")
    def test_ldr_imm_preind_neg(self):
        self.cpu.stack_push(42)
        self.cpu.stack_push(41)
        self.cpu.STACK += 4
        pre_stack = self.cpu.STACK
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 41)
        self.assertEqual(self.rf.read("SP"), pre_stack - 4)

    @itest_custom("ldr r1, [sp], #5")
    def test_ldr_imm_postind_pos(self):
        self.cpu.stack_push(42)
        pre_stack = self.cpu.STACK
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 42)
        self.assertEqual(self.rf.read("SP"), pre_stack + 5)

    @itest_custom("ldr r1, [sp], #-5")
    def test_ldr_imm_postind_neg(self):
        self.cpu.stack_push(42)
        pre_stack = self.cpu.STACK
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 42)
        self.assertEqual(self.rf.read("SP"), pre_stack - 5)

    # LDR reg

    @itest_custom("ldr r1, [sp, r2]")
    def test_ldr_reg_off(self):
        self.cpu.regfile.write("R2", 4)
        self.cpu.stack_push(42)
        self.cpu.stack_push(48)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 42)

    @itest_custom("ldr r1, [sp, -r2]")
    def test_ldr_reg_off_neg(self):
        self.cpu.regfile.write("R2", 4)
        self.cpu.stack_push(42)
        self.cpu.stack_push(48)
        self.cpu.STACK += 4
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 48)

    @itest_custom("ldr r1, [sp, r2, lsl #3]")
    def test_ldr_reg_off_shift(self):
        self.cpu.regfile.write("R2", 1)
        self.cpu.stack_push(42)
        self.cpu.stack_push(48)
        self.cpu.stack_push(40)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 42)

    @itest_custom("ldr r1, [sp, -r2, lsl #3]")
    def test_ldr_reg_off_neg_shift(self):
        self.cpu.regfile.write("R2", 1)
        self.cpu.stack_push(42)
        self.cpu.stack_push(48)
        self.cpu.STACK += 8
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 48)

    @itest_custom("ldr r1, [sp, r2]!")
    def test_ldr_reg_preind(self):
        self.cpu.regfile.write("R2", 4)
        self.cpu.stack_push(42)
        self.cpu.stack_push(48)
        pre_stack = self.cpu.STACK
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 42)
        self.assertEqual(self.rf.read("SP"), pre_stack + 4)

    @itest_custom("ldr r1, [sp, -r2, lsl #3]!")
    def test_ldr_reg_preind_shift(self):
        self.cpu.regfile.write("R2", 1)
        self.cpu.stack_push(42)
        self.cpu.stack_push(48)
        self.cpu.STACK += 8
        pre_stack = self.cpu.STACK
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 48)
        self.assertEqual(self.rf.read("SP"), pre_stack - 8)

    @itest_custom("ldr r1, [sp], r2")
    def test_ldr_reg_postind(self):
        self.cpu.regfile.write("R2", 4)
        self.cpu.stack_push(42)
        pre_stack = self.cpu.STACK
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 42)
        self.assertEqual(self.rf.read("SP"), pre_stack + 4)

    @itest_custom("ldr r1, [sp], -r2, lsl #3")
    def test_ldr_reg_postind_neg_shift(self):
        self.cpu.regfile.write("R2", 1)
        self.cpu.stack_push(42)
        pre_stack = self.cpu.STACK
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 42)
        self.assertEqual(self.rf.read("SP"), pre_stack - 8)

    @itest_custom("ldrd r2, [sp]")
    def test_ldrd(self):
        r2 = 0x41
        r3 = 0x42
        self.cpu.stack_push(r3)
        self.cpu.stack_push(r2)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R2"), r2)
        self.assertEqual(self.rf.read("R3"), r3)

    @itest_custom("pop {r1}")
    def test_pop_one_reg(self):
        self.cpu.stack_push(0x55)
        pre_stack = self.cpu.STACK
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 0x55)
        self.assertEqual(self.rf.read("SP"), pre_stack + 4)

    @itest_custom("pop {r1, r2, r3}")
    def test_pop_multops(self):
        vals = [0x01, 0x55, 0xAA]
        for v in vals:
            self.cpu.stack_push(v)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 0xAA)
        self.assertEqual(self.rf.read("R2"), 0x55)
        self.assertEqual(self.rf.read("R3"), 0x01)

    @itest_custom("push {r1}")
    @itest_setregs("R1=3")
    def test_push_one_reg(self):
        self.cpu.execute()
        self.assertEqual(b"".join(self.cpu.stack_peek()), struct.pack("<I", 3))

    @itest_custom("push {r1, r2, r3}")
    @itest_setregs("R1=3", "R2=0x55", "R3=0xffffffff")
    def test_push_multi_reg(self):
        pre_sp = self.cpu.STACK
        self.cpu.execute()
        sp = self.cpu.STACK
        self.assertEqual(self.rf.read("SP"), pre_sp - (3 * 4))
        self.assertEqual(b"".join(self.cpu.stack_peek()), struct.pack("<I", 3))
        self.assertEqual(self.cpu.read_int(sp + 4, self.cpu.address_bit_size), 0x55)
        self.assertEqual(self.cpu.read_int(sp + 8, self.cpu.address_bit_size), 0xFFFFFFFF)

    @itest_custom("str SP, [R1]")
    @itest_setregs("R1=0xd000")
    def test_str_basic(self):
        r1 = self.rf.read("R1")
        sp = self.rf.read("SP")
        self.cpu.execute()
        dr1 = self.cpu.read_int(r1, self.cpu.address_bit_size)
        self.assertEqual(sp, dr1)

    @itest_custom("str R1, [R2, R3]")
    @itest_setregs("R1=34", "R2=0xD000", "R3=8")
    def test_str_index(self):
        r1 = self.rf.read("R1")
        r2 = self.rf.read("R2")
        r3 = self.rf.read("R3")
        self.cpu.execute()
        retrieved = self.cpu.read_int(r2 + r3, self.cpu.address_bit_size)
        self.assertEqual(retrieved, r1)

    @itest_custom("str R1, [R2, R3, LSL #3]")
    @itest_setregs("R1=34", "R2=0xD000", "R3=1")
    def test_str_index_w_shift(self):
        r1 = self.rf.read("R1")
        r2 = self.rf.read("R2")
        r3 = self.rf.read("R3")
        r3 = r3 << 3
        self.cpu.execute()
        retrieved = self.cpu.read_int(r2 + r3, self.cpu.address_bit_size)
        self.assertEqual(retrieved, r1)

    @itest_custom("str R1, [R2], #3")
    @itest_setregs("R1=34", "R2=0xD000")
    def test_str_postindex(self):
        r1 = self.rf.read("R1")
        r2 = self.rf.read("R2")
        self.cpu.execute()
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
        self.cpu.execute()
        # check store results
        data = self.cpu.read_int(r2 + 3, self.cpu.address_bit_size)
        self.assertEqual(data, r1)
        # check writeback results
        new_r2 = self.rf.read("R2")
        self.assertEqual(new_r2, r2 + 3)

    @itest_custom("strd R2, [R1]")
    @itest_setregs("R1=0xD000", "R2=34", "R3=35")
    def test_strd(self):
        r1 = self.rf.read("R1")
        r2 = self.rf.read("R2")
        r3 = self.rf.read("R3")
        self.cpu.execute()
        dr2 = self.cpu.read_int(r1, self.cpu.address_bit_size)
        dr3 = self.cpu.read_int(r1 + 4, self.cpu.address_bit_size)
        self.assertEqual(dr2, r2)
        self.assertEqual(dr3, r3)

    @itest_custom("str R2, [R1]")
    @itest_setregs("R1=0xD000", "R2=34")
    def test_str(self):
        r1 = self.rf.read("R1")
        r2 = self.rf.read("R2")
        self.cpu.execute()
        dr2 = self.cpu.read_int(r1, self.cpu.address_bit_size)
        self.assertEqual(dr2, r2)

    # ADR

    @itest_custom("adr r0, #16")
    def test_adr(self):
        pre_pc = self.rf.read("PC")
        self.cpu.execute()
        self.assertEqual(self.rf.read("R0"), (pre_pc + 8) + 16)

    # Note, ARM ARM says that the following is an alternative encoding for a form of ADR
    @itest_custom("add r0, PC, #0x10")
    def test_adr_mod_imm_1(self):
        pre_pc = self.rf.read("PC")
        self.cpu.execute()
        self.assertEqual(self.rf.read("R0"), (pre_pc + 8) + 0x10)

    # Note, ARM ARM says that the following is an alternative encoding for a form of ADR
    @itest_custom("add r0, PC, #1, 28")
    def test_adr_mod_imm_2(self):
        pre_pc = self.rf.read("PC")
        self.cpu.execute()
        self.assertEqual(self.rf.read("R0"), (pre_pc + 8) + 0x10)

    @itest_custom("adr r0, #16", mode=CS_MODE_THUMB)
    def test_adr_thumb(self):
        pre_pc = self.rf.read("PC")
        self.cpu.execute()
        self.assertEqual(self.rf.read("R0"), (pre_pc + 4) + 16)  # adr is 4 bytes long

    # ADDW

    @itest_setregs("R1=0x1234")
    @itest_thumb("addw r0, r1, #0x2a")
    def test_addw(self):
        self.assertEqual(self.rf.read("R0"), 0x1234 + 0x2A)

    @itest_custom("addw r0, pc, #0x2a", mode=CS_MODE_THUMB)
    def test_addw_pc_relative(self):
        pre_pc = self.rf.read("PC")
        self.cpu.execute()
        self.assertEqual(self.rf.read("R0"), (pre_pc + 4) + 0x2A)  # addw is 4 bytes long

    # SUBW

    @itest_setregs("R1=0x1234")
    @itest_thumb("subw r0, r1, #0x2a")
    def test_subw(self):
        self.assertEqual(self.rf.read("R0"), 0x1234 - 0x2A)

    @itest_custom("subw r0, pc, #0x2a", mode=CS_MODE_THUMB)
    def test_subw_pc_relative(self):
        pre_pc = self.rf.read("PC")
        self.cpu.execute()
        self.assertEqual(self.rf.read("R0"), (pre_pc + 4) - 0x2A)  # subw is 4 bytes long

    # BL

    @itest_custom("bl 0x170")
    def test_bl(self):
        pre_pc = self.rf.read("PC")
        self.cpu.execute()
        self.assertEqual(self.rf.read("PC"), pre_pc + 0x170)
        self.assertEqual(self.rf.read("LR"), pre_pc + 4)

    @itest_custom("bl #-4")
    def test_bl_neg(self):
        pre_pc = self.rf.read("PC")
        self.cpu.execute()
        self.assertEqual(self.rf.read("PC"), pre_pc - 4)
        self.assertEqual(self.rf.read("LR"), pre_pc + 4)

    # CBZ/CBNZ

    @itest_setregs("R0=0")
    @itest_custom("cbz r0, #0x2a", mode=CS_MODE_THUMB)
    def test_cbz_taken(self):
        pre_pc = self.rf.read("PC")
        self.cpu.execute()
        self.assertEqual(self.rf.read("PC"), pre_pc + 0x2A)

    @itest_setregs("R0=1")
    @itest_custom("cbz r0, #0x2a", mode=CS_MODE_THUMB)
    def test_cbz_not_taken(self):
        pre_pc = self.rf.read("PC")
        self.cpu.execute()
        self.assertEqual(self.rf.read("PC"), pre_pc + 2)  # cbz is 2 bytes long

    @itest_setregs("R0=1")
    @itest_custom("cbnz r0, #0x2a", mode=CS_MODE_THUMB)
    def test_cbnz_taken(self):
        pre_pc = self.rf.read("PC")
        self.cpu.execute()
        self.assertEqual(self.rf.read("PC"), pre_pc + 0x2A)

    @itest_setregs("R0=0")
    @itest_custom("cbnz r0, #0x2a", mode=CS_MODE_THUMB)
    def test_cbnz_not_taken(self):
        pre_pc = self.rf.read("PC")
        self.cpu.execute()
        self.assertEqual(self.rf.read("PC"), pre_pc + 2)  # cbnz is 2 bytes long

    # TBB/TBH

    @itest_setregs("R0=0xd000", "R1=1")
    @itest_custom("tbb [r0, r1]", mode=CS_MODE_THUMB)
    def test_tbb(self):
        # Write the table of offsets at 0xd000 (R0)
        # Index is 1 (R1), offset will be 2 x 21 = 42
        for i, offset in enumerate([11, 21, 31]):
            self.mem.write(0xD000 + i, struct.pack("<B", offset))

        pre_pc = self.rf.read("PC")
        self.cpu.execute()
        self.assertEqual(self.rf.read("PC"), (pre_pc + 4) + 42)  # tbb is 4 bytes long

    @itest_setregs("R1=1")
    @itest_custom("tbb [pc, r1]", mode=CS_MODE_THUMB)
    def test_tbb_pc_relative(self):
        # Write the table of offsets after the instruction
        # Index is 1 (R1), offset will be 2 x 21 = 42
        for i, offset in enumerate([11, 21, 31]):
            self.mem.write(self.cpu.PC + 4 + i, struct.pack("<B", offset))

        pre_pc = self.rf.read("PC")
        self.cpu.execute()
        self.assertEqual(self.rf.read("PC"), (pre_pc + 4) + 42)  # tbb is 4 bytes long

    @itest_setregs("R0=0xd000", "R1=1")
    @itest_custom("tbh [r0, r1, lsl #1]", mode=CS_MODE_THUMB)
    def test_tbh(self):
        # Write the table of offsets at 0xd000 (R0)
        # Index is 1 (R1), offset will be 2 x 21 = 42
        for i, offset in enumerate([11, 21, 31]):
            self.mem.write(0xD000 + i * 2, struct.pack("<H", offset))

        pre_pc = self.rf.read("PC")
        self.cpu.execute()
        self.assertEqual(self.rf.read("PC"), (pre_pc + 4) + 42)  # tbh is 4 bytes long

    @itest_setregs("R1=1")
    @itest_custom("tbh [pc, r1, lsl #1]", mode=CS_MODE_THUMB)
    def test_tbh_pc_relative(self):
        # Write the table of offsets after the instruction
        # Index is 1 (R1), offset will be 2 x 21 = 42
        for i, offset in enumerate([11, 21, 31]):
            self.mem.write(self.cpu.PC + 4 + i * 2, struct.pack("<H", offset))

        pre_pc = self.rf.read("PC")
        self.cpu.execute()
        self.assertEqual(self.rf.read("PC"), (pre_pc + 4) + 42)  # tbh is 4 bytes long

    # CMN

    @itest_setregs("R0=-0x18000")
    @itest("cmn r0, #0x18000")
    def test_cmn_eq_mod_imm_1(self):
        self._checkFlagsNZCV(0, 1, 1, 0)

    @itest_setregs("R0=-0x18000")
    @itest("cmn r0, #24, 20")
    def test_cmn_eq_mod_imm_2(self):
        self._checkFlagsNZCV(0, 1, 1, 0)

    # CMP

    @itest_setregs("R0=3")
    @itest("cmp r0, 3")
    def test_cmp_eq(self):
        self._checkFlagsNZCV(0, 1, 1, 0)

    @itest_setregs("R0=0x18000")
    @itest("cmp r0, #0x18000")
    def test_cmp_eq_mod_imm_1(self):
        self._checkFlagsNZCV(0, 1, 1, 0)

    @itest_setregs("R0=0x18000")
    @itest("cmp r0, #24, 20")
    def test_cmp_eq_mod_imm_2(self):
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
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 16)

    @itest_custom("clz r1, r2")
    @itest_setregs("R2=0")
    def test_clz_all_zero(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), self.cpu.address_bit_size)

    @itest_custom("clz r1, r2")
    @itest_setregs("R2=0xffffffff")
    def test_clz_no_leading_zeroes(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 0)

    @itest_custom("clz r1, r2")
    @itest_setregs("R2=0x7fffffff")
    def test_clz_one_leading_zero(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 1)

    @itest_custom("clz r1, r2")
    @itest_setregs("R2=0x7f7fffff")
    def test_clz_lead_zero_then_more_zeroes(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 1)

    # SUB

    @itest_custom("sub r3, r1, r2")
    @itest_setregs("R1=4", "R2=2")
    def test_sub_basic(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 2)

    @itest_setregs("R3=0xE")
    @itest_thumb("sub r3, #12")
    def test_thumb_sub_basic(self):
        self.assertEqual(self.rf.read("R3"), 2)

    @itest_custom("sub r3, r1, #5")
    @itest_setregs("R1=10")
    def test_sub_imm(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 5)

    @itest_custom("sub r3, r1, #0x18000")
    @itest_setregs("R1=0x18000")
    def test_sub_mod_imm_1(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 0)

    @itest_custom("sub r3, r1, #24, 20")
    @itest_setregs("R1=0x18000")
    def test_sub_mod_imm_2(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 0)

    @itest_custom("uqsub8 r3, r1, r2")
    @itest_setregs("R1=0x04030201", "R2=0x01010101")
    def test_uqsub8_concrete(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 0x03020100)

    @itest_custom("uqsub8 r3, r1, r2")
    @itest_setregs("R1=0x05040302", "R2=0x07050101")
    def test_uqsub8_concrete_saturated(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 0x00000201)

    @itest_custom("uqsub8 r3, r1, r2")
    @itest_setregs("R2=0x01010101")
    def test_uqsub8_sym(self):
        op1 = self.cpu.memory.constraints.new_bitvec(32, "op1")
        self.cpu.memory.constraints.add(op1 >= 0x04030201)
        self.cpu.memory.constraints.add(op1 < 0x04030204)
        self.cpu.R1 = op1
        self.cpu.execute()
        all_vals = solver.get_all_values(self.cpu.memory.constraints, self.cpu.R3)
        self.assertIn(0x03020100, all_vals)

    # RSC

    @itest_custom("rsc r3, r1, #0x18000")
    @itest_setregs("R1=0x18000", "APSR_C=1")
    def test_rsc_mod_imm_1(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 0)

    @itest_custom("rsc r3, r1, #0x18000")
    @itest_setregs("R1=0x17fff", "APSR_C=0")
    def test_rsc_mod_imm_2(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 0)

    @itest_custom("rsc r3, r1, #24, 20")
    @itest_setregs("R1=0x18000", "APSR_C=1")
    def test_rsc_mod_imm_3(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 0)

    @itest_custom("rsc r3, r1, #24, 20")
    @itest_setregs("R1=0x17fff", "APSR_C=0")
    def test_rsc_mod_imm_4(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 0)

    # SBC

    @itest_custom("sbc r3, r1, #5")
    @itest_setregs("R1=10")
    def test_sbc_imm(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 4)

    @itest_setregs("R0=0", "R3=0xffffffff")
    @itest_thumb("sbcs r0, r3")
    def test_sbc_thumb(self):
        self.assertEqual(self.rf.read("R0"), 0)

    @itest_custom("sbc r3, r1, #0x18000")
    @itest_setregs("R1=0x18010", "APSR_C=1")
    def test_sbc_mod_imm_1(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 0x10)

    @itest_custom("sbc r3, r1, #0x18000")
    @itest_setregs("R1=0x18010", "APSR_C=0")
    def test_sbc_mod_imm_2(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 0xF)

    @itest_custom("sbc r3, r1, #24, 20")
    @itest_setregs("R1=0x18010", "APSR_C=1")
    def test_sbc_mod_imm_3(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 0x10)

    @itest_custom("sbc r3, r1, #24, 20")
    @itest_setregs("R1=0x18010", "APSR_C=0")
    def test_sbc_mod_imm_4(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R3"), 0xF)

    # LDM/LDMIB/LDMDA/LDMDB

    @itest_custom("ldm sp, {r1, r2, r3}")
    def test_ldm(self):
        self.cpu.stack_push(0x41414141)
        self.cpu.stack_push(2)
        self.cpu.stack_push(42)
        pre_sp = self.cpu.STACK
        self.cpu.execute()
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
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 42)
        self.assertEqual(self.rf.read("R2"), 2)
        self.assertEqual(self.rf.read("R3"), 0x41414141)
        self.assertEqual(self.cpu.STACK, pre_sp + 12)

    @itest_setregs("R0=0xd100")
    @itest_custom("ldmia r0!, {r1, r2, r3}")
    def test_ldmia(self):
        # IA - Increment After
        # so the first value read should be at 0xd100
        self.cpu.write_int(0xD100 + 0x0, 1, self.cpu.address_bit_size)
        self.cpu.write_int(0xD100 + 0x4, 2, self.cpu.address_bit_size)
        self.cpu.write_int(0xD100 + 0x8, 3, self.cpu.address_bit_size)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 1)
        self.assertEqual(self.rf.read("R2"), 2)
        self.assertEqual(self.rf.read("R3"), 3)
        # and the writeback should be 0xd10c
        self.assertEqual(self.rf.read("R0"), 0xD100 + 0xC)

    @itest_setregs("R0=0xd100")
    @itest_custom("ldmib r0!, {r1, r2, r3}")
    def test_ldmib(self):
        # IB - Increment Before
        # so the first value read should be at 0xd104
        self.cpu.write_int(0xD100 + 0x4, 1, self.cpu.address_bit_size)
        self.cpu.write_int(0xD100 + 0x8, 2, self.cpu.address_bit_size)
        self.cpu.write_int(0xD100 + 0xC, 3, self.cpu.address_bit_size)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 1)
        self.assertEqual(self.rf.read("R2"), 2)
        self.assertEqual(self.rf.read("R3"), 3)
        # and the writeback should be 0xd10c
        self.assertEqual(self.rf.read("R0"), 0xD100 + 0xC)

    @itest_setregs("R0=0xd100")
    @itest_custom("ldmda r0!, {r1, r2, r3}")
    def test_ldmda(self):
        # DA - Decrement After
        # so the first value read should be at 0xd100
        self.cpu.write_int(0xD100 - 0x0, 1, self.cpu.address_bit_size)
        self.cpu.write_int(0xD100 - 0x4, 2, self.cpu.address_bit_size)
        self.cpu.write_int(0xD100 - 0x8, 3, self.cpu.address_bit_size)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 1)
        self.assertEqual(self.rf.read("R2"), 2)
        self.assertEqual(self.rf.read("R3"), 3)
        # and the writeback should be 0xd0f8
        self.assertEqual(self.rf.read("R0"), 0xD100 - 0xC)

    @itest_setregs("R0=0xd100")
    @itest_custom("ldmdb r0!, {r1, r2, r3}")
    def test_ldmdb(self):
        # DB - Decrement Before
        # so the first value read should be at 0xd0fc
        self.cpu.write_int(0xD100 - 0x4, 1, self.cpu.address_bit_size)
        self.cpu.write_int(0xD100 - 0x8, 2, self.cpu.address_bit_size)
        self.cpu.write_int(0xD100 - 0xC, 3, self.cpu.address_bit_size)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 1)
        self.assertEqual(self.rf.read("R2"), 2)
        self.assertEqual(self.rf.read("R3"), 3)
        # and the writeback should be 0xd0f8
        self.assertEqual(self.rf.read("R0"), 0xD100 - 0xC)

    # STM/STMIB/STMDA/STMDB

    @itest_setregs("R1=42", "R2=2", "R3=0x42424242")
    @itest_custom("stm sp, {r1, r2, r3}")
    def test_stm(self):
        self.cpu.STACK -= 12
        pre_sp = self.cpu.STACK
        self.cpu.execute()
        self.assertEqual(self.cpu.read_int(pre_sp, self.cpu.address_bit_size), 42)
        self.assertEqual(self.cpu.read_int(pre_sp + 4, self.cpu.address_bit_size), 2)
        self.assertEqual(self.cpu.read_int(pre_sp + 8, self.cpu.address_bit_size), 0x42424242)
        self.assertEqual(self.cpu.STACK, pre_sp)

    @itest_setregs("R1=42", "R2=2", "R3=0x42424242")
    @itest_custom("stm sp!, {r1, r2, r3}")
    def test_stm_wb(self):
        self.cpu.STACK -= 12
        pre_sp = self.cpu.STACK
        self.cpu.execute()
        self.assertEqual(self.cpu.read_int(pre_sp, self.cpu.address_bit_size), 42)
        self.assertEqual(self.cpu.read_int(pre_sp + 4, self.cpu.address_bit_size), 2)
        self.assertEqual(self.cpu.read_int(pre_sp + 8, self.cpu.address_bit_size), 0x42424242)
        self.assertEqual(self.cpu.STACK, pre_sp + 12)

    @itest_setregs("R0=0xd100", "R1=1", "R2=2", "R3=3")
    @itest_custom("stmia r0!, {r1, r2, r3}")
    def test_stmia(self):
        # IA = Increment After
        self.cpu.execute()
        # so the first value written should be at 0xd100
        self.assertEqual(self.cpu.read_int(0xD100 + 0x0, self.cpu.address_bit_size), 1)
        self.assertEqual(self.cpu.read_int(0xD100 + 0x4, self.cpu.address_bit_size), 2)
        self.assertEqual(self.cpu.read_int(0xD100 + 0x8, self.cpu.address_bit_size), 3)
        # and the writeback should be 0xd100c
        self.assertEqual(self.rf.read("R0"), 0xD100 + 0xC)

    @itest_setregs("R0=0xd100", "R1=1", "R2=2", "R3=3")
    @itest_custom("stmib r0!, {r1, r2, r3}")
    def test_stmib(self):
        # IB = Increment Before
        self.cpu.execute()
        # so the first value written should be at 0xd104
        self.assertEqual(self.cpu.read_int(0xD100 + 0x4, self.cpu.address_bit_size), 1)
        self.assertEqual(self.cpu.read_int(0xD100 + 0x8, self.cpu.address_bit_size), 2)
        self.assertEqual(self.cpu.read_int(0xD100 + 0xC, self.cpu.address_bit_size), 3)
        # and the writeback should be 0xd100c
        self.assertEqual(self.rf.read("R0"), 0xD100 + 0xC)

    @itest_setregs("R0=0xd100", "R1=1", "R2=2", "R3=3")
    @itest_custom("stmda r0!, {r1, r2, r3}")
    def test_stmda(self):
        # DA = Decrement After
        self.cpu.execute()
        # so the first value written should be at 0xd100
        self.assertEqual(self.cpu.read_int(0xD100 - 0x0, self.cpu.address_bit_size), 1)
        self.assertEqual(self.cpu.read_int(0xD100 - 0x4, self.cpu.address_bit_size), 2)
        self.assertEqual(self.cpu.read_int(0xD100 - 0x8, self.cpu.address_bit_size), 3)
        # and the writeback should be 0xd0f8
        self.assertEqual(self.rf.read("R0"), 0xD100 - 0xC)

    @itest_setregs("R0=0xd100", "R1=1", "R2=2", "R3=3")
    @itest_custom("stmdb r0!, {r1, r2, r3}")
    def test_stmdb(self):
        # DB = Decrement Before
        self.cpu.execute()
        # so the first value written should be at 0xd0fc
        self.assertEqual(self.cpu.read_int(0xD100 - 0x4, self.cpu.address_bit_size), 1)
        self.assertEqual(self.cpu.read_int(0xD100 - 0x8, self.cpu.address_bit_size), 2)
        self.assertEqual(self.cpu.read_int(0xD100 - 0xC, self.cpu.address_bit_size), 3)
        # and the writeback should be 0xd0f8
        self.assertEqual(self.rf.read("R0"), 0xD100 - 0xC)

    # BX

    @itest_custom("bx r1")
    @itest_setregs("R1=0x1008")
    def test_bx_basic(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("PC"), 0x1008)
        self.assertEqual(self.cpu.mode, CS_MODE_ARM)

    @itest_custom("bx r1")
    @itest_setregs("R1=0x1009")
    def test_bx_thumb(self):
        pre_pc = self.rf.read("PC")
        self.cpu.execute()
        self.assertEqual(self.rf.read("PC"), pre_pc + 4)
        self.assertEqual(self.cpu.mode, CS_MODE_THUMB)

    # ORR

    @itest_custom("orr r2, r3, #5")
    @itest_setregs("R3=0x1000")
    def test_orr_imm(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R2"), 0x1005)

    @itest_setregs("R3=0x1000")
    @itest_thumb("orr r3, #5")
    def test_thumb_orr_imm(self):
        self.assertEqual(self.rf.read("R3"), 0x1005)

    @itest_custom("orr r2, r3, #0x18000")
    @itest_setregs("R3=0x1000")
    def test_orr_mod_imm_1(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R2"), 0x19000)

    @itest_custom("orr r2, r3, #24, 20")
    @itest_setregs("R3=0x1000")
    def test_orr_mod_imm_2(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R2"), 0x19000)

    @itest_custom("orrs r2, r3")
    @itest_setregs("R2=0x5", "R3=0x80000000")
    def test_orrs_imm_flags(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R2"), 0x80000005)
        self.assertEqual(self.rf.read("APSR_N"), True)

    @itest_custom("orr r2, r3")
    @itest_setregs("R2=0x5", "R3=0x80000000")
    def test_orr_reg_w_flags(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R2"), 0x80000005)
        # self.assertEqual(self.rf.read('APSR_N'), 1)

    @itest_custom("orr r2, r3, r4")
    @itest_setregs("R3=0x5", "R4=0x80000000")
    def test_orr_reg_two_op(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R2"), 0x80000005)
        # self.assertEqual(self.rf.read('APSR_N'), 1)

    @itest_custom("orr r2, r3, r4, LSL #4")
    @itest_setregs("R3=0x5", "R4=0xF")
    def test_orr_reg_two_op_shifted(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R2"), 0xF5)

    # ORN
    @itest_setregs("R2=0x0", "R5=0xFFFFFFFA")
    @itest_thumb("orn r2, r2, r5")
    def test_orn(self):
        self.assertEqual(self.rf.read("R2"), 0x5)

    # EOR

    @itest_custom("eor r2, r3, #5")
    @itest_setregs("R3=0xA")
    def test_eor_imm(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R2"), 0xF)

    @itest_setregs("R3=0xA")
    @itest_thumb("eor r3, #5")
    def test_thumb_eor_imm(self):
        self.assertEqual(self.rf.read("R3"), 0xF)

    @itest_custom("eors r2, r3")
    @itest_setregs("R2=0xAA", "R3=0x80000000")
    def test_eors_imm_flags(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R2"), 0x800000AA)
        self.assertEqual(self.rf.read("APSR_N"), True)

    @itest_custom("eors r2, r3")
    @itest_setregs("R2=0x5", "R3=0x80000005")
    def test_eor_reg_w_flags(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R2"), 0x80000000)
        self.assertEqual(self.rf.read("APSR_N"), 1)

    @itest_custom("eor r2, r3, r4")
    @itest_setregs("R3=0x80000005", "R4=0x80000005")
    def test_eor_reg_two_op(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R2"), 0)

    @itest_custom("eor r2, r3, r4, LSL #4")
    @itest_setregs("R3=0x55", "R4=0x5")
    def test_eor_reg_two_op_shifted(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R2"), 0x5)

    @itest_custom("eor r2, r3, #0x18000")
    @itest_setregs("R3=0xA")
    def test_eor_mod_imm_1(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R2"), 0x1800A)

    @itest_custom("eor r2, r3, #24, 20")
    @itest_setregs("R3=0xA")
    def test_eor_mod_imm_2(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read("R2"), 0x1800A)

    # LDRH - see also LDR tests

    @itest_custom("ldrh r1, [sp]")
    def test_ldrh_imm_off_none(self):
        self.cpu.stack_push(0x41410041)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 0x41)

    @itest_custom("ldrh r1, [sp, r2]")
    @itest_setregs("R2=4")
    def test_ldrh_reg_off(self):
        self.cpu.stack_push(0x41410041)
        self.cpu.stack_push(48)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 0x41)

    # LDRSH - see also LDR tests

    @itest_custom("ldrsh r1, [sp]")
    def test_ldrsh_imm_off_none_neg(self):
        self.cpu.stack_push(0x2FF0F)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 0xFFFFFF0F)

    @itest_custom("ldrsh r1, [sp]")
    def test_ldrsh_imm_off_none_pos(self):
        self.cpu.stack_push(0xFF0FFF)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 0x0FFF)

    @itest_custom("ldrsh r1, [sp, r2]")
    @itest_setregs("R2=4")
    def test_ldrsh_reg_off_neg(self):
        self.cpu.stack_push(0x2FF0F)
        self.cpu.stack_push(48)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 0xFFFFFF0F)

    @itest_custom("ldrsh r1, [sp, r2]")
    @itest_setregs("R2=4")
    def test_ldrsh_reg_off_pos(self):
        self.cpu.stack_push(0xFF0FFF)
        self.cpu.stack_push(48)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 0x0FFF)

    # LDRB - see also LDR tests

    @itest_custom("ldrb r1, [sp]")
    def test_ldrb_imm_off_none(self):
        self.cpu.stack_push(0x41)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 0x41)

    @itest_custom("ldrb r1, [sp, r2]")
    @itest_setregs("R2=4")
    def test_ldrb_reg_off(self):
        self.cpu.stack_push(0x41)
        self.cpu.stack_push(48)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 0x41)

    # LDRSB - see also LDR tests

    @itest_custom("ldrsb r1, [sp]")
    def test_ldrsb_imm_off_none_neg(self):
        self.cpu.stack_push(0x2FF)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), Mask(32))

    @itest_custom("ldrsb r1, [sp]")
    def test_ldrsb_imm_off_none_pos(self):
        self.cpu.stack_push(0xFF0F)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 0xF)

    @itest_custom("ldrsb r1, [sp, r2]")
    @itest_setregs("R2=4")
    def test_ldrsb_reg_off_neg(self):
        self.cpu.stack_push(0x2FF)
        self.cpu.stack_push(48)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), Mask(32))

    @itest_custom("ldrsb r1, [sp, r2]")
    @itest_setregs("R2=4")
    def test_ldrsb_reg_off_pos(self):
        self.cpu.stack_push(0xFF0F)
        self.cpu.stack_push(48)
        self.cpu.execute()
        self.assertEqual(self.rf.read("R1"), 0xF)

    # TST
    @itest_setregs("R1=1", "R3=0")
    @itest("tst r3, r1")
    def test_tst_1(self):
        self._checkFlagsNZCV(0, 1, 0, 0)

    @itest_setregs("R1=1", "R3=1")
    @itest("tst r3, r1")
    def test_tst_2(self):
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_setregs("R1=1", "R3=3")
    @itest("tst r3, r1")
    def test_tst_3(self):
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_setregs("R3=0")
    @itest("tst r3, #0x18000")
    def test_tst_mod_imm_1(self):
        self._checkFlagsNZCV(0, 1, 0, 0)

    @itest_setregs("R3=0")
    @itest("tst r3, #24, 20")
    def test_tst_mod_imm_2(self):
        self._checkFlagsNZCV(0, 1, 0, 0)

    # TEQ
    @itest_setregs("R1=1", "R3=0")
    @itest("teq r3, r1")
    def test_teq_1(self):
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_setregs("R1=1", "R3=1")
    @itest("teq r3, r1")
    def test_teq_2(self):
        self._checkFlagsNZCV(0, 1, 0, 0)

    @itest_setregs("R3=0")
    @itest("teq r3, #0x18000")
    def test_teq_mod_imm_1(self):
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_setregs("R3=0x18000")
    @itest("teq r3, #0x18000")
    def test_teq_mod_imm_2(self):
        self._checkFlagsNZCV(0, 1, 0, 0)

    @itest_setregs("R3=0")
    @itest("teq r3, #24, 20")
    def test_teq_mod_imm_3(self):
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_setregs("R3=0x18000")
    @itest("teq r3, #24, 20")
    def test_teq_mod_imm_4(self):
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

    @itest_setregs("R2=5")
    @itest("and r2, r2, #0x18000")
    def test_and_mod_imm_1(self):
        self.assertEqual(self.rf.read("R2"), 0)

    @itest_setregs("R2=5")
    @itest("and r2, r2, #24, 20")
    def test_and_mod_imm_2(self):
        self.assertEqual(self.rf.read("R2"), 0)

    # svc

    def test_svc(self):
        with self.assertRaises(Interruption):
            self._setupCpu("svc #0")
            self.cpu.execute()

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

    @itest_setregs("R2=0xffffffff")
    @itest("lsls r2, r2, #0x1f")
    def test_lsl_imm_carry(self):
        self.assertEqual(self.cpu.R2, 0x1 << 31)
        self._checkFlagsNZCV(1, 0, 1, 0)

    @itest_setregs("R5=1", "R6=2")
    @itest_thumb("lsl.w r5, r6, #3")
    def test_lslw_thumb(self):
        """thumb mode specific behavior"""
        self.assertEqual(self.cpu.R5, 0x2 << 3)

    # lsr
    @itest_setregs("R0=0x1000", "R2=3")
    @itest("lsr r0, r0, r2")
    def test_lsr_reg(self):
        self.assertEqual(self.rf.read("R0"), 0x1000 >> 3)

    @itest_setregs("R0=0x1000")
    @itest("lsr r0, r0, #3")
    def test_lsr_reg_imm(self):
        self.assertEqual(self.rf.read("R0"), 0x1000 >> 3)

    @itest_setregs("R1=0", "R2=3")
    @itest_thumb("lsrs r1, r2")
    def test_thumb_lsrs(self):
        self.assertEqual(self.cpu.R1, 0)

    @itest_setregs("R5=0", "R6=16")
    @itest_thumb("lsr.w R5, R6, #3")
    def test_lsrw_thumb(self):
        self.assertEqual(self.cpu.R5, 16 >> 3)

    @itest_setregs("R0=11", "R2=2")
    @itest_thumb("lsr.w R0, R0, R2")
    def test_lsrw_thumb_reg(self):
        self.assertEqual(self.cpu.R0, 11 >> 2)

    @itest_setregs("R5=0", "R6=16")
    @itest_thumb("asr.w R5, R6, #3")
    def test_asrw_thumb(self):
        self.assertEqual(self.cpu.R5, 16 >> 3)

    # RSB

    @itest_setregs("R2=29")
    @itest("RSB r2, r2, #31")
    def test_rsb_imm(self):
        # Diverging instruction from trace
        self.assertEqual(self.rf.read("R2"), 2)

    @itest_setregs("R2=0x17000")
    @itest("RSB r2, r2, #0x18000")
    def test_rsb_mod_imm_1(self):
        self.assertEqual(self.rf.read("R2"), 0x1000)

    @itest_setregs("R2=0x17000")
    @itest("RSB r2, r2, #24, 20")
    def test_rsb_mod_imm_2(self):
        self.assertEqual(self.rf.read("R2"), 0x1000)

    @itest_setregs("R6=2", "R8=0xfffffffe")
    @itest("RSBS r8, r6, #0")
    def test_rsbs_carry(self):
        self.assertEqual(self.rf.read("R8"), 0xFFFFFFFE)
        self._checkFlagsNZCV(1, 0, 0, 0)

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
        self.cpu.execute()
        self.rf.write("R1", 1)
        self.rf.write("R3", 0)
        self.mem.write(self.cpu.PC, assemble("tst r3, r1"))
        self.cpu.execute()
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

    @itest_setregs("R1=0xFF")
    @itest("BIC R1, #0x10")
    def test_thumb_bic_reg_imm(self):
        self.assertEqual(self.rf.read("R1"), 0xEF)

    @itest_setregs("R1=0x18002")
    @itest("BIC R2, R1, #0x18000")
    def test_bic_reg_mod_imm_1(self):
        self.assertEqual(self.rf.read("R2"), 0x2)

    @itest_setregs("R1=0x18002")
    @itest("BIC R2, R1, #24, 20")
    def test_bic_reg_mod_imm_2(self):
        self.assertEqual(self.rf.read("R2"), 0x2)

    @itest_setregs("R1=0x1008")
    @itest("BLX R1")
    def test_blx_reg(self):
        self.assertEqual(self.rf.read("PC"), 0x1008)
        self.assertEqual(self.rf.read("LR"), 0x1008)
        self.assertEqual(self.cpu.mode, CS_MODE_ARM)

    @itest_setregs("R1=0x1009")
    @itest("BLX R1")
    def test_blx_reg_thumb(self):
        self.assertEqual(self.rf.read("PC"), 0x1008)
        self.assertEqual(self.rf.read("LR"), 0x1008)
        self.assertEqual(self.cpu.mode, CS_MODE_THUMB)

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

    @itest("dmb ish")
    def test_dmb(self):
        # This is a nop, ensure that the instruction exists
        self.assertTrue(True)

    @itest_custom("vldmia  r1, {d8, d9, d10}")
    def test_vldmia(self):
        self.cpu.stack_push(20, 8)
        self.cpu.stack_push(21, 8)
        self.cpu.stack_push(22, 8)
        self.cpu.R1 = self.cpu.SP
        pre = self.cpu.R1
        self.cpu.execute()
        self.assertEqual(self.cpu.D8, 22)
        self.assertEqual(self.cpu.D9, 21)
        self.assertEqual(self.cpu.D10, 20)
        self.assertEqual(self.cpu.R1, pre)

    @itest_custom("vldmia  r1!, {d8, d9, d10}")
    def test_vldmia_wb(self):
        pre = self.cpu.SP
        self.cpu.stack_push(20, 8)
        self.cpu.stack_push(21, 8)
        self.cpu.stack_push(22, 8)
        self.cpu.R1 = self.cpu.SP
        self.cpu.execute()
        self.assertEqual(self.cpu.D8, 22)
        self.assertEqual(self.cpu.D9, 21)
        self.assertEqual(self.cpu.D10, 20)
        self.assertEqual(self.cpu.R1, pre)

    @itest_setregs("R3=3")
    @itest("movt R3, #9")
    def test_movt(self):
        self.assertEqual(self.cpu.R3, 0x90003)

    @itest_custom("mrc p15, #0, r2, c13, c0, #3")
    def test_mrc(self):
        self.cpu.set_arm_tls(0x55555)
        self.cpu.write_register("R2", 0)
        self.cpu.execute()
        self.assertEqual(self.cpu.R2, 0x55555)

    @itest_setregs("R1=0x45", "R2=0x55555555")
    @itest("uxtb r1, r2")
    def test_uxtb(self):
        self.assertEqual(self.cpu.R2, 0x55555555)
        self.assertEqual(self.cpu.R1, 0x55)

    @itest_setregs("R1=0x45", "R2=0x55555555")
    @itest("uxth r1, r2")
    def test_uxth(self):
        self.assertEqual(self.cpu.R2, 0x55555555)
        self.assertEqual(self.cpu.R1, 0x5555)

    @itest_setregs("R1=1", "R2=0", "R3=0", "R4=0", "R12=0x4141")
    @itest_thumb_multiple(["cmp r1, #1", "itt ne", "mov r2, r12", "mov r3, r12", "mov r4, r12"])
    def test_itt_ne_noexec(self):
        self.assertEqual(self.rf.read("R2"), 0)
        self.assertEqual(self.rf.read("R3"), 0)
        self.assertEqual(self.rf.read("R4"), 0x4141)

    @itest_setregs("R1=0", "R2=0", "R3=0", "R4=0", "R12=0x4141")
    @itest_thumb_multiple(["cmp r1, #1", "itt ne", "mov r2, r12", "mov r3, r12", "mov r4, r12"])
    def test_itt_ne_exec(self):
        self.assertEqual(self.rf.read("R2"), 0x4141)
        self.assertEqual(self.rf.read("R3"), 0x4141)
        self.assertEqual(self.rf.read("R4"), 0x4141)

    @itest_setregs("R1=0", "R2=0", "R3=0", "R4=0", "R12=0x4141")
    @itest_thumb_multiple(["cmp r1, #1", "ite ne", "mov r2, r12", "mov r3, r12", "mov r4, r12"])
    def test_ite_ne_exec(self):
        self.assertEqual(self.rf.read("R2"), 0x4141)
        self.assertEqual(self.rf.read("R3"), 0x0)
        self.assertEqual(self.rf.read("R4"), 0x4141)

    @itest_setregs("R1=0", "R2=0", "R3=0", "R4=0")
    @itest_thumb_multiple(
        ["cmp r1, #1", "itete ne", "mov r1, #1", "mov r2, #1", "mov r3, #1", "mov r4, #4"]
    )
    def test_itete_exec(self):
        self.assertEqual(self.rf.read("R1"), 1)
        self.assertEqual(self.rf.read("R2"), 0)
        self.assertEqual(self.rf.read("R3"), 1)
        self.assertEqual(self.rf.read("R4"), 0)

    @itest_setregs("APSR_GE=3", "R4=0", "R5=0x01020304", "R6=0x05060708")
    @itest_thumb("sel r4, r5, r6")
    def test_sel(self):
        self.assertEqual(self.rf.read("R4"), 0x05060304)

    @itest_setregs("R2=0", "R1=0x01020304")
    @itest("rev r2, r1")
    def test_rev(self):
        self.assertEqual(self.rf.read("R1"), 0x01020304)
        self.assertEqual(self.rf.read("R2"), 0x04030201)

    @itest_setregs("R1=0x01020304", "R2=0x05060708", "R3=0", "R4=0xF001")
    @itest_multiple(["sxth r1, r2", "sxth r3, r4", "sxth r5, r4, ROR #8"])
    def test_sxth(self):
        self.assertEqual(self.rf.read("R1"), 0x0708)
        self.assertEqual(self.rf.read("R3"), 0xFFFFF001)
        self.assertEqual(self.rf.read("R5"), 0xF0)

    @itest_custom("blx  r1")
    def test_blx_reg_sym(self):
        dest = self.cpu.memory.constraints.new_bitvec(32, "dest")
        self.cpu.memory.constraints.add(dest >= 0x1000)
        self.cpu.memory.constraints.add(dest <= 0x1001)
        self.cpu.R1 = dest

        # First, make sure we raise when the mode is symbolic and ambiguous
        with self.assertRaises(Concretize) as cm:
            self.cpu.execute()

        # Then, make sure we have the correct expression
        e = cm.exception
        all_modes = solver.get_all_values(self.cpu.memory.constraints, e.expression)
        self.assertIn(CS_MODE_THUMB, all_modes)
        self.assertIn(CS_MODE_ARM, all_modes)

        # Assuming we're in ARM mode, ensure the callback toggles correctly.
        self.assertEqual(self.cpu.mode, CS_MODE_ARM)
        # The setstate callback expects a State as its first argument; since we
        # don't have a state, the unit test itself is an okay approximation, since
        # the cpu lives in self.cpu
        e.setstate(self, CS_MODE_THUMB)
        self.assertEqual(self.cpu.mode, CS_MODE_THUMB)

    @itest_setregs("R1=0x00000008")  # pc/r15 is set to 0x1004 in _setupCpu()
    @itest("add pc, pc, r1")
    def test_add_to_pc(self):
        self.assertEqual(self.rf.read("R15"), 0x1014)

    # Make sure a cpu will survive a round trip through pickling/unpickling
    def test_arm_save_restore_cpu(self):
        import pickle

        dumped_s = pickle_dumps(self.cpu)
        self.cpu = pickle.loads(dumped_s)

    def test_symbolic_conditional(self):
        asm = ""
        asm += "  tst r0, r0\n"  # 0x1004
        asm += "  beq label\n"  # 0x1006
        asm += "  bne label\n"  # 0x1008
        asm += "label:\n"
        asm += "  nop"  # 0x100a

        self._setupCpu(asm, mode=CS_MODE_THUMB)  # code starts at 0x1004

        # Set R0 as a symbolic value
        self.cpu.R0 = self.cpu.memory.constraints.new_bitvec(32, "val")
        self.cpu.execute()  # tst r0, r0
        self.cpu.execute()  # beq label

        # Here the PC can have two values, one for each branch of the beq
        with self.assertRaises(ConcretizeRegister) as cm:
            self.cpu.execute()  # Should request concretizing the PC

        # Get the symbolic expression of the PC
        expression = self.cpu.read_register(cm.exception.reg_name)
        # Get all possible values of the expression
        all_values = solver.get_all_values(self.cpu.memory.constraints, expression)
        # They should be either the beq instruction itself, or the next instruction
        self.assertEqual(sorted(all_values), [0x1006, 0x1008])

        # Move the PC to the second branch instruction
        self.cpu.PC = 0x1008
        self.cpu.execute()  # bne label

        # Here the PC can have two values again, one for each branch of the bne
        with self.assertRaises(ConcretizeRegister) as cm:
            self.cpu.execute()  # Should request concretizing the PC

        # Get the symbolic expression of the PC
        expression = self.cpu.read_register(cm.exception.reg_name)
        # Get all possible values of the PC
        all_values = solver.get_all_values(self.cpu.memory.constraints, expression)
        # They should be either the bne instruction itself, or the next instruction
        self.assertEqual(sorted(all_values), [0x1008, 0x100A])
