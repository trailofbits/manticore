import unittest
import struct
from functools import wraps

from manticore.core.cpu.arm import Armv7Cpu as Cpu, Mask, Interruption
from manticore.core.memory import Memory32

from capstone.arm import *
from keystone import Ks, KS_ARCH_ARM, KS_MODE_ARM

ks = Ks(KS_ARCH_ARM, KS_MODE_ARM)

import logging

logger = logging.getLogger("ARM_TESTS")


def assemble(asm):
    ords = ks.asm(asm)[0]
    if not ords:
        raise Exception('bad assembly: {}'.format(asm))
    return ''.join(map(chr, ords))


class Armv7CpuTest(unittest.TestCase):
    def setUp(self):
        self.c = Cpu(Memory32())
        self.rf = self.c.regfile
        self._setupStack()

    def _setupStack(self):
        self.stack = self.c.memory.mmap(0xf000, 0x1000, 'rw')
        self.rf.write('SP', self.stack + 0x1000)

    def test_rd(self):
        self.assertEqual(self.rf.read('R0'), 0)

    def test_rd2(self):
        self.c.STACK = 0x1337
        self.assertEqual(self.rf.read('SP'), 0x1337)

    def test_stack_set_get(self):
        self.c.STACK = 0x1337
        self.assertEqual(self.c.STACK, 0x1337)

    def test_rd3(self):
        self.c.STACK = 0x1337 - 1
        self.assertEqual(self.rf.read('SP'), 0x1336)

    def test_rd4(self):
        self.c.STACK = 0x1337 + 1
        self.assertEqual(self.rf.read('SP'), 0x1338)

    def test_stack_push(self):
        self.c.stack_push(42)
        self.c.stack_push(44)
        self.assertItemsEqual(self.c.read(self.c.STACK, 4), '\x2c\x00\x00\x00')
        self.assertItemsEqual(self.c.read(self.c.STACK + 4, 4), '\x2a\x00\x00\x00')

    def test_stack_pop(self):
        v = 0x55
        v_bytes = struct.pack('<I', v)
        self.c.stack_push(v)
        val = self.c.stack_pop()
        self.assertItemsEqual(self.c.read(self.c.STACK - 4, 4), v_bytes)

    def test_stack_peek(self):
        self.c.stack_push(42)
        self.assertItemsEqual(self.c.stack_peek(), '\x2a\x00\x00\x00')

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
                dest, src = p.split('=')

                try:
                    src = int(src, 0)
                except:
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


class Armv7CpuInstructions(unittest.TestCase):
    def setUp(self):
        self.cpu = Cpu(Memory32())
        self.mem = self.cpu.memory
        self.rf = self.cpu.regfile

    def _setupCpu(self, asm):
        self.code = self.mem.mmap(0x1000, 0x1000, 'rwx')
        self.data = self.mem.mmap(0xd000, 0x1000, 'rw')
        self.stack = self.mem.mmap(0xf000, 0x1000, 'rw')
        start = self.code + 4
        self.mem.write(start, assemble(asm))
        self.rf.write('PC', start)
        self.rf.write('SP', self.stack + 0x1000)

    def _checkFlagsNZCV(self, n, z, c, v):
        self.assertEqual(self.rf.read('APSR_N'), n)
        self.assertEqual(self.rf.read('APSR_Z'), z)
        self.assertEqual(self.rf.read('APSR_C'), c)
        self.assertEqual(self.rf.read('APSR_V'), v)

    # MOV

    @itest("mov r0, 0x0")
    def test_mov_imm_min(self):
        self.assertEqual(self.rf.read('R0'), 0x0)

    @itest("mov r0, 42")
    def test_mov_imm_norm(self):
        self.assertEqual(self.rf.read('R0'), 42)

    @itest("mov r0, 0x100")
    def test_mov_imm_modified_imm_min(self):
        self.assertEqual(self.rf.read('R0'), 0x100)

    @itest("mov r0, 0xff000000")
    def test_mov_imm_modified_imm_max(self):
        self.assertEqual(self.rf.read('R0'), 0xff000000)

    @itest_custom("mov r0, r1")
    def test_mov_immreg(self):
        self.rf.write('R1', 0)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R0'), 0)

    @itest_custom("mov r0, r1")
    def test_mov_immreg1(self):
        self.rf.write('R1', 2 ** 32)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R0'), 0)

    @itest_custom("mov r0, r1")
    def test_mov_immreg2(self):
        self.rf.write('R1', 0xffffffff)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R0'), 0xffffffff)

    @itest_custom("mov r0, r1")
    def test_mov_immreg3(self):
        self.rf.write('R1', 42)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R0'), 42)

    # MOVW

    @itest("movw r0, 0")
    def test_movw_imm_min(self):
        self.assertEqual(self.rf.read('R0'), 0x0)

    @itest("movw r0, 0xffff")
    def test_movw_imm_max(self):
        self.assertEqual(self.rf.read('R0'), 0xffff)

    # MOVS

    @itest_custom("movs r0, 0")
    def test_movs_imm_min(self):
        pre_c = self.rf.read('APSR_C')
        pre_v = self.rf.read('APSR_V')
        self.cpu.execute()
        self.assertEqual(self.rf.read('R0'), 0)
        self._checkFlagsNZCV(0, 1, pre_c, pre_v)

    @itest_custom("movs r0, 42")
    def test_movs_imm_norm(self):
        pre_c = self.rf.read('APSR_C')
        pre_v = self.rf.read('APSR_V')
        self.cpu.execute()
        self.assertEqual(self.rf.read('R0'), 42)
        self._checkFlagsNZCV(0, 0, pre_c, pre_v)

    @itest_custom("movs r0, 0x100")
    def test_movs_imm_modified_imm_min(self):
        pre_c = self.rf.read('APSR_C')
        pre_v = self.rf.read('APSR_V')
        self.cpu.execute()
        self.assertEqual(self.rf.read('R0'), 0x100)
        self._checkFlagsNZCV(0, 0, pre_c, pre_v)

    @itest_custom("movs r0, 0xff000000")
    def test_movs_imm_modified_imm_max(self):
        pre_v = self.rf.read('APSR_V')
        self.cpu.execute()
        self.assertEqual(self.rf.read('R0'), 0xff000000)
        self._checkFlagsNZCV(1, 0, 1, pre_v)

    @itest_custom("movs r0, 0x0e000000")
    def test_movs_imm_modified_imm_sans_carry(self):
        pre_v = self.rf.read('APSR_V')
        self.cpu.execute()
        self.assertEqual(self.rf.read('R0'), 0x0e000000)
        self._checkFlagsNZCV(0, 0, 0, pre_v)

    @itest_custom("movs r0, r1")
    def test_movs_reg(self):
        self.rf.write('R1', 0)
        pre_c = self.rf.read('APSR_C')
        pre_v = self.rf.read('APSR_V')
        self.cpu.execute()
        self.assertEqual(self.rf.read('R0'), 0)
        self._checkFlagsNZCV(0, 1, pre_c, pre_v)

    @itest_custom("movs r0, r1")
    def test_movs_reg1(self):
        self.rf.write('R1', 2 ** 32)
        pre_c = self.rf.read('APSR_C')
        pre_v = self.rf.read('APSR_V')
        self.cpu.execute()
        self.assertEqual(self.rf.read('R0'), 0)
        self._checkFlagsNZCV(0, 1, pre_c, pre_v)

    @itest_custom("movs r0, r1")
    def test_movs_reg2(self):
        self.rf.write('R1', 2 ** 32 - 1)
        pre_c = self.rf.read('APSR_C')
        pre_v = self.rf.read('APSR_V')
        self.cpu.execute()
        self.assertEqual(self.rf.read('R0'), 2 ** 32 - 1)
        self._checkFlagsNZCV(1, 0, pre_c, pre_v)

    @itest_custom("movs r0, r1")
    def test_movs_reg3(self):
        self.rf.write('R1', 42)
        pre_c = self.rf.read('APSR_C')
        pre_v = self.rf.read('APSR_V')
        self.cpu.execute()
        self.assertEqual(self.rf.read('R0'), 42)
        self._checkFlagsNZCV(0, 0, pre_c, pre_v)

    # ADD

    @itest_custom("add r3, r1, 55")
    def test_add_imm_norm(self):
        self.rf.write('R1', 44)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 99)

    @itest_custom("add r3, r1, 0x100")
    def test_add_imm_mod_imm_min(self):
        self.rf.write('R1', 44)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 44 + 0x100)

    @itest_custom("add r3, r1, 0xff000000")
    def test_add_imm_mod_imm_max(self):
        self.rf.write('R1', 44)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 44 + 0xff000000)

    @itest_custom("add r3, r1, 0x1000000")
    def test_add_imm_carry(self):
        self.rf.write('R1', 0xff000001)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 1)

    @itest_custom("add r3, r1, 0x1")
    def test_add_imm_overflow(self):
        self.rf.write('R1', (2 ** 31 - 1))
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 0x80000000)

    @itest_custom("add r3, r1, r2")
    def test_add_reg_norm(self):
        self.rf.write('R1', 44)
        self.rf.write('R2', 55)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 99)

    @itest_custom("add r3, r1, r2")
    def test_add_reg_mod_imm_min(self):
        self.rf.write('R1', 44)
        self.rf.write('R2', 0x100)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 44 + 0x100)

    @itest_custom("add r3, r1, r2")
    def test_add_reg_mod_imm_max(self):
        self.rf.write('R1', 44)
        self.rf.write('R2', 0xff000000)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 44 + 0xff000000)

    @itest_custom("add r3, r1, r2")
    def test_add_reg_carry(self):
        self.rf.write('R1', 0x1000000)
        self.rf.write('R2', 0xff000001)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 1)

    @itest_custom("add r3, r1, r2")
    def test_add_reg_overflow(self):
        self.rf.write('R1', (2 ** 31 - 1))
        self.rf.write('R2', 1)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), (1 << 31))

    @itest_custom("add r3, r1, r2, lsl #3")
    def test_add_reg_sft_lsl(self):
        self.rf.write('R1', 0x0)
        self.rf.write('R2', 0x1)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), (1 << 3))

    @itest_custom("add r3, r1, r2, lsr #3")
    def test_add_reg_sft_lsr(self):
        self.rf.write('R1', 0x0)
        self.rf.write('R2', 0x8)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), (0x8 >> 3))

    @itest_custom("add r3, r1, r2, asr #3")
    def test_add_reg_sft_asr(self):
        self.rf.write('R1', 0x0)
        self.rf.write('R2', 0x80000000)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 0xf0000000)

    @itest_custom("add r3, r1, r2, asr #3")
    def test_add_reg_sft_asr2(self):
        self.rf.write('R1', 0x0)
        self.rf.write('R2', 0x40000000)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), (0x40000000 >> 3))

    @itest_custom("add r3, r1, r2, ror #3")
    def test_add_reg_sft_ror_norm(self):
        self.rf.write('R1', 0x0)
        self.rf.write('R2', 0x8)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 0x1)

    @itest_custom("add r3, r1, r2, ror #3")
    def test_add_reg_sft_ror(self):
        self.rf.write('R1', 0x0)
        self.rf.write('R2', 0x3)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 0x60000000)

    @itest_custom("adc r3, r1, r2")
    @itest_setregs("R1=1", "R2=2", "APSR_C=1")
    def test_adc_basic(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 4)

    @itest_custom("adc r3, r1, r2, ror #3")
    @itest_setregs("R1=1", "R2=2", "APSR_C=1")
    def test_adc_reg_sft_ror(self):
        self.rf.write('R1', 0x0)
        self.rf.write('R2', 0x3)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 0x60000001)

    # TODO what is shifter_carry_out in the manual, A8-291? it gets set to
    # Bit[0] presumably, but i have no clue what it is. Not mentioned again in
    # manual.
    @itest_custom("add r3, r1, r2, rrx")
    def test_add_reg_sft_rrx(self):
        self.rf.write('APSR_C', 0x0)
        self.rf.write('R1', 0x0)
        self.rf.write('R2', 2 ** 32 - 1)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 2 ** 31 - 1)

    @itest_custom("add r3, r1, r2, rrx")
    def test_add_reg_sft_rrx2(self):
        self.rf.write('APSR_C', 0x1)
        self.rf.write('R1', 0x0)
        self.rf.write('R2', 2 ** 32 - 1)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 2 ** 32 - 1)

    @itest_custom("add r3, r1, r2, lsl r4")
    def test_add_reg_sft_lsl_reg(self):
        self.rf.write('R1', 0x0)
        self.rf.write('R4', 0x3)
        self.rf.write('R2', 0x1)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), (1 << 3))

    @itest_custom("add r3, r1, r2, lsr r4")
    def test_add_reg_sft_lsr_reg(self):
        self.rf.write('R1', 0x0)
        self.rf.write('R4', 0x3)
        self.rf.write('R2', 0x8)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), (0x8 >> 3))

    @itest_custom("add r3, r1, r2, asr r4")
    def test_add_reg_sft_asr_reg(self):
        self.rf.write('R1', 0x0)
        self.rf.write('R4', 0x3)
        self.rf.write('R2', 0x80000000)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 0xf0000000)

    @itest_custom("add r3, r1, r2, asr r4")
    def test_add_reg_sft_asr2_reg(self):
        self.rf.write('R1', 0x0)
        self.rf.write('R4', 0x3)
        self.rf.write('R2', 0x40000000)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), (0x40000000 >> 3))

    @itest_custom("add r3, r1, r2, ror r4")
    def test_add_reg_sft_ror_norm_reg(self):
        self.rf.write('R1', 0x0)
        self.rf.write('R4', 0x3)
        self.rf.write('R2', 0x8)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 1)

    @itest_custom("add r3, r1, r2, ror r4")
    def test_add_reg_sft_ror_reg(self):
        self.rf.write('R1', 0x0)
        self.rf.write('R4', 0x3)
        self.rf.write('R2', 0x3)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 0x60000000)

    @itest_custom("add r3, r1, r2, rrx")
    def test_add_reg_sft_rrx_reg(self):
        self.rf.write('R1', 0x0)
        self.rf.write('APSR_C', 0x0)
        self.rf.write('R2', 2 ** 32 - 1)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 2 ** 31 - 1)

    @itest_custom("add r3, r1, r2, rrx")
    def test_add_reg_sft_rrx2_reg(self):
        self.rf.write('R1', 0x0)
        self.rf.write('APSR_C', 0x1)
        self.rf.write('R2', 2 ** 32 - 1)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 2 ** 32 - 1)

    # ADDS

    @itest_custom("adds r3, r1, 55")
    def test_adds_imm_norm(self):
        self.rf.write('R1', 44)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 99)
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_custom("adds r3, r1, 0x100")
    def test_adds_imm_mod_imm_min(self):
        self.rf.write('R1', 44)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 44 + 0x100)
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_custom("adds r3, r1, 0xff000000")
    def test_adds_imm_mod_imm_max(self):
        self.rf.write('R1', 44)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 44 + 0xff000000)
        self._checkFlagsNZCV(1, 0, 0, 0)

    @itest_custom("adds r3, r1, 0x1000000")
    def test_adds_imm_carry(self):
        self.rf.write('R1', 0xff000001)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 1)
        self._checkFlagsNZCV(0, 0, 1, 0)

    @itest_custom("adds r3, r1, 0x80000000")
    def test_adds_imm_carry_overflow(self):
        self.rf.write('R1', 0x80000001)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 1)
        self._checkFlagsNZCV(0, 0, 1, 1)

    @itest_custom("adds r3, r1, 0x1")
    def test_adds_imm_overflow(self):
        self.rf.write('R1', (2 ** 31 - 1))
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 0x80000000)
        self._checkFlagsNZCV(1, 0, 0, 1)

    @itest_custom("adds r3, r3, 0x0")
    def test_adds_imm_zf(self):
        self.rf.write('R3', 0)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 0)
        self._checkFlagsNZCV(0, 1, 0, 0)

    @itest_custom("adds r3, r1, r2")
    def test_adds_reg_norm(self):
        self.rf.write('R1', 44)
        self.rf.write('R2', 55)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 99)
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_custom("adds r3, r1, r2")
    def test_adds_reg_mod_imm_min(self):
        self.rf.write('R1', 44)
        self.rf.write('R2', 0x100)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 44 + 0x100)
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_custom("adds r3, r1, r2")
    def test_adds_reg_mod_imm_max(self):
        self.rf.write('R1', 44)
        self.rf.write('R2', 0xff000000)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 44 + 0xff000000)
        self._checkFlagsNZCV(1, 0, 0, 0)

    @itest_custom("adds r3, r1, r2")
    def test_adds_reg_carry(self):
        self.rf.write('R1', 0x1000000)
        self.rf.write('R2', 0xff000001)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 1)
        self._checkFlagsNZCV(0, 0, 1, 0)

    @itest_custom("adds r3, r1, r2")
    def test_adds_reg_overflow(self):
        self.rf.write('R1', (2 ** 31 - 1))
        self.rf.write('R2', 1)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), (1 << 31))
        self._checkFlagsNZCV(1, 0, 0, 1)

    @itest_custom("adds r3, r1, r2")
    def test_adds_reg_carry_overflow(self):
        self.rf.write('R1', 0x80000001)
        self.rf.write('R2', 0x80000000)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 1)
        self._checkFlagsNZCV(0, 0, 1, 1)

    @itest_custom("adds r3, r1, r2")
    def test_adds_reg_zf(self):
        self.rf.write('R1', 0x0)
        self.rf.write('R2', 0x0)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 0)
        self._checkFlagsNZCV(0, 1, 0, 0)

    @itest_custom("adds r3, r1, r2, asr #3")
    def test_adds_reg_sft_asr(self):
        self.rf.write('R1', 0x0)
        self.rf.write('R2', 0x80000000)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 0xf0000000)
        self._checkFlagsNZCV(1, 0, 0, 0)

    @itest_custom("adds r3, r1, r2, asr #3")
    def test_adds_reg_sft_asr2(self):
        self.rf.write('R1', 0x0)
        self.rf.write('R2', 0x40000000)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), (0x40000000 >> 3))
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_custom("adds r3, r1, r2, rrx")
    def test_adds_reg_sft_rrx(self):
        self.rf.write('APSR_C', 0x0)
        self.rf.write('R1', 0x0)
        self.rf.write('R2', 2 ** 32 - 1)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 2 ** 31 - 1)
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_custom("adds r3, r1, r2, rrx")
    def test_adds_reg_sft_rrx2(self):
        self.rf.write('APSR_C', 0x1)
        self.rf.write('R1', 0x0)
        self.rf.write('R2', 2 ** 32 - 1)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 2 ** 32 - 1)
        self._checkFlagsNZCV(1, 0, 0, 0)

    # LDR imm

    @itest_custom("ldr r1, [sp]")
    def test_ldr_imm_off_none(self):
        self.cpu.stack_push(42)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 42)

    @itest_custom("ldr r1, [sp, #4]")
    def test_ldr_imm_off_pos(self):
        self.cpu.stack_push(42)
        self.cpu.stack_push(41)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 42)

    @itest_custom("ldr r1, [sp, #-4]")
    def test_ldr_imm_off_neg(self):
        self.cpu.stack_push(42)
        self.cpu.stack_push(41)
        self.cpu.STACK += 4
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 41)

    @itest_custom("ldr r1, [sp, #4]!")
    def test_ldr_imm_preind_pos(self):
        self.cpu.stack_push(42)
        self.cpu.stack_push(41)
        pre_stack = self.cpu.STACK
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 42)
        self.assertEqual(self.rf.read('SP'), pre_stack + 4)

    @itest_custom("ldr r1, [sp, #-4]!")
    def test_ldr_imm_preind_neg(self):
        self.cpu.stack_push(42)
        self.cpu.stack_push(41)
        self.cpu.STACK += 4
        pre_stack = self.cpu.STACK
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 41)
        self.assertEqual(self.rf.read('SP'), pre_stack - 4)

    @itest_custom("ldr r1, [sp], #5")
    def test_ldr_imm_postind_pos(self):
        self.cpu.stack_push(42)
        pre_stack = self.cpu.STACK
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 42)
        self.assertEqual(self.rf.read('SP'), pre_stack + 5)

    @itest_custom("ldr r1, [sp], #-5")
    def test_ldr_imm_postind_neg(self):
        self.cpu.stack_push(42)
        pre_stack = self.cpu.STACK
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 42)
        self.assertEqual(self.rf.read('SP'), pre_stack - 5)

    # LDR reg

    @itest_custom("ldr r1, [sp, r2]")
    def test_ldr_reg_off(self):
        self.cpu.regfile.write('R2', 4)
        self.cpu.stack_push(42)
        self.cpu.stack_push(48)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 42)

    @itest_custom("ldr r1, [sp, -r2]")
    def test_ldr_reg_off_neg(self):
        self.cpu.regfile.write('R2', 4)
        self.cpu.stack_push(42)
        self.cpu.stack_push(48)
        self.cpu.STACK += 4
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 48)

    @itest_custom("ldr r1, [sp, r2, lsl #3]")
    def test_ldr_reg_off_shift(self):
        self.cpu.regfile.write('R2', 1)
        self.cpu.stack_push(42)
        self.cpu.stack_push(48)
        self.cpu.stack_push(40)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 42)

    @itest_custom("ldr r1, [sp, -r2, lsl #3]")
    def test_ldr_reg_off_neg_shift(self):
        self.cpu.regfile.write('R2', 1)
        self.cpu.stack_push(42)
        self.cpu.stack_push(48)
        self.cpu.STACK += 8
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 48)

    @itest_custom("ldr r1, [sp, r2]!")
    def test_ldr_reg_preind(self):
        self.cpu.regfile.write('R2', 4)
        self.cpu.stack_push(42)
        self.cpu.stack_push(48)
        pre_stack = self.cpu.STACK
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 42)
        self.assertEqual(self.rf.read('SP'), pre_stack + 4)

    @itest_custom("ldr r1, [sp, -r2, lsl #3]!")
    def test_ldr_reg_preind_shift(self):
        self.cpu.regfile.write('R2', 1)
        self.cpu.stack_push(42)
        self.cpu.stack_push(48)
        self.cpu.STACK += 8
        pre_stack = self.cpu.STACK
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 48)
        self.assertEqual(self.rf.read('SP'), pre_stack - 8)

    @itest_custom("ldr r1, [sp], r2")
    def test_ldr_reg_postind(self):
        self.cpu.regfile.write('R2', 4)
        self.cpu.stack_push(42)
        pre_stack = self.cpu.STACK
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 42)
        self.assertEqual(self.rf.read('SP'), pre_stack + 4)

    @itest_custom("ldr r1, [sp], -r2, lsl #3")
    def test_ldr_reg_postind_neg_shift(self):
        self.cpu.regfile.write('R2', 1)
        self.cpu.stack_push(42)
        pre_stack = self.cpu.STACK
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 42)
        self.assertEqual(self.rf.read('SP'), pre_stack - 8)

    @itest_custom("pop {r1}")
    def test_pop_one_reg(self):
        self.cpu.stack_push(0x55)
        pre_stack = self.cpu.STACK
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 0x55)
        self.assertEqual(self.rf.read('SP'), pre_stack + 4)

    @itest_custom("pop {r1, r2, r3}")
    def test_pop_multops(self):
        vals = [0x01, 0x55, 0xAA]
        for v in vals:
            self.cpu.stack_push(v)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 0xAA)
        self.assertEqual(self.rf.read('R2'), 0x55)
        self.assertEqual(self.rf.read('R3'), 0x01)

    @itest_custom("push {r1}")
    @itest_setregs("R1=3")
    def test_push_one_reg(self):
        self.cpu.execute()
        self.assertItemsEqual(self.cpu.stack_peek(), struct.pack('<I', 3))

    @itest_custom("push {r1, r2, r3}")
    @itest_setregs("R1=3", "R2=0x55", "R3=0xffffffff")
    def test_push_multi_reg(self):
        pre_sp = self.cpu.STACK
        self.cpu.execute()
        sp = self.cpu.STACK
        self.assertEqual(self.rf.read('SP'), pre_sp - (3 * 4))
        self.assertItemsEqual(self.cpu.stack_peek(), struct.pack('<I', 3))
        self.assertEqual(self.cpu.read_int(sp + 4, self.cpu.address_bit_size), 0x55)
        self.assertEqual(self.cpu.read_int(sp + 8, self.cpu.address_bit_size), 0xffffffff)

    @itest_custom("str SP, [R1]")
    @itest_setregs("R1=0xd000")
    def test_str_basic(self):
        r1 = self.rf.read('R1')
        sp = self.rf.read('SP')
        self.cpu.execute()
        dr1 = self.cpu.read_int(r1, self.cpu.address_bit_size)
        self.assertEqual(sp, dr1)

    @itest_custom("str R1, [R2, R3]")
    @itest_setregs("R1=34", "R2=0xD000", "R3=8")
    def test_str_index(self):
        r1 = self.rf.read('R1')
        r2 = self.rf.read('R2')
        r3 = self.rf.read('R3')
        self.cpu.execute()
        retrieved = self.cpu.read_int(r2 + r3, self.cpu.address_bit_size)
        self.assertEqual(retrieved, r1)

    @itest_custom("str R1, [R2, R3, LSL #3]")
    @itest_setregs("R1=34", "R2=0xD000", "R3=1")
    def test_str_index_w_shift(self):
        r1 = self.rf.read('R1')
        r2 = self.rf.read('R2')
        r3 = self.rf.read('R3')
        r3 = r3 << 3
        self.cpu.execute()
        retrieved = self.cpu.read_int(r2 + r3, self.cpu.address_bit_size)
        self.assertEqual(retrieved, r1)

    @itest_custom("str R1, [R2], #3")
    @itest_setregs("R1=34", "R2=0xD000")
    def test_str_postindex(self):
        r1 = self.rf.read('R1')
        r2 = self.rf.read('R2')
        self.cpu.execute()
        # check store results
        data = self.cpu.read_int(r2, self.cpu.address_bit_size)
        self.assertEqual(data, r1)
        # check writeback results
        new_r2 = self.rf.read('R2')
        self.assertEqual(new_r2, r2 + 3)

    @itest_custom("str R1, [R2, #3]!")
    @itest_setregs("R1=34", "R2=0xD000")
    def test_str_index_writeback(self):
        r1 = self.rf.read('R1')
        r2 = self.rf.read('R2')
        self.cpu.execute()
        # check store results
        data = self.cpu.read_int(r2 + 3, self.cpu.address_bit_size)
        self.assertEqual(data, r1)
        # check writeback results
        new_r2 = self.rf.read('R2')
        self.assertEqual(new_r2, r2 + 3)

    # BL

    @itest_custom("bl 0x170")
    def test_bl(self):
        pre_pc = self.rf.read('PC')
        self.cpu.execute()
        self.assertEqual(self.rf.read('PC'), pre_pc + 0x170)
        self.assertEqual(self.rf.read('LR'), pre_pc + 4)

    @itest_custom("bl #-4")
    def test_bl_neg(self):
        pre_pc = self.rf.read('PC')
        self.cpu.execute()
        self.assertEqual(self.rf.read('PC'), pre_pc - 4)
        self.assertEqual(self.rf.read('LR'), pre_pc + 4)

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
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 16)

    @itest_custom("clz r1, r2")
    @itest_setregs("R2=0")
    def test_clz_all_zero(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), self.cpu.address_bit_size)

    @itest_custom("clz r1, r2")
    @itest_setregs("R2=0xffffffff")
    def test_clz_no_leading_zeroes(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 0)

    @itest_custom("clz r1, r2")
    @itest_setregs("R2=0x7fffffff")
    def test_clz_one_leading_zero(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 1)

    @itest_custom("clz r1, r2")
    @itest_setregs("R2=0x7f7fffff")
    def test_clz_lead_zero_then_more_zeroes(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 1)

    @itest_custom("sub r3, r1, r2")
    @itest_setregs("R1=4", "R2=2")
    def test_sub_basic(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 2)

    @itest_custom("sub r3, r1, #5")
    @itest_setregs("R1=10")
    def test_sub_imm(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 5)

    @itest_custom("sbc r3, r1, #5")
    @itest_setregs("R1=10")
    def test_sbc_imm(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read('R3'), 4)

    @itest_custom("ldm sp, {r1, r2, r3}")
    def test_ldm(self):
        self.cpu.stack_push(0x41414141)
        self.cpu.stack_push(2)
        self.cpu.stack_push(42)
        pre_sp = self.cpu.STACK
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 42)
        self.assertEqual(self.rf.read('R2'), 2)
        self.assertEqual(self.rf.read('R3'), 0x41414141)
        self.assertEqual(self.cpu.STACK, pre_sp)

    @itest_custom("ldm sp!, {r1, r2, r3}")
    def test_ldm_wb(self):
        self.cpu.stack_push(0x41414141)
        self.cpu.stack_push(2)
        self.cpu.stack_push(42)
        pre_sp = self.cpu.STACK
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 42)
        self.assertEqual(self.rf.read('R2'), 2)
        self.assertEqual(self.rf.read('R3'), 0x41414141)
        self.assertEqual(self.cpu.STACK, pre_sp + 12)

    @itest_setregs("R1=2", "R2=42", "R3=0x42424242")
    @itest_custom("stm sp, {r1, r2, r3}")
    def test_stm(self):
        self.cpu.STACK -= 12
        pre_sp = self.cpu.STACK
        self.cpu.execute()
        self.assertEqual(self.cpu.read_int(pre_sp, self.cpu.address_bit_size), 2)
        self.assertEqual(self.cpu.read_int(pre_sp + 4, self.cpu.address_bit_size), 42)
        self.assertEqual(self.cpu.read_int(pre_sp + 8, self.cpu.address_bit_size),
                         0x42424242)
        self.assertEqual(self.cpu.STACK, pre_sp)

    @itest_setregs("R1=2", "R2=42", "R3=0x42424242")
    @itest_custom("stm sp!, {r1, r2, r3}")
    def test_stm_wb(self):
        self.cpu.STACK -= 12
        pre_sp = self.cpu.STACK
        self.cpu.execute()
        self.assertEqual(self.cpu.read_int(pre_sp, self.cpu.address_bit_size), 2)
        self.assertEqual(self.cpu.read_int(pre_sp + 4, self.cpu.address_bit_size), 42)
        self.assertEqual(self.cpu.read_int(pre_sp + 8, self.cpu.address_bit_size),
                         0x42424242)
        self.assertEqual(self.cpu.STACK, pre_sp + 12)

    @itest_custom("stmib   r3, {r2, r4}")
    @itest_setregs("R1=1", "R2=2", "R4=4", "R3=0xd100")
    def test_stmib_basic(self):
        self.cpu.execute()
        addr = self.rf.read('R3')
        self.assertEqual(self.cpu.read_int(addr + 4, self.cpu.address_bit_size), 2)
        self.assertEqual(self.cpu.read_int(addr + 8, self.cpu.address_bit_size), 4)

    @itest_custom("bx r1")
    @itest_setregs("R1=0x1008")
    def test_bx_basic(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read('PC'), 0x1008)

    @itest_custom("bx r1")
    @itest_setregs("R1=0x1009")
    def test_bx_thumb(self):
        pre_pc = self.rf.read('PC')
        self.cpu.execute()
        self.assertEqual(self.rf.read('PC'), pre_pc + 4)

    # ORR

    @itest_custom("orr r2, r3, #5")
    @itest_setregs("R3=0x1000")
    def test_orr_imm(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read('R2'), 0x1005)

    @itest_custom("orrs r2, r3")
    @itest_setregs("R2=0x5", "R3=0x80000000")
    def test_orrs_imm_flags(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read('R2'), 0x80000005)
        self.assertEqual(self.rf.read('APSR_N'), True)

    @itest_custom("orr r2, r3")
    @itest_setregs("R2=0x5", "R3=0x80000000")
    def test_orr_reg_w_flags(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read('R2'), 0x80000005)
        # self.assertEqual(self.rf.read('APSR_N'), 1)

    @itest_custom("orr r2, r3, r4")
    @itest_setregs("R3=0x5", "R4=0x80000000")
    def test_orr_reg_two_op(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read('R2'), 0x80000005)
        # self.assertEqual(self.rf.read('APSR_N'), 1)

    @itest_custom("orr r2, r3, r4, LSL #4")
    @itest_setregs("R3=0x5", "R4=0xF")
    def test_orr_reg_two_op_shifted(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read('R2'), 0xF5)

    # EOR

    @itest_custom("eor r2, r3, #5")
    @itest_setregs("R3=0xA")
    def test_eor_imm(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read('R2'), 0xF)

    @itest_custom("eors r2, r3")
    @itest_setregs("R2=0xAA", "R3=0x80000000")
    def test_eors_imm_flags(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read('R2'), 0x800000AA)
        self.assertEqual(self.rf.read('APSR_N'), True)

    @itest_custom("eors r2, r3")
    @itest_setregs("R2=0x5", "R3=0x80000005")
    def test_eor_reg_w_flags(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read('R2'), 0x80000000)
        self.assertEqual(self.rf.read('APSR_N'), 1)

    @itest_custom("eor r2, r3, r4")
    @itest_setregs("R3=0x80000005", "R4=0x80000005")
    def test_eor_reg_two_op(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read('R2'), 0)

    @itest_custom("eor r2, r3, r4, LSL #4")
    @itest_setregs("R3=0x55", "R4=0x5")
    def test_eor_reg_two_op_shifted(self):
        self.cpu.execute()
        self.assertEqual(self.rf.read('R2'), 0x5)

    # LDRH - see also LDR tests

    @itest_custom("ldrh r1, [sp]")
    def test_ldrh_imm_off_none(self):
        self.cpu.stack_push(0x41410041)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 0x41)

    @itest_custom("ldrh r1, [sp, r2]")
    @itest_setregs("R2=4")
    def test_ldrh_reg_off(self):
        self.cpu.stack_push(0x41410041)
        self.cpu.stack_push(48)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 0x41)

    # LDRSH - see also LDR tests

    @itest_custom("ldrsh r1, [sp]")
    def test_ldrsh_imm_off_none_neg(self):
        self.cpu.stack_push(0x2ff0f)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 0xffffff0f)

    @itest_custom("ldrsh r1, [sp]")
    def test_ldrsh_imm_off_none_pos(self):
        self.cpu.stack_push(0xff0fff)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 0x0fff)

    @itest_custom("ldrsh r1, [sp, r2]")
    @itest_setregs("R2=4")
    def test_ldrsh_reg_off_neg(self):
        self.cpu.stack_push(0x2ff0f)
        self.cpu.stack_push(48)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 0xffffff0f)

    @itest_custom("ldrsh r1, [sp, r2]")
    @itest_setregs("R2=4")
    def test_ldrsh_reg_off_pos(self):
        self.cpu.stack_push(0xff0fff)
        self.cpu.stack_push(48)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 0x0fff)

    # LDRB - see also LDR tests

    @itest_custom("ldrb r1, [sp]")
    def test_ldrb_imm_off_none(self):
        self.cpu.stack_push(0x41)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 0x41)

    @itest_custom("ldrb r1, [sp, r2]")
    @itest_setregs("R2=4")
    def test_ldrb_reg_off(self):
        self.cpu.stack_push(0x41)
        self.cpu.stack_push(48)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 0x41)

    # LDRSB - see also LDR tests

    @itest_custom("ldrsb r1, [sp]")
    def test_ldrsb_imm_off_none_neg(self):
        self.cpu.stack_push(0x2ff)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), Mask(32))

    @itest_custom("ldrsb r1, [sp]")
    def test_ldrsb_imm_off_none_pos(self):
        self.cpu.stack_push(0xff0f)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 0xf)

    @itest_custom("ldrsb r1, [sp, r2]")
    @itest_setregs("R2=4")
    def test_ldrsb_reg_off_neg(self):
        self.cpu.stack_push(0x2ff)
        self.cpu.stack_push(48)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), Mask(32))

    @itest_custom("ldrsb r1, [sp, r2]")
    @itest_setregs("R2=4")
    def test_ldrsb_reg_off_pos(self):
        self.cpu.stack_push(0xff0f)
        self.cpu.stack_push(48)
        self.cpu.execute()
        self.assertEqual(self.rf.read('R1'), 0xf)

    # TST
    @itest_setregs("R1=1", "R3=0")
    @itest("tst r3, r1")
    def test_tst(self):
        self._checkFlagsNZCV(0, 1, 0, 0)

    # AND
    @itest_setregs("R2=5")
    @itest("and r2, r2, #1")
    def test_and_imm(self):
        self.assertEqual(self.rf.read('R2'), 1)

    @itest_setregs("R1=5", "R2=3")
    @itest("and r1, r1, r2")
    def test_and_reg(self):
        self.assertEqual(self.rf.read('R1'), 3 & 5)

    @itest_setregs("R1=5", "R2=3", "APSR_C=1")
    @itest("and r1, r1, r2")
    def test_and_reg_carry(self):
        self.assertEqual(self.rf.read('R1'), 3 & 5)
        self.assertEqual(self.rf.read('APSR_C'), 1)

    # svc

    def test_svc(self):
        with self.assertRaises(Interruption):
            self._setupCpu("svc #0")
            self.cpu.execute()

    # lsl

    @itest_setregs("R3=0x11")
    @itest("lsls r4, r3, 1")
    def test_lsl_imm_min(self):
        self.assertEqual(self.rf.read('R4'), 0x11 << 1)
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_setregs("R3=0x11")
    @itest("lsls r4, r3, 31")
    def test_lsl_imm_max(self):
        self.assertEqual(self.rf.read('R4'), 1 << 31)
        self._checkFlagsNZCV(1, 0, 0, 0)

    @itest_setregs("R3=0x11", "R2=0xff01")
    @itest("lsls r4, r3, r2")
    def test_lsl_reg_min(self):
        self.assertEqual(self.rf.read('R4'), 0x11 << 1)
        self._checkFlagsNZCV(0, 0, 0, 0)

    @itest_setregs("R3=0x11", "R2=0xff1f")
    @itest("lsls r4, r3, r2")
    def test_lsl_reg_max(self):
        self.assertEqual(self.rf.read('R4'), 0x1 << 31)
        self._checkFlagsNZCV(1, 0, 0, 0)

    @itest_setregs("R2=0xffffffff")
    @itest("lsls r2, r2, #0x1f")
    def test_lsl_imm_carry(self):
        self.assertEqual(self.cpu.R2, 0x1 << 31)
        self._checkFlagsNZCV(1, 0, 1, 0)

    # lsr
    @itest_setregs("R0=0x1000", "R2=3")
    @itest("lsr r0, r0, r2")
    def test_lsr_reg(self):
        self.assertEqual(self.rf.read('R0'), 0x1000 >> 3)

    @itest_setregs("R0=0x1000")
    @itest("lsr r0, r0, #3")
    def test_lsr_reg_imm(self):
        self.assertEqual(self.rf.read('R0'), 0x1000 >> 3)

    @itest_setregs("R2=29")
    @itest("RSB r2, r2, #31")
    def test_rsb_imm(self):
        # Diverging instruction from trace
        self.assertEqual(self.rf.read('R2'), 2)

    @itest_setregs("R6=2", "R8=0xfffffffe")
    @itest("RSBS r8, r6, #0")
    def test_rsbs_carry(self):
        self.assertEqual(self.rf.read('R8'), 0xFFFFFFFE)
        self._checkFlagsNZCV(1, 0, 0, 0)

    def test_flag_state_continuity(self):
        '''If an instruction only partially updates flags, cpu.setFlags should
        ensure unupdated flags are preserved.

        For example:
        r1 = 2**31 - 1
        add r2, r1, 0x1 // overflow = 1
        mov r1, 1
        mov r3, 0
        tst r3, r1 // does not change overflow flag
        // ovf should still be 1
        '''

        self.rf.write('R1', (2 ** 31 - 1))
        self._setupCpu("adds r2, r1, #0x1")
        self.cpu.execute()
        self.rf.write('R1', 1)
        self.rf.write('R3', 0)
        self.mem.write(self.cpu.PC, assemble("tst r3, r1"))
        self.cpu.execute()
        self._checkFlagsNZCV(0, 1, 0, 1)

    @itest_setregs("R1=30", "R2=10")
    @itest("MUL R1, R2")
    def test_mul_reg(self):
        self.assertEqual(self.rf.read('R1'), 300)

    @itest_setregs("R1=30", "R2=10")
    @itest("MUL R3, R1, R2")
    def test_mul_reg_w_dest(self):
        self.assertEqual(self.rf.read('R3'), 300)

    @itest_setregs("R2=10", "R3=15", "R4=7")
    @itest("MLA R1, R2, R3, R4")
    def test_mla_reg(self):
        self.assertEqual(self.rf.read('R1'), 157)

    @itest_setregs("R1=0xFF")
    @itest("BIC R2, R1, #0x10")
    def test_bic_reg_imm(self):
        self.assertEqual(self.rf.read('R2'), 0xEF)

    @itest_setregs("R1=0x1008")
    @itest("BLX R1")
    def test_blx_reg(self):
        self.assertEqual(self.rf.read('PC'), 0x1008)
        self.assertEqual(self.rf.read('LR'), 0x1008)

    @itest_setregs("R1=0x1009")
    @itest("BLX R1")
    def test_blx_reg_thumb(self):
        self.assertEqual(self.rf.read('PC'), 0x1008)
        self.assertEqual(self.rf.read('LR'), 0x1008)

    @itest_setregs("R1=0xffffffff", "R2=2")
    @itest("UMULLS R1, R2, R1, R2")
    def test_umull(self):
        mul = 0xffffffff * 2
        pre_c = self.rf.read('APSR_C')
        pre_v = self.rf.read('APSR_V')
        self.assertEqual(self.rf.read('R1'), mul & Mask(32))
        self.assertEqual(self.rf.read('R2'), mul >> 32)
        self._checkFlagsNZCV(0, 0, pre_c, pre_v)

    @itest_setregs("R1=2", "R2=2")
    @itest("UMULLS R1, R2, R1, R2")
    def test_umull_still32(self):
        mul = 2 * 2
        pre_c = self.rf.read('APSR_C')
        pre_v = self.rf.read('APSR_V')
        self.assertEqual(self.rf.read('R1'), mul & Mask(32))
        self.assertEqual(self.rf.read('R2'), mul >> 32)
        self._checkFlagsNZCV(0, 0, pre_c, pre_v)

    @itest_setregs("R1=0xfffffffe", "R2=0xfffffffe")
    @itest("UMULLS R1, R2, R1, R2")
    def test_umull_max(self):
        mul = 0xfffffffe ** 2
        pre_c = self.rf.read('APSR_C')
        pre_v = self.rf.read('APSR_V')
        self.assertEqual(self.rf.read('R1'), mul & Mask(32))
        self.assertEqual(self.rf.read('R2'), mul >> 32)
        self._checkFlagsNZCV(1, 0, pre_c, pre_v)

    @itest_setregs("R1=3", "R2=0")
    @itest("UMULLS R1, R2, R1, R2")
    def test_umull_z(self):
        mul = 3 * 0
        pre_c = self.rf.read('APSR_C')
        pre_v = self.rf.read('APSR_V')
        self.assertEqual(self.rf.read('R1'), mul & Mask(32))
        self.assertEqual(self.rf.read('R2'), (mul >> 32) & Mask(32))
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
        self.cpu.write_register('R2', 0)
        self.cpu.execute()
        self.assertEqual(self.cpu.R2, 0x55555)

    @itest_setregs("R1=0x45", "R2=0x55555555")
    @itest("uxtb r1, r2")
    def test_uxtb(self):
        self.assertEqual(self.cpu.R2, 0x55555555)
        self.assertEqual(self.cpu.R1, 0x55)
