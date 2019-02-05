import unittest

from capstone import CS_MODE_ARM
from functools import wraps
from keystone import Ks, KS_ARCH_ARM64, KS_MODE_LITTLE_ENDIAN

from manticore.core.smtlib import *
from manticore.native.memory import SMemory64, Memory64
from manticore.native.cpu.aarch64 import Aarch64Cpu as Cpu
from manticore.native.cpu.bitwise import LSL
from .test_armv7cpu import itest_custom, itest_setregs
from .test_armv7unicorn import emulate_next
from .test_aarch64rf import MAGIC_64, MAGIC_32

ks = Ks(KS_ARCH_ARM64, KS_MODE_LITTLE_ENDIAN)

def assemble(asm):
    ords = ks.asm(asm)[0]
    if not ords:
        raise Exception(f"Bad assembly: '{asm}'")
    return ''.join(map(chr, ords))


# XXX: These functions are taken from 'test_armv7cpu' and modified to be more
# generic, to support running under Unicorn and Manticore from the same test
# definitions.  It would be nice to do the same for Armv7 code as well.

def itest(asm):
    def instr_dec(assertions_func):
        @wraps(assertions_func)
        def wrapper(self):
            self._setupCpu(asm)
            self._execute()
            assertions_func(self)

        return wrapper

    return instr_dec


def itest_multiple(asms):
    def instr_dec(assertions_func):
        @wraps(assertions_func)
        def wrapper(self):
            self._setupCpu(asms, mode=CS_MODE_ARM, multiple_insts=True)
            for i in range(len(asms)):
                self._execute()
            assertions_func(self)

        return wrapper

    return instr_dec


class Aarch64Instructions:
    _multiprocess_can_split_ = True

    def _setupCpu(self, asm, mode=CS_MODE_ARM, multiple_insts=False):
        if mode != CS_MODE_ARM:
            raise Exception(f"Unsupported mode: '{mode}'")

        # XXX: Adapted from the Armv7 test code.
        self.code = self.mem.mmap(0x1000, 0x1000, 'rwx')
        self.data = self.mem.mmap(0xd000, 0x1000, 'rw')
        # Some tests rely on SP being in a particular range, so make sure that
        # all tests work before changing this.
        self.stack = self.mem.mmap(0x7ffffffffffff000, 0x1000, 'rw')

        start = self.code
        if multiple_insts:
            offset = 0
            for asm_single in asm:
                asm_inst = assemble(asm_single)
                self.mem.write(start + offset, asm_inst)
                offset += len(asm_inst)
        else:
            self.mem.write(start, assemble(asm))

        self.rf.write('PC', start)
        self.rf.write('SP', self.stack + 0x1000)
        self.cpu.mode = mode


    # MOV (register).

    @itest_setregs("X1=42")
    @itest("mov x0, x1")
    def test_mov_reg(self):
        self.assertEqual(self.rf.read('X0'), 42)
        self.assertEqual(self.rf.read('W0'), 42)

    @itest_setregs("W1=42")
    @itest("mov w0, w1")
    def test_mov_reg32(self):
        self.assertEqual(self.rf.read('X0'), 42)
        self.assertEqual(self.rf.read('W0'), 42)


    # MOV (to/from SP).

    @itest_setregs(f"X0={MAGIC_64}")
    @itest("mov sp, x0")
    def test_mov_to_sp(self):
        self.assertEqual(self.rf.read('SP'), MAGIC_64)
        self.assertEqual(self.rf.read('WSP'), MAGIC_32)

    @itest_custom("mov x0, sp")
    def test_mov_from_sp(self):
        # Do not overwrite SP with '_setupCpu'.
        self.rf.write('SP', MAGIC_64)
        self.cpu.execute()
        self.assertEqual(self.rf.read('X0'), MAGIC_64)
        self.assertEqual(self.rf.read('W0'), MAGIC_32)

    @itest_setregs(f"W0={MAGIC_32}")
    @itest("mov wsp, w0")
    def test_mov_to_sp32(self):
        self.assertEqual(self.rf.read('SP'), MAGIC_32)
        self.assertEqual(self.rf.read('WSP'), MAGIC_32)

    @itest_custom("mov w0, wsp")
    def test_mov_from_sp32(self):
        # Do not overwrite WSP with '_setupCpu'.
        self.rf.write('WSP', MAGIC_32)
        self.cpu.execute()
        self.assertEqual(self.rf.read('X0'), MAGIC_32)
        self.assertEqual(self.rf.read('W0'), MAGIC_32)


    # LDR (literal).

    @itest_custom('ldr w0, .+8')
    def test_ldr_lit32(self):
        self.cpu.STACK = self.cpu.PC + 16
        self.cpu.push_int(0x4142434445464748)
        self.cpu.execute()
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_custom('ldr x0, .+8')
    def test_ldr_lit64(self):
        self.cpu.STACK = self.cpu.PC + 16
        self.cpu.push_int(0x4142434445464748)
        self.cpu.execute()
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)

    @itest_custom('ldr w0, .-8')
    def test_ldr_lit_neg32(self):
        insn = self.mem.read(self.code, 4)
        self.mem.write(self.code + 16, insn)
        self.cpu.PC += 16
        self.cpu.STACK = self.cpu.PC
        self.cpu.push_int(0x4142434445464748)
        self.cpu.execute()
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_custom('ldr x0, .-8')
    def test_ldr_lit_neg64(self):
        insn = self.mem.read(self.code, 4)
        self.mem.write(self.code + 16, insn)
        self.cpu.PC += 16
        self.cpu.STACK = self.cpu.PC
        self.cpu.push_int(0x4142434445464748)
        self.cpu.execute()
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)


    # LDR (register).

    # 32-bit.

    @itest_setregs('W1=-8')
    @itest_custom('ldr w0, [sp, w1, uxtw]')
    def test_ldr_reg_uxtw32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        # Account for -8 (0xfffffff8) being treated like a large positive value
        # after zero extension to 64 bits.
        self.cpu.STACK -= 0xfffffff8
        self.cpu.execute()
        self.assertEqual(self.rf.read('W0'), 0x55565758)

    @itest_setregs('W1=-8')
    @itest_custom('ldr w0, [sp, w1, uxtw #2]')
    def test_ldr_reg_uxtw2_32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        # Account for -8 (0xfffffff8) being treated like a large positive value
        # after zero extension to 64 bits.
        self.cpu.STACK -= LSL(0xfffffff8, 2, 32)
        self.cpu.execute()
        self.assertEqual(self.rf.read('W0'), 0x55565758)

    @itest_setregs('X1=8')
    @itest_custom('ldr w0, [sp, x1]')
    def test_ldr_reg32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.execute()
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=2')
    @itest_custom('ldr w0, [sp, x1, lsl #2]')
    def test_ldr_reg_lsl32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.execute()
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('W1=-8')
    @itest_custom('ldr w0, [sp, w1, sxtw]')
    def test_ldr_reg_sxtw32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 8
        self.cpu.execute()
        self.assertEqual(self.rf.read('W0'), 0x55565758)

    @itest_setregs('W1=-8')
    @itest_custom('ldr w0, [sp, w1, sxtw #2]')
    def test_ldr_reg_sxtw2_32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += LSL(8, 2, 32)
        self.cpu.execute()
        self.assertEqual(self.rf.read('W0'), 0x55565758)

    @itest_setregs('X1=-8')
    @itest_custom('ldr w0, [sp, x1, sxtx]')
    def test_ldr_reg_sxtx32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 8
        self.cpu.execute()
        self.assertEqual(self.rf.read('W0'), 0x55565758)

    @itest_setregs('X1=-2')
    @itest_custom('ldr w0, [sp, x1, sxtx #2]')
    def test_ldr_reg_sxtx2_32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 8
        self.cpu.execute()
        self.assertEqual(self.rf.read('W0'), 0x55565758)

    # 64-bit.

    @itest_setregs('W1=-8')
    @itest_custom('ldr x0, [sp, w1, uxtw]')
    def test_ldr_reg_uxtw64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        # Account for -8 (0xfffffff8) being treated like a large positive value
        # after zero extension to 64 bits.
        self.cpu.STACK -= 0xfffffff8
        self.cpu.execute()
        self.assertEqual(self.rf.read('X0'), 0x5152535455565758)

    @itest_setregs('W1=-8')
    @itest_custom('ldr x0, [sp, w1, uxtw #3]')
    def test_ldr_reg_uxtw3_64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        # Account for -8 (0xfffffff8) being treated like a large positive value
        # after zero extension to 64 bits.
        self.cpu.STACK -= LSL(0xfffffff8, 3, 32)
        self.cpu.execute()
        self.assertEqual(self.rf.read('X0'), 0x5152535455565758)

    @itest_setregs('X1=8')
    @itest_custom('ldr x0, [sp, x1]')
    def test_ldr_reg64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.execute()
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)

    @itest_setregs('X1=2')
    @itest_custom('ldr x0, [sp, x1, lsl #3]')
    def test_ldr_reg_lsl64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.execute()
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)

    @itest_setregs('W1=-8')
    @itest_custom('ldr x0, [sp, w1, sxtw]')
    def test_ldr_reg_sxtw64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 8
        self.cpu.execute()
        self.assertEqual(self.rf.read('X0'), 0x5152535455565758)

    @itest_setregs('W1=-8')
    @itest_custom('ldr x0, [sp, w1, sxtw #3]')
    def test_ldr_reg_sxtw3_64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += LSL(8, 3, 32)
        self.cpu.execute()
        self.assertEqual(self.rf.read('X0'), 0x5152535455565758)

    @itest_setregs('X1=-8')
    @itest_custom('ldr x0, [sp, x1, sxtx]')
    def test_ldr_reg_sxtx_64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 8
        self.cpu.execute()
        self.assertEqual(self.rf.read('X0'), 0x5152535455565758)

    @itest_setregs('X1=-2')
    @itest_custom('ldr x0, [sp, x1, sxtx #3]')
    def test_ldr_reg_sxtx3_64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 16
        self.cpu.execute()
        self.assertEqual(self.rf.read('X0'), 0x5152535455565758)


    # Unimplemented.

    @itest("mov x0, #43")
    def test_mov_imm(self):
        self.assertEqual(self.rf.read('X0'), 43)
        self.assertEqual(self.rf.read('W0'), 43)

    # This immediate doesn't fit in 16-bits.  The instruction should be
    # interpreted as 'movn x0, #0'.
    @itest("mov x0, #0xffffffffffffffff")
    def test_mov_imm64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    @itest("movn x0, #0")
    def test_movn_imm(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    @itest_multiple(["movn x0, #0", "mov w0, #1"])
    def test_mov_same_reg32(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)

    @itest_multiple(["movn x0, #0", "movk w0, #1"])
    def test_movk_same_reg32(self):
        self.assertEqual(self.rf.read('X0'), 0xffff0001)
        self.assertEqual(self.rf.read('W0'), 0xffff0001)

    @itest_multiple(["movn x0, #0", "movk x0, #1"])
    def test_movk_same_reg64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffffffff0001)
        self.assertEqual(self.rf.read('W0'), 0xffff0001)

class Aarch64CpuInstructions(unittest.TestCase, Aarch64Instructions):
    def setUp(self):
        # XXX: Adapted from the Armv7 test code.
        cs = ConstraintSet()
        self.cpu = Cpu(SMemory64(cs))
        self.mem = self.cpu.memory
        self.rf = self.cpu.regfile

    def _execute(self):
        self.cpu.execute()

class Aarch64UnicornInstructions(unittest.TestCase, Aarch64Instructions):
    def setUp(self):
        # XXX: Adapted from the Armv7 test code.
        self.cpu = Cpu(Memory64())
        self.mem = self.cpu.memory
        self.rf = self.cpu.regfile

    def _execute(self):
        emulate_next(self.cpu)
