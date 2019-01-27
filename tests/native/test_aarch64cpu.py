import unittest

from capstone import CS_MODE_ARM
from keystone import Ks, KS_ARCH_ARM64, KS_MODE_LITTLE_ENDIAN

from manticore.core.smtlib import *
from manticore.native.memory import SMemory32
from manticore.native.cpu.aarch64 import Aarch64Cpu as Cpu
from .test_armv7cpu import itest, itest_setregs, itest_multiple

ks = Ks(KS_ARCH_ARM64, KS_MODE_LITTLE_ENDIAN)

def assemble(asm):
    ords = ks.asm(asm)[0]
    if not ords:
        raise Exception(f"Bad assembly: '{asm}'")
    return ''.join(map(chr, ords))


class Aarch64CpuInstructions(unittest.TestCase):
    _multiprocess_can_split_ = True

    def setUp(self):
        # XXX: Copied from the Armv7 test code.
        # XXX: Should this use 'SMemory32'?
        cs = ConstraintSet()
        self.cpu = Cpu(SMemory32(cs))
        self.mem = self.cpu.memory
        self.rf = self.cpu.regfile

    def _setupCpu(self, asm, mode=CS_MODE_ARM, multiple_insts=False):
        if mode != CS_MODE_ARM:
            raise Exception(f"Unsupported mode: '{mode}'")

        # XXX: Copied from the Armv7 test code.
        self.code = self.mem.mmap(0x1000, 0x1000, 'rwx')
        self.data = self.mem.mmap(0xd000, 0x1000, 'rw')
        self.stack = self.mem.mmap(0xf000, 0x1000, 'rw')

        start = self.code + 4
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

    @itest_setregs("X1=42")
    @itest("mov x0, x1")
    def test_mov_reg(self):
        self.assertEqual(self.rf.read('X0'), 42)

    @itest("mov x0, #43")
    def test_mov_imm(self):
        self.assertEqual(self.rf.read('X0'), 43)

    # This immediate doesn't fit in 16-bits.  The instruction should be
    # interpreted as 'movn x0, #0'.
    @itest("mov x0, #0xffffffffffffffff")
    def test_mov_imm64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffffffffffff)

    @itest("movn x0, #0")
    def test_movn_imm(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffffffffffff)

    @itest_multiple(["movn x0, #0", "mov w0, #1"])
    def test_mov_same_reg32(self):
        self.assertEqual(self.rf.read('X0'), 1)

    @itest_multiple(["movn x0, #0", "movk w0, #1"])
    def test_movk_same_reg32(self):
        self.assertEqual(self.rf.read('X0'), 0xffff0001)

    @itest_multiple(["movn x0, #0", "movk x0, #1"])
    def test_movk_same_reg64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffffffff0001)
