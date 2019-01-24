import unittest

from capstone import CS_MODE_ARM
from keystone import Ks, KS_ARCH_ARM64, KS_MODE_LITTLE_ENDIAN

from manticore.core.smtlib import *
from manticore.native.memory import SMemory32
from manticore.native.cpu.aarch64 import Aarch64Cpu as Cpu
from .test_armv7cpu import itest, itest_setregs

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

    # XXX: Support multiple instructions.
    def _setupCpu(self, asm, mode=CS_MODE_ARM):
        if mode != CS_MODE_ARM:
            raise Exception(f"Unsupported mode: '{mode}'")

        # XXX: Copied from the Armv7 test code.
        self.code = self.mem.mmap(0x1000, 0x1000, 'rwx')
        self.data = self.mem.mmap(0xd000, 0x1000, 'rw')
        self.stack = self.mem.mmap(0xf000, 0x1000, 'rw')

        start = self.code + 4

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
