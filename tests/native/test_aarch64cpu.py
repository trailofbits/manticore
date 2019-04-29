import unittest

from capstone import CS_MODE_ARM
from functools import wraps
from keystone import Ks, KS_ARCH_ARM64, KS_MODE_LITTLE_ENDIAN
from nose.tools import nottest

from manticore.core.smtlib import *
from manticore.native.memory import SMemory64, Memory64
from manticore.native.cpu.aarch64 import Aarch64Cpu as Cpu
from manticore.native.cpu.abstractcpu import (
    Interruption, InstructionNotImplementedError, ConcretizeRegister
)
from manticore.native.cpu.bitwise import LSL, Mask
from manticore.utils.fallback_emulator import UnicornEmulator
from tests.native.test_aarch64rf import MAGIC_64, MAGIC_32

ks = Ks(KS_ARCH_ARM64, KS_MODE_LITTLE_ENDIAN)


def assemble(asm):
    ords = ks.asm(asm)[0]
    if not ords:
        raise Exception(f"Bad assembly: '{asm}'")
    return ''.join(map(chr, ords))


# XXX: These functions are taken from 'test_armv7cpu' and modified to be more
# generic, to support running under Unicorn and Manticore from the same test
# definitions.  It would be nice to do the same for Armv7 code as well.


def itest_setregs(*preds):
    def instr_dec(custom_func):
        @wraps(custom_func)
        def wrapper(self):
            for p in preds:
                dest, src = p.split('=')

                try:
                    src = int(src, 0)
                except ValueError:
                    self.fail()

                self._setreg(dest, src)

            custom_func(self)

        return wrapper

    return instr_dec


def skip_sym(msg):
    def instr_dec(assertions_func):
        @wraps(assertions_func)
        def wrapper(self):
            if self.__class__.__name__ == 'Aarch64SymInstructions':
                self.skipTest(msg)

        return wrapper

    return instr_dec


def itest(asm):
    def instr_dec(assertions_func):
        @wraps(assertions_func)
        def wrapper(self):
            self._setupCpu(asm)
            self._execute()
            assertions_func(self)

        return wrapper

    return instr_dec


def itest_custom(asms, multiple_insts=False):
    def instr_dec(custom_func):
        @wraps(custom_func)
        def wrapper(self):
            self._setupCpu(
                asms,
                mode=CS_MODE_ARM,
                multiple_insts=multiple_insts
            )
            custom_func(self)

        return wrapper

    return instr_dec


def itest_multiple(asms, count=None):
    def instr_dec(assertions_func):
        @wraps(assertions_func)
        def wrapper(self):
            self._setupCpu(asms, mode=CS_MODE_ARM, multiple_insts=True)
            for i in range(count if count else len(asms)):
                self._execute()
            assertions_func(self)

        return wrapper

    return instr_dec


NZCV_COND_MAP = {
    # name: (true, false)
    'eq': (0x40000000, 0xb0000000),
    'ne': (0xb0000000, 0x40000000),
    'cs': (0x20000000, 0xd0000000),
    'hs': (0x20000000, 0xd0000000),
    'cc': (0xd0000000, 0x20000000),
    'lo': (0xd0000000, 0x20000000),
    'mi': (0x80000000, 0x70000000),
    'pl': (0x70000000, 0x80000000),
    'vs': (0x10000000, 0xe0000000),
    'vc': (0xe0000000, 0x10000000),
    'hi': (0x20000000, 0x40000000),
    'ls': (0x40000000, 0x20000000),
    'ge': (0xd0000000, 0xc0000000),
    'lt': (0xc0000000, 0xd0000000),
    'gt': (0x90000000, 0xd0000000),
    'le': (0xd0000000, 0x90000000),
    'al': (0xf0000000, None),
    'nv': (0, None)
}


# XXX: Armv7 also has these methods: stack_pop, stack_push, stack_peek.
class Aarch64CpuTest(unittest.TestCase):
    # XXX: Adapted from the Armv7 test code.
    _multiprocess_can_split_ = True

    def setUp(self):
        cs = ConstraintSet()
        self.cpu = Cpu(SMemory64(cs))
        self.rf = self.cpu.regfile
        self._setupStack()

    def _setupStack(self):
        self.stack = self.cpu.memory.mmap(0xf000, 0x1000, 'rw')
        self.rf.write('SP', self.stack + 0x1000)

    def test_read_init(self):
        self.assertEqual(self.rf.read('X0'), 0)

    def test_read_stack(self):
        self.cpu.STACK = 0x1337
        self.assertEqual(self.rf.read('SP'), 0x1337)

    def test_read_stack2(self):
        self.cpu.STACK = 0x1337 - 1
        self.assertEqual(self.rf.read('SP'), 0x1336)

    def test_read_stack3(self):
        self.cpu.STACK = 0x1337 + 1
        self.assertEqual(self.rf.read('SP'), 0x1338)

    def test_read_stack4(self):
        self.cpu.STACK = 0x1337
        self.assertEqual(self.cpu.STACK, 0x1337)

    def test_write_read_int(self):
        self.cpu.STACK -= 8
        self.cpu.write_int(self.cpu.STACK, MAGIC_64, 64)
        self.assertEqual(self.cpu.read_int(self.cpu.STACK), MAGIC_64)


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
        self.rf.write('SP', self.stack + 0x1000 - 8)
        self.cpu.mode = mode

    def _setreg(self, reg, val):
        reg = reg.upper()

        if self.mem.__class__.__name__ == 'Memory64':
            self.rf.write(reg, val)
        elif self.mem.__class__.__name__ == 'SMemory64':
            size = self.rf.size(reg)
            self.rf.write(reg, self.cs.new_bitvec(size, name=reg))
            self.cs.add(self.rf.read(reg) == val)
        else:
            self.fail()

    # ADD (extended register).

    # 32-bit.

    @itest_setregs('W1=0x41424344', 'W2=0x51525384')
    @itest('add w0, w1, w2, uxtb')
    def test_add_ext_reg_uxtb32(self):
        self.assertEqual(self.rf.read('X0'), 0x414243c8)
        self.assertEqual(self.rf.read('W0'), 0x414243c8)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51525384')
    @itest('add w0, w1, w2, uxtb #0')
    def test_add_ext_reg_uxtb0_32(self):
        self.assertEqual(self.rf.read('X0'), 0x414243c8)
        self.assertEqual(self.rf.read('W0'), 0x414243c8)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51525384')
    @itest('add w0, w1, w2, uxtb #4')
    def test_add_ext_reg_uxtb4_32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424b84)
        self.assertEqual(self.rf.read('W0'), 0x41424b84)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51528354')
    @itest('add w0, w1, w2, uxth')
    def test_add_ext_reg_uxth32(self):
        self.assertEqual(self.rf.read('X0'), 0x4142c698)
        self.assertEqual(self.rf.read('W0'), 0x4142c698)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51528354')
    @itest('add w0, w1, w2, uxth #0')
    def test_add_ext_reg_uxth0_32(self):
        self.assertEqual(self.rf.read('X0'), 0x4142c698)
        self.assertEqual(self.rf.read('W0'), 0x4142c698)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51528354')
    @itest('add w0, w1, w2, uxth #4')
    def test_add_ext_reg_uxth4_32(self):
        self.assertEqual(self.rf.read('X0'), 0x414a7884)
        self.assertEqual(self.rf.read('W0'), 0x414a7884)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('add w0, w1, w2, uxtw')
    def test_add_ext_reg_uxtw32(self):
        self.assertEqual(self.rf.read('X0'), 0xc2949698)
        self.assertEqual(self.rf.read('W0'), 0xc2949698)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('add w0, w1, w2, uxtw #0')
    def test_add_ext_reg_uxtw0_32(self):
        self.assertEqual(self.rf.read('X0'), 0xc2949698)
        self.assertEqual(self.rf.read('W0'), 0xc2949698)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('add w0, w1, w2, uxtw #4')
    def test_add_ext_reg_uxtw4_32(self):
        self.assertEqual(self.rf.read('X0'), 0x56677884)
        self.assertEqual(self.rf.read('W0'), 0x56677884)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('add w0, w1, w2, uxtx')
    def test_add_ext_reg_uxtx32(self):
        self.assertEqual(self.rf.read('X0'), 0xc2949698)
        self.assertEqual(self.rf.read('W0'), 0xc2949698)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('add w0, w1, w2, uxtx #0')
    def test_add_ext_reg_uxtx0_32(self):
        self.assertEqual(self.rf.read('X0'), 0xc2949698)
        self.assertEqual(self.rf.read('W0'), 0xc2949698)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('add w0, w1, w2, uxtx #4')
    def test_add_ext_reg_uxtx4_32(self):
        self.assertEqual(self.rf.read('X0'), 0x56677884)
        self.assertEqual(self.rf.read('W0'), 0x56677884)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51525384')
    @itest('add w0, w1, w2, sxtb')
    def test_add_ext_reg_sxtb32(self):
        self.assertEqual(self.rf.read('X0'), 0x414242c8)
        self.assertEqual(self.rf.read('W0'), 0x414242c8)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51525384')
    @itest('add w0, w1, w2, sxtb #0')
    def test_add_ext_reg_sxtb0_32(self):
        self.assertEqual(self.rf.read('X0'), 0x414242c8)
        self.assertEqual(self.rf.read('W0'), 0x414242c8)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51525384')
    @itest('add w0, w1, w2, sxtb #4')
    def test_add_ext_reg_sxtb4_32(self):
        self.assertEqual(self.rf.read('X0'), 0x41423b84)
        self.assertEqual(self.rf.read('W0'), 0x41423b84)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51528354')
    @itest('add w0, w1, w2, sxth')
    def test_add_ext_reg_sxth32(self):
        self.assertEqual(self.rf.read('X0'), 0x4141c698)
        self.assertEqual(self.rf.read('W0'), 0x4141c698)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51528354')
    @itest('add w0, w1, w2, sxth #0')
    def test_add_ext_reg_sxth0_32(self):
        self.assertEqual(self.rf.read('X0'), 0x4141c698)
        self.assertEqual(self.rf.read('W0'), 0x4141c698)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51528354')
    @itest('add w0, w1, w2, sxth #4')
    def test_add_ext_reg_sxth4_32(self):
        self.assertEqual(self.rf.read('X0'), 0x413a7884)
        self.assertEqual(self.rf.read('W0'), 0x413a7884)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('add w0, w1, w2, sxtw')
    def test_add_ext_reg_sxtw32(self):
        self.assertEqual(self.rf.read('X0'), 0xc2949698)
        self.assertEqual(self.rf.read('W0'), 0xc2949698)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('add w0, w1, w2, sxtw #0')
    def test_add_ext_reg_sxtw0_32(self):
        self.assertEqual(self.rf.read('X0'), 0xc2949698)
        self.assertEqual(self.rf.read('W0'), 0xc2949698)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('add w0, w1, w2, sxtw #4')
    def test_add_ext_reg_sxtw4_32(self):
        self.assertEqual(self.rf.read('X0'), 0x56677884)
        self.assertEqual(self.rf.read('W0'), 0x56677884)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('add w0, w1, w2, sxtx')
    def test_add_ext_reg_sxtx32(self):
        self.assertEqual(self.rf.read('X0'), 0xc2949698)
        self.assertEqual(self.rf.read('W0'), 0xc2949698)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('add w0, w1, w2, sxtx #0')
    def test_add_ext_reg_sxtx0_32(self):
        self.assertEqual(self.rf.read('X0'), 0xc2949698)
        self.assertEqual(self.rf.read('W0'), 0xc2949698)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('add w0, w1, w2, sxtx #4')
    def test_add_ext_reg_sxtx4_32(self):
        self.assertEqual(self.rf.read('X0'), 0x56677884)
        self.assertEqual(self.rf.read('W0'), 0x56677884)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('add w0, w1, w2, lsl #0')
    def test_add_ext_reg_lsl0_32(self):
        self.assertEqual(self.rf.read('X0'), 0xc2949698)
        self.assertEqual(self.rf.read('W0'), 0xc2949698)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('add w0, w1, w2, lsl #4')
    def test_add_ext_reg_lsl4_32(self):
        self.assertEqual(self.rf.read('X0'), 0x56677884)
        self.assertEqual(self.rf.read('W0'), 0x56677884)
        self.assertEqual(self.rf.read('NZCV'), 0)

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51525384')
    @itest('add x0, x1, w2, uxtb')
    def test_add_ext_reg_uxtb64(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344454647cc)
        self.assertEqual(self.rf.read('W0'), 0x454647cc)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51525384')
    @itest('add x0, x1, w2, uxtb #0')
    def test_add_ext_reg_uxtb0_64(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344454647cc)
        self.assertEqual(self.rf.read('W0'), 0x454647cc)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51525384')
    @itest('add x0, x1, w2, uxtb #4')
    def test_add_ext_reg_uxtb4_64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464f88)
        self.assertEqual(self.rf.read('W0'), 0x45464f88)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51528354')
    @itest('add x0, x1, w2, uxth')
    def test_add_ext_reg_uxth64(self):
        self.assertEqual(self.rf.read('X0'), 0x414243444546ca9c)
        self.assertEqual(self.rf.read('W0'), 0x4546ca9c)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51528354')
    @itest('add x0, x1, w2, uxth #0')
    def test_add_ext_reg_uxth0_64(self):
        self.assertEqual(self.rf.read('X0'), 0x414243444546ca9c)
        self.assertEqual(self.rf.read('W0'), 0x4546ca9c)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51528354')
    @itest('add x0, x1, w2, uxth #4')
    def test_add_ext_reg_uxth4_64(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344454e7c88)
        self.assertEqual(self.rf.read('W0'), 0x454e7c88)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x81525354')
    @itest('add x0, x1, w2, uxtw')
    def test_add_ext_reg_uxtw64(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344c6989a9c)
        self.assertEqual(self.rf.read('W0'), 0xc6989a9c)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x81525354')
    @itest('add x0, x1, w2, uxtw #0')
    def test_add_ext_reg_uxtw0_64(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344c6989a9c)
        self.assertEqual(self.rf.read('W0'), 0xc6989a9c)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x81525354')
    @itest('add x0, x1, w2, uxtw #4')
    def test_add_ext_reg_uxtw4_64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434c5a6b7c88)
        self.assertEqual(self.rf.read('W0'), 0x5a6b7c88)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('add x0, x1, x2, uxtx')
    def test_add_ext_reg_uxtx64(self):
        self.assertEqual(self.rf.read('X0'), 0xc29496989a9c9ea0)
        self.assertEqual(self.rf.read('W0'), 0x9a9c9ea0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('add x0, x1, x2, uxtx #0')
    def test_add_ext_reg_uxtx0_64(self):
        self.assertEqual(self.rf.read('X0'), 0xc29496989a9c9ea0)
        self.assertEqual(self.rf.read('W0'), 0x9a9c9ea0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('add x0, x1, x2, uxtx #4')
    def test_add_ext_reg_uxtx4_64(self):
        self.assertEqual(self.rf.read('X0'), 0x566778899aabbcc8)
        self.assertEqual(self.rf.read('W0'), 0x9aabbcc8)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51525384')
    @itest('add x0, x1, w2, sxtb')
    def test_add_ext_reg_sxtb64(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344454646cc)
        self.assertEqual(self.rf.read('W0'), 0x454646cc)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51525384')
    @itest('add x0, x1, w2, sxtb #0')
    def test_add_ext_reg_sxtb0_64(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344454646cc)
        self.assertEqual(self.rf.read('W0'), 0x454646cc)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51525384')
    @itest('add x0, x1, w2, sxtb #4')
    def test_add_ext_reg_sxtb4_64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445463f88)
        self.assertEqual(self.rf.read('W0'), 0x45463f88)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51528354')
    @itest('add x0, x1, w2, sxth')
    def test_add_ext_reg_sxth64(self):
        self.assertEqual(self.rf.read('X0'), 0x414243444545ca9c)
        self.assertEqual(self.rf.read('W0'), 0x4545ca9c)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51528354')
    @itest('add x0, x1, w2, sxth #0')
    def test_add_ext_reg_sxth0_64(self):
        self.assertEqual(self.rf.read('X0'), 0x414243444545ca9c)
        self.assertEqual(self.rf.read('W0'), 0x4545ca9c)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51528354')
    @itest('add x0, x1, w2, sxth #4')
    def test_add_ext_reg_sxth4_64(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344453e7c88)
        self.assertEqual(self.rf.read('W0'), 0x453e7c88)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x81525354')
    @itest('add x0, x1, w2, sxtw')
    def test_add_ext_reg_sxtw64(self):
        self.assertEqual(self.rf.read('X0'), 0x41424343c6989a9c)
        self.assertEqual(self.rf.read('W0'), 0xc6989a9c)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x81525354')
    @itest('add x0, x1, w2, sxtw #0')
    def test_add_ext_reg_sxtw0_64(self):
        self.assertEqual(self.rf.read('X0'), 0x41424343c6989a9c)
        self.assertEqual(self.rf.read('W0'), 0xc6989a9c)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x81525354')
    @itest('add x0, x1, w2, sxtw #4')
    def test_add_ext_reg_sxtw4_64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142433c5a6b7c88)
        self.assertEqual(self.rf.read('W0'), 0x5a6b7c88)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('add x0, x1, x2, sxtx')
    def test_add_ext_reg_sxtx64(self):
        self.assertEqual(self.rf.read('X0'), 0xc29496989a9c9ea0)
        self.assertEqual(self.rf.read('W0'), 0x9a9c9ea0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('add x0, x1, x2, sxtx #0')
    def test_add_ext_reg_sxtx0_64(self):
        self.assertEqual(self.rf.read('X0'), 0xc29496989a9c9ea0)
        self.assertEqual(self.rf.read('W0'), 0x9a9c9ea0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('add x0, x1, x2, sxtx #4')
    def test_add_ext_reg_sxtx4_64(self):
        self.assertEqual(self.rf.read('X0'), 0x566778899aabbcc8)
        self.assertEqual(self.rf.read('W0'), 0x9aabbcc8)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('add x0, x1, x2, lsl #0')
    def test_add_ext_reg_lsl0_64(self):
        self.assertEqual(self.rf.read('X0'), 0xc29496989a9c9ea0)
        self.assertEqual(self.rf.read('W0'), 0x9a9c9ea0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('add x0, x1, x2, lsl #4')
    def test_add_ext_reg_lsl4_64(self):
        self.assertEqual(self.rf.read('X0'), 0x566778899aabbcc8)
        self.assertEqual(self.rf.read('W0'), 0x9aabbcc8)
        self.assertEqual(self.rf.read('NZCV'), 0)

    # ADD (immediate).

    # 32-bit.

    @itest_setregs('W1=0x41424344')
    @itest('add w0, w1, #0')
    def test_add_imm_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344')
    @itest('add w0, w1, #4095')
    def test_add_imm_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x41425343)
        self.assertEqual(self.rf.read('W0'), 0x41425343)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344')
    @itest('add w0, w1, #1')
    def test_add_imm32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424345)
        self.assertEqual(self.rf.read('W0'), 0x41424345)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344')
    @itest('add w0, w1, #1, lsl #0')
    def test_add_imm_lsl0_32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424345)
        self.assertEqual(self.rf.read('W0'), 0x41424345)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344')
    @itest('add w0, w1, #1, lsl #12')
    def test_add_imm_lsl12_32(self):
        self.assertEqual(self.rf.read('X0'), 0x41425344)
        self.assertEqual(self.rf.read('W0'), 0x41425344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748')
    @itest('add x0, x1, #0')
    def test_add_imm_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748')
    @itest('add x0, x1, #4095')
    def test_add_imm_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445465747)
        self.assertEqual(self.rf.read('W0'), 0x45465747)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748')
    @itest('add x0, x1, #1')
    def test_add_imm64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464749)
        self.assertEqual(self.rf.read('W0'), 0x45464749)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748')
    @itest('add x0, x1, #1, lsl #0')
    def test_add_imm_lsl0_64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464749)
        self.assertEqual(self.rf.read('W0'), 0x45464749)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748')
    @itest('add x0, x1, #1, lsl #12')
    def test_add_imm_lsl12_64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445465748)
        self.assertEqual(self.rf.read('W0'), 0x45465748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    # ADD (shifted register).

    # 32-bit.

    @itest_setregs('W1=0x41424344', 'W2=0x45464748')
    @itest('add w0, w1, w2')
    def test_add_sft_reg32(self):
        self.assertEqual(self.rf.read('X0'), 0x86888a8c)
        self.assertEqual(self.rf.read('W0'), 0x86888a8c)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x45464748')
    @itest('add w0, w1, w2, lsl #0')
    def test_add_sft_reg_lsl_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x86888a8c)
        self.assertEqual(self.rf.read('W0'), 0x86888a8c)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=1')
    @itest('add w0, w1, w2, lsl #31')
    def test_add_sft_reg_lsl_max32(self):
        self.assertEqual(self.rf.read('X0'), 0xc1424344)
        self.assertEqual(self.rf.read('W0'), 0xc1424344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x45464748')
    @itest('add w0, w1, w2, lsl #1')
    def test_add_sft_reg_lsl32(self):
        self.assertEqual(self.rf.read('X0'), 0xcbced1d4)
        self.assertEqual(self.rf.read('W0'), 0xcbced1d4)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x45464748')
    @itest('add w0, w1, w2, lsr #0')
    def test_add_sft_reg_lsr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x86888a8c)
        self.assertEqual(self.rf.read('W0'), 0x86888a8c)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x80000000')
    @itest('add w0, w1, w2, lsr #31')
    def test_add_sft_reg_lsr_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424345)
        self.assertEqual(self.rf.read('W0'), 0x41424345)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x80000000')
    @itest('add w0, w1, w2, lsr #1')
    def test_add_sft_reg_lsr32(self):
        self.assertEqual(self.rf.read('X0'), 0x81424344)
        self.assertEqual(self.rf.read('W0'), 0x81424344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x45464748')
    @itest('add w0, w1, w2, asr #0')
    def test_add_sft_reg_asr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x86888a8c)
        self.assertEqual(self.rf.read('W0'), 0x86888a8c)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x80000000')
    @itest('add w0, w1, w2, asr #31')
    def test_add_sft_reg_asr_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424343)
        self.assertEqual(self.rf.read('W0'), 0x41424343)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x80000000')
    @itest('add w0, w1, w2, asr #1')
    def test_add_sft_reg_asr32(self):
        self.assertEqual(self.rf.read('X0'), 0x01424344)
        self.assertEqual(self.rf.read('W0'), 0x01424344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748', 'X2=0x5152535455565758')
    @itest('add x0, x1, x2')
    def test_add_sft_reg64(self):
        self.assertEqual(self.rf.read('X0'), 0x929496989a9c9ea0)
        self.assertEqual(self.rf.read('W0'), 0x9a9c9ea0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x5152535455565758')
    @itest('add x0, x1, x2, lsl #0')
    def test_add_sft_reg_lsl_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x929496989a9c9ea0)
        self.assertEqual(self.rf.read('W0'), 0x9a9c9ea0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=1')
    @itest('add x0, x1, x2, lsl #63')
    def test_add_sft_reg_lsl_max64(self):
        self.assertEqual(self.rf.read('X0'), 0xc142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x5152535455565758')
    @itest('add x0, x1, x2, lsl #1')
    def test_add_sft_reg_lsl64(self):
        self.assertEqual(self.rf.read('X0'), 0xe3e6e9eceff2f5f8)
        self.assertEqual(self.rf.read('W0'), 0xeff2f5f8)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x5152535455565758')
    @itest('add x0, x1, x2, lsr #0')
    def test_add_sft_reg_lsr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x929496989a9c9ea0)
        self.assertEqual(self.rf.read('W0'), 0x9a9c9ea0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8000000000000000')
    @itest('add x0, x1, x2, lsr #63')
    def test_add_sft_reg_lsr_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464749)
        self.assertEqual(self.rf.read('W0'), 0x45464749)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8000000000000000')
    @itest('add x0, x1, x2, lsr #1')
    def test_add_sft_reg_lsr64(self):
        self.assertEqual(self.rf.read('X0'), 0x8142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x5152535455565758')
    @itest('add x0, x1, x2, asr #0')
    def test_add_sft_reg_asr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x929496989a9c9ea0)
        self.assertEqual(self.rf.read('W0'), 0x9a9c9ea0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8000000000000000')
    @itest('add x0, x1, x2, asr #63')
    def test_add_sft_reg_asr_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464747)
        self.assertEqual(self.rf.read('W0'), 0x45464747)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8000000000000000')
    @itest('add x0, x1, x2, asr #1')
    def test_add_sft_reg_asr64(self):
        self.assertEqual(self.rf.read('X0'), 0x0142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    # ADD (scalar).

    # XXX: Uses 'reset'.

    @itest_setregs(
        'V1=0x41424344454647485152535455565758',
        'V2=0x61626364656667687172737475767778'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'add d0, d1, d2'],
        multiple_insts=True
    )
    def test_add_scalar(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xc2c4c6c8caccced0)
        self.assertEqual(self.rf.read('Q0'), 0xc2c4c6c8caccced0)
        self.assertEqual(self.rf.read('D0'), 0xc2c4c6c8caccced0)
        self.assertEqual(self.rf.read('S0'), 0xcaccced0)
        self.assertEqual(self.rf.read('H0'), 0xced0)
        self.assertEqual(self.rf.read('B0'), 0xd0)

    @itest_setregs(
        'V1=0xffffffffffffffffffffffffffffffff',
        'V2=0xffffffffffffffffffffffffffffffff'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'add d0, d1, d2'],
        multiple_insts=True
    )
    def test_add_scalar_max(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xfffffffffffffffe)
        self.assertEqual(self.rf.read('Q0'), 0xfffffffffffffffe)
        self.assertEqual(self.rf.read('D0'), 0xfffffffffffffffe)
        self.assertEqual(self.rf.read('S0'), 0xfffffffe)
        self.assertEqual(self.rf.read('H0'), 0xfffe)
        self.assertEqual(self.rf.read('B0'), 0xfe)

    # ADD (vector).

    # XXX: Uses 'reset'.

    # 8b.

    @itest_setregs(
        'V1=0x41424344454647485152535455565758',
        'V2=0x61626364656667687172737475767778'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'add v0.8b, v1.8b, v2.8b'],
        multiple_insts=True
    )
    def test_add_vector_8b(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xc2c4c6c8caccced0)
        self.assertEqual(self.rf.read('Q0'), 0xc2c4c6c8caccced0)
        self.assertEqual(self.rf.read('D0'), 0xc2c4c6c8caccced0)
        self.assertEqual(self.rf.read('S0'), 0xcaccced0)
        self.assertEqual(self.rf.read('H0'), 0xced0)
        self.assertEqual(self.rf.read('B0'), 0xd0)

    @itest_setregs(
        'V1=0xffffffffffffffffffffffffffffffff',
        'V2=0xffffffffffffffffffffffffffffffff'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'add v0.8b, v1.8b, v2.8b'],
        multiple_insts=True
    )
    def test_add_vector_8b_max(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xfefefefefefefefe)
        self.assertEqual(self.rf.read('Q0'), 0xfefefefefefefefe)
        self.assertEqual(self.rf.read('D0'), 0xfefefefefefefefe)
        self.assertEqual(self.rf.read('S0'), 0xfefefefe)
        self.assertEqual(self.rf.read('H0'), 0xfefe)
        self.assertEqual(self.rf.read('B0'), 0xfe)

    # 16b.

    @itest_setregs(
        'V1=0x41424344454647485152535455565758',
        'V2=0x61626364656667687172737475767778'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'add v0.16b, v1.16b, v2.16b'],
        multiple_insts=True
    )
    def test_add_vector_16b(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xa2a4a6a8aaacaeb0c2c4c6c8caccced0)
        self.assertEqual(self.rf.read('Q0'), 0xa2a4a6a8aaacaeb0c2c4c6c8caccced0)
        self.assertEqual(self.rf.read('D0'), 0xc2c4c6c8caccced0)
        self.assertEqual(self.rf.read('S0'), 0xcaccced0)
        self.assertEqual(self.rf.read('H0'), 0xced0)
        self.assertEqual(self.rf.read('B0'), 0xd0)

    @itest_setregs(
        'V1=0xffffffffffffffffffffffffffffffff',
        'V2=0xffffffffffffffffffffffffffffffff'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'add v0.16b, v1.16b, v2.16b'],
        multiple_insts=True
    )
    def test_add_vector_16b_max(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xfefefefefefefefefefefefefefefefe)
        self.assertEqual(self.rf.read('Q0'), 0xfefefefefefefefefefefefefefefefe)
        self.assertEqual(self.rf.read('D0'), 0xfefefefefefefefe)
        self.assertEqual(self.rf.read('S0'), 0xfefefefe)
        self.assertEqual(self.rf.read('H0'), 0xfefe)
        self.assertEqual(self.rf.read('B0'), 0xfe)

    # 4h.

    @itest_setregs(
        'V1=0x41424344454647485152535455565758',
        'V2=0x61626364656667687172737475767778'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'add v0.4h, v1.4h, v2.4h'],
        multiple_insts=True
    )
    def test_add_vector_4h(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xc2c4c6c8caccced0)
        self.assertEqual(self.rf.read('Q0'), 0xc2c4c6c8caccced0)
        self.assertEqual(self.rf.read('D0'), 0xc2c4c6c8caccced0)
        self.assertEqual(self.rf.read('S0'), 0xcaccced0)
        self.assertEqual(self.rf.read('H0'), 0xced0)
        self.assertEqual(self.rf.read('B0'), 0xd0)

    @itest_setregs(
        'V1=0xffffffffffffffffffffffffffffffff',
        'V2=0xffffffffffffffffffffffffffffffff'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'add v0.4h, v1.4h, v2.4h'],
        multiple_insts=True
    )
    def test_add_vector_4h_max(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xfffefffefffefffe)
        self.assertEqual(self.rf.read('Q0'), 0xfffefffefffefffe)
        self.assertEqual(self.rf.read('D0'), 0xfffefffefffefffe)
        self.assertEqual(self.rf.read('S0'), 0xfffefffe)
        self.assertEqual(self.rf.read('H0'), 0xfffe)
        self.assertEqual(self.rf.read('B0'), 0xfe)

    # 8h.

    @itest_setregs(
        'V1=0x41424344454647485152535455565758',
        'V2=0x61626364656667687172737475767778'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'add v0.8h, v1.8h, v2.8h'],
        multiple_insts=True
    )
    def test_add_vector_8h(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xa2a4a6a8aaacaeb0c2c4c6c8caccced0)
        self.assertEqual(self.rf.read('Q0'), 0xa2a4a6a8aaacaeb0c2c4c6c8caccced0)
        self.assertEqual(self.rf.read('D0'), 0xc2c4c6c8caccced0)
        self.assertEqual(self.rf.read('S0'), 0xcaccced0)
        self.assertEqual(self.rf.read('H0'), 0xced0)
        self.assertEqual(self.rf.read('B0'), 0xd0)

    @itest_setregs(
        'V1=0xffffffffffffffffffffffffffffffff',
        'V2=0xffffffffffffffffffffffffffffffff'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'add v0.8h, v1.8h, v2.8h'],
        multiple_insts=True
    )
    def test_add_vector_8h_max(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xfffefffefffefffefffefffefffefffe)
        self.assertEqual(self.rf.read('Q0'), 0xfffefffefffefffefffefffefffefffe)
        self.assertEqual(self.rf.read('D0'), 0xfffefffefffefffe)
        self.assertEqual(self.rf.read('S0'), 0xfffefffe)
        self.assertEqual(self.rf.read('H0'), 0xfffe)
        self.assertEqual(self.rf.read('B0'), 0xfe)

    # 2s.

    @itest_setregs(
        'V1=0x41424344454647485152535455565758',
        'V2=0x61626364656667687172737475767778'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'add v0.2s, v1.2s, v2.2s'],
        multiple_insts=True
    )
    def test_add_vector_2s(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xc2c4c6c8caccced0)
        self.assertEqual(self.rf.read('Q0'), 0xc2c4c6c8caccced0)
        self.assertEqual(self.rf.read('D0'), 0xc2c4c6c8caccced0)
        self.assertEqual(self.rf.read('S0'), 0xcaccced0)
        self.assertEqual(self.rf.read('H0'), 0xced0)
        self.assertEqual(self.rf.read('B0'), 0xd0)

    @itest_setregs(
        'V1=0xffffffffffffffffffffffffffffffff',
        'V2=0xffffffffffffffffffffffffffffffff'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'add v0.2s, v1.2s, v2.2s'],
        multiple_insts=True
    )
    def test_add_vector_2s_max(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xfffffffefffffffe)
        self.assertEqual(self.rf.read('Q0'), 0xfffffffefffffffe)
        self.assertEqual(self.rf.read('D0'), 0xfffffffefffffffe)
        self.assertEqual(self.rf.read('S0'), 0xfffffffe)
        self.assertEqual(self.rf.read('H0'), 0xfffe)
        self.assertEqual(self.rf.read('B0'), 0xfe)

    # 4s.

    @itest_setregs(
        'V1=0x41424344454647485152535455565758',
        'V2=0x61626364656667687172737475767778'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'add v0.4s, v1.4s, v2.4s'],
        multiple_insts=True
    )
    def test_add_vector_4s(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xa2a4a6a8aaacaeb0c2c4c6c8caccced0)
        self.assertEqual(self.rf.read('Q0'), 0xa2a4a6a8aaacaeb0c2c4c6c8caccced0)
        self.assertEqual(self.rf.read('D0'), 0xc2c4c6c8caccced0)
        self.assertEqual(self.rf.read('S0'), 0xcaccced0)
        self.assertEqual(self.rf.read('H0'), 0xced0)
        self.assertEqual(self.rf.read('B0'), 0xd0)

    @itest_setregs(
        'V1=0xffffffffffffffffffffffffffffffff',
        'V2=0xffffffffffffffffffffffffffffffff'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'add v0.4s, v1.4s, v2.4s'],
        multiple_insts=True
    )
    def test_add_vector_4s_max(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xfffffffefffffffefffffffefffffffe)
        self.assertEqual(self.rf.read('Q0'), 0xfffffffefffffffefffffffefffffffe)
        self.assertEqual(self.rf.read('D0'), 0xfffffffefffffffe)
        self.assertEqual(self.rf.read('S0'), 0xfffffffe)
        self.assertEqual(self.rf.read('H0'), 0xfffe)
        self.assertEqual(self.rf.read('B0'), 0xfe)

    # 2d.

    @itest_setregs(
        'V1=0x41424344454647485152535455565758',
        'V2=0x61626364656667687172737475767778'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'add v0.2d, v1.2d, v2.2d'],
        multiple_insts=True
    )
    def test_add_vector_2d(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xa2a4a6a8aaacaeb0c2c4c6c8caccced0)
        self.assertEqual(self.rf.read('Q0'), 0xa2a4a6a8aaacaeb0c2c4c6c8caccced0)
        self.assertEqual(self.rf.read('D0'), 0xc2c4c6c8caccced0)
        self.assertEqual(self.rf.read('S0'), 0xcaccced0)
        self.assertEqual(self.rf.read('H0'), 0xced0)
        self.assertEqual(self.rf.read('B0'), 0xd0)

    @itest_setregs(
        'V1=0xffffffffffffffffffffffffffffffff',
        'V2=0xffffffffffffffffffffffffffffffff'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'add v0.2d, v1.2d, v2.2d'],
        multiple_insts=True
    )
    def test_add_vector_2d_max(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xfffffffffffffffefffffffffffffffe)
        self.assertEqual(self.rf.read('Q0'), 0xfffffffffffffffefffffffffffffffe)
        self.assertEqual(self.rf.read('D0'), 0xfffffffffffffffe)
        self.assertEqual(self.rf.read('S0'), 0xfffffffe)
        self.assertEqual(self.rf.read('H0'), 0xfffe)
        self.assertEqual(self.rf.read('B0'), 0xfe)

    # ADDP (scalar).

    # XXX: Uses 'reset'.

    @itest_setregs('V1=0x41424344454647485152535455565758')
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'addp d0, v1.2d'],
        multiple_insts=True
    )
    def test_addp_scalar(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0x929496989a9c9ea0)
        self.assertEqual(self.rf.read('Q0'), 0x929496989a9c9ea0)
        self.assertEqual(self.rf.read('D0'), 0x929496989a9c9ea0)
        self.assertEqual(self.rf.read('S0'), 0x9a9c9ea0)
        self.assertEqual(self.rf.read('H0'), 0x9ea0)
        self.assertEqual(self.rf.read('B0'), 0xa0)

    @itest_setregs('V1=0xffffffffffffffffffffffffffffffff')
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'addp d0, v1.2d'],
        multiple_insts=True
    )
    def test_addp_scalar_max(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xfffffffffffffffe)
        self.assertEqual(self.rf.read('Q0'), 0xfffffffffffffffe)
        self.assertEqual(self.rf.read('D0'), 0xfffffffffffffffe)
        self.assertEqual(self.rf.read('S0'), 0xfffffffe)
        self.assertEqual(self.rf.read('H0'), 0xfffe)
        self.assertEqual(self.rf.read('B0'), 0xfe)

    # ADDP (vector).

    # 8b.

    @itest_setregs(
        'V1=0x41424344454647485152535455565758',
        'V2=0x61626364656667687172737475767778'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'addp v0.8b, v1.8b, v2.8b'],
        multiple_insts=True
    )
    def test_addp_vector_8b(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xe3e7ebefa3a7abaf)
        self.assertEqual(self.rf.read('Q0'), 0xe3e7ebefa3a7abaf)
        self.assertEqual(self.rf.read('D0'), 0xe3e7ebefa3a7abaf)
        self.assertEqual(self.rf.read('S0'), 0xa3a7abaf)
        self.assertEqual(self.rf.read('H0'), 0xabaf)
        self.assertEqual(self.rf.read('B0'), 0xaf)

    @itest_setregs(
        'V1=0xffffffffffffffffffffffffffffffff',
        'V2=0xffffffffffffffffffffffffffffffff'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'addp v0.8b, v1.8b, v2.8b'],
        multiple_insts=True
    )
    def test_addp_vector_8b_max(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xfefefefefefefefe)
        self.assertEqual(self.rf.read('Q0'), 0xfefefefefefefefe)
        self.assertEqual(self.rf.read('D0'), 0xfefefefefefefefe)
        self.assertEqual(self.rf.read('S0'), 0xfefefefe)
        self.assertEqual(self.rf.read('H0'), 0xfefe)
        self.assertEqual(self.rf.read('B0'), 0xfe)

    # 16b.

    @itest_setregs(
        'V1=0x41424344454647485152535455565758',
        'V2=0x61626364656667687172737475767778'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'addp v0.16b, v1.16b, v2.16b'],
        multiple_insts=True
    )
    def test_addp_vector_16b(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xc3c7cbcfe3e7ebef83878b8fa3a7abaf)
        self.assertEqual(self.rf.read('Q0'), 0xc3c7cbcfe3e7ebef83878b8fa3a7abaf)
        self.assertEqual(self.rf.read('D0'), 0x83878b8fa3a7abaf)
        self.assertEqual(self.rf.read('S0'), 0xa3a7abaf)
        self.assertEqual(self.rf.read('H0'), 0xabaf)
        self.assertEqual(self.rf.read('B0'), 0xaf)

    @itest_setregs(
        'V1=0xffffffffffffffffffffffffffffffff',
        'V2=0xffffffffffffffffffffffffffffffff'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'addp v0.16b, v1.16b, v2.16b'],
        multiple_insts=True
    )
    def test_addp_vector_16b_max(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xfefefefefefefefefefefefefefefefe)
        self.assertEqual(self.rf.read('Q0'), 0xfefefefefefefefefefefefefefefefe)
        self.assertEqual(self.rf.read('D0'), 0xfefefefefefefefe)
        self.assertEqual(self.rf.read('S0'), 0xfefefefe)
        self.assertEqual(self.rf.read('H0'), 0xfefe)
        self.assertEqual(self.rf.read('B0'), 0xfe)

    # 4h.

    @itest_setregs(
        'V1=0x41424344454647485152535455565758',
        'V2=0x61626364656667687172737475767778'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'addp v0.4h, v1.4h, v2.4h'],
        multiple_insts=True
    )
    def test_addp_vector_4h(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xe4e6eceea4a6acae)
        self.assertEqual(self.rf.read('Q0'), 0xe4e6eceea4a6acae)
        self.assertEqual(self.rf.read('D0'), 0xe4e6eceea4a6acae)
        self.assertEqual(self.rf.read('S0'), 0xa4a6acae)
        self.assertEqual(self.rf.read('H0'), 0xacae)
        self.assertEqual(self.rf.read('B0'), 0xae)

    @itest_setregs(
        'V1=0xffffffffffffffffffffffffffffffff',
        'V2=0xffffffffffffffffffffffffffffffff'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'addp v0.4h, v1.4h, v2.4h'],
        multiple_insts=True
    )
    def test_addp_vector_4h_max(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xfffefffefffefffe)
        self.assertEqual(self.rf.read('Q0'), 0xfffefffefffefffe)
        self.assertEqual(self.rf.read('D0'), 0xfffefffefffefffe)
        self.assertEqual(self.rf.read('S0'), 0xfffefffe)
        self.assertEqual(self.rf.read('H0'), 0xfffe)
        self.assertEqual(self.rf.read('B0'), 0xfe)

    # 8h.

    @itest_setregs(
        'V1=0x41424344454647485152535455565758',
        'V2=0x61626364656667687172737475767778'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'addp v0.8h, v1.8h, v2.8h'],
        multiple_insts=True
    )
    def test_addp_vector_8h(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xc4c6cccee4e6ecee84868c8ea4a6acae)
        self.assertEqual(self.rf.read('Q0'), 0xc4c6cccee4e6ecee84868c8ea4a6acae)
        self.assertEqual(self.rf.read('D0'), 0x84868c8ea4a6acae)
        self.assertEqual(self.rf.read('S0'), 0xa4a6acae)
        self.assertEqual(self.rf.read('H0'), 0xacae)
        self.assertEqual(self.rf.read('B0'), 0xae)

    @itest_setregs(
        'V1=0xffffffffffffffffffffffffffffffff',
        'V2=0xffffffffffffffffffffffffffffffff'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'addp v0.8h, v1.8h, v2.8h'],
        multiple_insts=True
    )
    def test_addp_vector_8h_max(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xfffefffefffefffefffefffefffefffe)
        self.assertEqual(self.rf.read('Q0'), 0xfffefffefffefffefffefffefffefffe)
        self.assertEqual(self.rf.read('D0'), 0xfffefffefffefffe)
        self.assertEqual(self.rf.read('S0'), 0xfffefffe)
        self.assertEqual(self.rf.read('H0'), 0xfffe)
        self.assertEqual(self.rf.read('B0'), 0xfe)

    # 2s.

    @itest_setregs(
        'V1=0x41424344454647485152535455565758',
        'V2=0x61626364656667687172737475767778'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'addp v0.2s, v1.2s, v2.2s'],
        multiple_insts=True
    )
    def test_addp_vector_2s(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xe6e8eaeca6a8aaac)
        self.assertEqual(self.rf.read('Q0'), 0xe6e8eaeca6a8aaac)
        self.assertEqual(self.rf.read('D0'), 0xe6e8eaeca6a8aaac)
        self.assertEqual(self.rf.read('S0'), 0xa6a8aaac)
        self.assertEqual(self.rf.read('H0'), 0xaaac)
        self.assertEqual(self.rf.read('B0'), 0xac)

    @itest_setregs(
        'V1=0xffffffffffffffffffffffffffffffff',
        'V2=0xffffffffffffffffffffffffffffffff'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'addp v0.2s, v1.2s, v2.2s'],
        multiple_insts=True
    )
    def test_addp_vector_2s_max(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xfffffffefffffffe)
        self.assertEqual(self.rf.read('Q0'), 0xfffffffefffffffe)
        self.assertEqual(self.rf.read('D0'), 0xfffffffefffffffe)
        self.assertEqual(self.rf.read('S0'), 0xfffffffe)
        self.assertEqual(self.rf.read('H0'), 0xfffe)
        self.assertEqual(self.rf.read('B0'), 0xfe)

    # 4s.

    @itest_setregs(
        'V1=0x41424344454647485152535455565758',
        'V2=0x61626364656667687172737475767778'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'addp v0.4s, v1.4s, v2.4s'],
        multiple_insts=True
    )
    def test_addp_vector_4s(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xc6c8cacce6e8eaec86888a8ca6a8aaac)
        self.assertEqual(self.rf.read('Q0'), 0xc6c8cacce6e8eaec86888a8ca6a8aaac)
        self.assertEqual(self.rf.read('D0'), 0x86888a8ca6a8aaac)
        self.assertEqual(self.rf.read('S0'), 0xa6a8aaac)
        self.assertEqual(self.rf.read('H0'), 0xaaac)
        self.assertEqual(self.rf.read('B0'), 0xac)

    @itest_setregs(
        'V1=0xffffffffffffffffffffffffffffffff',
        'V2=0xffffffffffffffffffffffffffffffff'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'addp v0.4s, v1.4s, v2.4s'],
        multiple_insts=True
    )
    def test_addp_vector_4s_max(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xfffffffefffffffefffffffefffffffe)
        self.assertEqual(self.rf.read('Q0'), 0xfffffffefffffffefffffffefffffffe)
        self.assertEqual(self.rf.read('D0'), 0xfffffffefffffffe)
        self.assertEqual(self.rf.read('S0'), 0xfffffffe)
        self.assertEqual(self.rf.read('H0'), 0xfffe)
        self.assertEqual(self.rf.read('B0'), 0xfe)

    # 2d.

    @itest_setregs(
        'V1=0x41424344454647485152535455565758',
        'V2=0x61626364656667687172737475767778'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'addp v0.2d, v1.2d, v2.2d'],
        multiple_insts=True
    )
    def test_addp_vector_2d(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xd2d4d6d8dadcdee0929496989a9c9ea0)
        self.assertEqual(self.rf.read('Q0'), 0xd2d4d6d8dadcdee0929496989a9c9ea0)
        self.assertEqual(self.rf.read('D0'), 0x929496989a9c9ea0)
        self.assertEqual(self.rf.read('S0'), 0x9a9c9ea0)
        self.assertEqual(self.rf.read('H0'), 0x9ea0)
        self.assertEqual(self.rf.read('B0'), 0xa0)

    @itest_setregs(
        'V1=0xffffffffffffffffffffffffffffffff',
        'V2=0xffffffffffffffffffffffffffffffff'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'addp v0.2d, v1.2d, v2.2d'],
        multiple_insts=True
    )
    def test_addp_vector_2d_max(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xfffffffffffffffefffffffffffffffe)
        self.assertEqual(self.rf.read('Q0'), 0xfffffffffffffffefffffffffffffffe)
        self.assertEqual(self.rf.read('D0'), 0xfffffffffffffffe)
        self.assertEqual(self.rf.read('S0'), 0xfffffffe)
        self.assertEqual(self.rf.read('H0'), 0xfffe)
        self.assertEqual(self.rf.read('B0'), 0xfe)

    # ADDS (extended register).

    # 32-bit.

    @itest_setregs('W1=0x41424344', 'W2=0x51525384')
    @itest('adds w0, w1, w2, uxtb')
    def test_adds_ext_reg_uxtb32(self):
        self.assertEqual(self.rf.read('X0'), 0x414243c8)
        self.assertEqual(self.rf.read('W0'), 0x414243c8)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51525384')
    @itest('adds w0, w1, w2, uxtb #0')
    def test_adds_ext_reg_uxtb0_32(self):
        self.assertEqual(self.rf.read('X0'), 0x414243c8)
        self.assertEqual(self.rf.read('W0'), 0x414243c8)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51525384')
    @itest('adds w0, w1, w2, uxtb #4')
    def test_adds_ext_reg_uxtb4_32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424b84)
        self.assertEqual(self.rf.read('W0'), 0x41424b84)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51528354')
    @itest('adds w0, w1, w2, uxth')
    def test_adds_ext_reg_uxth32(self):
        self.assertEqual(self.rf.read('X0'), 0x4142c698)
        self.assertEqual(self.rf.read('W0'), 0x4142c698)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51528354')
    @itest('adds w0, w1, w2, uxth #0')
    def test_adds_ext_reg_uxth0_32(self):
        self.assertEqual(self.rf.read('X0'), 0x4142c698)
        self.assertEqual(self.rf.read('W0'), 0x4142c698)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51528354')
    @itest('adds w0, w1, w2, uxth #4')
    def test_adds_ext_reg_uxth4_32(self):
        self.assertEqual(self.rf.read('X0'), 0x414a7884)
        self.assertEqual(self.rf.read('W0'), 0x414a7884)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('adds w0, w1, w2, uxtw')
    def test_adds_ext_reg_uxtw32(self):
        self.assertEqual(self.rf.read('X0'), 0xc2949698)
        self.assertEqual(self.rf.read('W0'), 0xc2949698)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('adds w0, w1, w2, uxtw #0')
    def test_adds_ext_reg_uxtw0_32(self):
        self.assertEqual(self.rf.read('X0'), 0xc2949698)
        self.assertEqual(self.rf.read('W0'), 0xc2949698)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('adds w0, w1, w2, uxtw #4')
    def test_adds_ext_reg_uxtw4_32(self):
        self.assertEqual(self.rf.read('X0'), 0x56677884)
        self.assertEqual(self.rf.read('W0'), 0x56677884)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('adds w0, w1, w2, uxtx')
    def test_adds_ext_reg_uxtx32(self):
        self.assertEqual(self.rf.read('X0'), 0xc2949698)
        self.assertEqual(self.rf.read('W0'), 0xc2949698)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('adds w0, w1, w2, uxtx #0')
    def test_adds_ext_reg_uxtx0_32(self):
        self.assertEqual(self.rf.read('X0'), 0xc2949698)
        self.assertEqual(self.rf.read('W0'), 0xc2949698)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('adds w0, w1, w2, uxtx #4')
    def test_adds_ext_reg_uxtx4_32(self):
        self.assertEqual(self.rf.read('X0'), 0x56677884)
        self.assertEqual(self.rf.read('W0'), 0x56677884)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51525384')
    @itest('adds w0, w1, w2, sxtb')
    def test_adds_ext_reg_sxtb32(self):
        self.assertEqual(self.rf.read('X0'), 0x414242c8)
        self.assertEqual(self.rf.read('W0'), 0x414242c8)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344', 'W2=0x51525384')
    @itest('adds w0, w1, w2, sxtb #0')
    def test_adds_ext_reg_sxtb0_32(self):
        self.assertEqual(self.rf.read('X0'), 0x414242c8)
        self.assertEqual(self.rf.read('W0'), 0x414242c8)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344', 'W2=0x51525384')
    @itest('adds w0, w1, w2, sxtb #4')
    def test_adds_ext_reg_sxtb4_32(self):
        self.assertEqual(self.rf.read('X0'), 0x41423b84)
        self.assertEqual(self.rf.read('W0'), 0x41423b84)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344', 'W2=0x51528354')
    @itest('adds w0, w1, w2, sxth')
    def test_adds_ext_reg_sxth32(self):
        self.assertEqual(self.rf.read('X0'), 0x4141c698)
        self.assertEqual(self.rf.read('W0'), 0x4141c698)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344', 'W2=0x51528354')
    @itest('adds w0, w1, w2, sxth #0')
    def test_adds_ext_reg_sxth0_32(self):
        self.assertEqual(self.rf.read('X0'), 0x4141c698)
        self.assertEqual(self.rf.read('W0'), 0x4141c698)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344', 'W2=0x51528354')
    @itest('adds w0, w1, w2, sxth #4')
    def test_adds_ext_reg_sxth4_32(self):
        self.assertEqual(self.rf.read('X0'), 0x413a7884)
        self.assertEqual(self.rf.read('W0'), 0x413a7884)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('adds w0, w1, w2, sxtw')
    def test_adds_ext_reg_sxtw32(self):
        self.assertEqual(self.rf.read('X0'), 0xc2949698)
        self.assertEqual(self.rf.read('W0'), 0xc2949698)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('adds w0, w1, w2, sxtw #0')
    def test_adds_ext_reg_sxtw0_32(self):
        self.assertEqual(self.rf.read('X0'), 0xc2949698)
        self.assertEqual(self.rf.read('W0'), 0xc2949698)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('adds w0, w1, w2, sxtw #4')
    def test_adds_ext_reg_sxtw4_32(self):
        self.assertEqual(self.rf.read('X0'), 0x56677884)
        self.assertEqual(self.rf.read('W0'), 0x56677884)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('adds w0, w1, w2, sxtx')
    def test_adds_ext_reg_sxtx32(self):
        self.assertEqual(self.rf.read('X0'), 0xc2949698)
        self.assertEqual(self.rf.read('W0'), 0xc2949698)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('adds w0, w1, w2, sxtx #0')
    def test_adds_ext_reg_sxtx0_32(self):
        self.assertEqual(self.rf.read('X0'), 0xc2949698)
        self.assertEqual(self.rf.read('W0'), 0xc2949698)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('adds w0, w1, w2, sxtx #4')
    def test_adds_ext_reg_sxtx4_32(self):
        self.assertEqual(self.rf.read('X0'), 0x56677884)
        self.assertEqual(self.rf.read('W0'), 0x56677884)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('adds w0, w1, w2, lsl #0')
    def test_adds_ext_reg_lsl0_32(self):
        self.assertEqual(self.rf.read('X0'), 0xc2949698)
        self.assertEqual(self.rf.read('W0'), 0xc2949698)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('adds w0, w1, w2, lsl #4')
    def test_adds_ext_reg_lsl4_32(self):
        self.assertEqual(self.rf.read('X0'), 0x56677884)
        self.assertEqual(self.rf.read('W0'), 0x56677884)
        self.assertEqual(self.rf.read('NZCV'), 0)

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51525384')
    @itest('adds x0, x1, w2, uxtb')
    def test_adds_ext_reg_uxtb64(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344454647cc)
        self.assertEqual(self.rf.read('W0'), 0x454647cc)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51525384')
    @itest('adds x0, x1, w2, uxtb #0')
    def test_adds_ext_reg_uxtb0_64(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344454647cc)
        self.assertEqual(self.rf.read('W0'), 0x454647cc)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51525384')
    @itest('adds x0, x1, w2, uxtb #4')
    def test_adds_ext_reg_uxtb4_64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464f88)
        self.assertEqual(self.rf.read('W0'), 0x45464f88)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51528354')
    @itest('adds x0, x1, w2, uxth')
    def test_adds_ext_reg_uxth64(self):
        self.assertEqual(self.rf.read('X0'), 0x414243444546ca9c)
        self.assertEqual(self.rf.read('W0'), 0x4546ca9c)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51528354')
    @itest('adds x0, x1, w2, uxth #0')
    def test_adds_ext_reg_uxth0_64(self):
        self.assertEqual(self.rf.read('X0'), 0x414243444546ca9c)
        self.assertEqual(self.rf.read('W0'), 0x4546ca9c)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51528354')
    @itest('adds x0, x1, w2, uxth #4')
    def test_adds_ext_reg_uxth4_64(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344454e7c88)
        self.assertEqual(self.rf.read('W0'), 0x454e7c88)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x81525354')
    @itest('adds x0, x1, w2, uxtw')
    def test_adds_ext_reg_uxtw64(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344c6989a9c)
        self.assertEqual(self.rf.read('W0'), 0xc6989a9c)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x81525354')
    @itest('adds x0, x1, w2, uxtw #0')
    def test_adds_ext_reg_uxtw0_64(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344c6989a9c)
        self.assertEqual(self.rf.read('W0'), 0xc6989a9c)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x81525354')
    @itest('adds x0, x1, w2, uxtw #4')
    def test_adds_ext_reg_uxtw4_64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434c5a6b7c88)
        self.assertEqual(self.rf.read('W0'), 0x5a6b7c88)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('adds x0, x1, x2, uxtx')
    def test_adds_ext_reg_uxtx64(self):
        self.assertEqual(self.rf.read('X0'), 0xc29496989a9c9ea0)
        self.assertEqual(self.rf.read('W0'), 0x9a9c9ea0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('adds x0, x1, x2, uxtx #0')
    def test_adds_ext_reg_uxtx0_64(self):
        self.assertEqual(self.rf.read('X0'), 0xc29496989a9c9ea0)
        self.assertEqual(self.rf.read('W0'), 0x9a9c9ea0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('adds x0, x1, x2, uxtx #4')
    def test_adds_ext_reg_uxtx4_64(self):
        self.assertEqual(self.rf.read('X0'), 0x566778899aabbcc8)
        self.assertEqual(self.rf.read('W0'), 0x9aabbcc8)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51525384')
    @itest('adds x0, x1, w2, sxtb')
    def test_adds_ext_reg_sxtb64(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344454646cc)
        self.assertEqual(self.rf.read('W0'), 0x454646cc)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51525384')
    @itest('adds x0, x1, w2, sxtb #0')
    def test_adds_ext_reg_sxtb0_64(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344454646cc)
        self.assertEqual(self.rf.read('W0'), 0x454646cc)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51525384')
    @itest('adds x0, x1, w2, sxtb #4')
    def test_adds_ext_reg_sxtb4_64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445463f88)
        self.assertEqual(self.rf.read('W0'), 0x45463f88)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51528354')
    @itest('adds x0, x1, w2, sxth')
    def test_adds_ext_reg_sxth64(self):
        self.assertEqual(self.rf.read('X0'), 0x414243444545ca9c)
        self.assertEqual(self.rf.read('W0'), 0x4545ca9c)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51528354')
    @itest('adds x0, x1, w2, sxth #0')
    def test_adds_ext_reg_sxth0_64(self):
        self.assertEqual(self.rf.read('X0'), 0x414243444545ca9c)
        self.assertEqual(self.rf.read('W0'), 0x4545ca9c)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51528354')
    @itest('adds x0, x1, w2, sxth #4')
    def test_adds_ext_reg_sxth4_64(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344453e7c88)
        self.assertEqual(self.rf.read('W0'), 0x453e7c88)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x81525354')
    @itest('adds x0, x1, w2, sxtw')
    def test_adds_ext_reg_sxtw64(self):
        self.assertEqual(self.rf.read('X0'), 0x41424343c6989a9c)
        self.assertEqual(self.rf.read('W0'), 0xc6989a9c)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x81525354')
    @itest('adds x0, x1, w2, sxtw #0')
    def test_adds_ext_reg_sxtw0_64(self):
        self.assertEqual(self.rf.read('X0'), 0x41424343c6989a9c)
        self.assertEqual(self.rf.read('W0'), 0xc6989a9c)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x81525354')
    @itest('adds x0, x1, w2, sxtw #4')
    def test_adds_ext_reg_sxtw4_64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142433c5a6b7c88)
        self.assertEqual(self.rf.read('W0'), 0x5a6b7c88)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('adds x0, x1, x2, sxtx')
    def test_adds_ext_reg_sxtx64(self):
        self.assertEqual(self.rf.read('X0'), 0xc29496989a9c9ea0)
        self.assertEqual(self.rf.read('W0'), 0x9a9c9ea0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('adds x0, x1, x2, sxtx #0')
    def test_adds_ext_reg_sxtx0_64(self):
        self.assertEqual(self.rf.read('X0'), 0xc29496989a9c9ea0)
        self.assertEqual(self.rf.read('W0'), 0x9a9c9ea0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('adds x0, x1, x2, sxtx #4')
    def test_adds_ext_reg_sxtx4_64(self):
        self.assertEqual(self.rf.read('X0'), 0x566778899aabbcc8)
        self.assertEqual(self.rf.read('W0'), 0x9aabbcc8)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('adds x0, x1, x2, lsl #0')
    def test_adds_ext_reg_lsl0_64(self):
        self.assertEqual(self.rf.read('X0'), 0xc29496989a9c9ea0)
        self.assertEqual(self.rf.read('W0'), 0x9a9c9ea0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('adds x0, x1, x2, lsl #4')
    def test_adds_ext_reg_lsl4_64(self):
        self.assertEqual(self.rf.read('X0'), 0x566778899aabbcc8)
        self.assertEqual(self.rf.read('W0'), 0x9aabbcc8)
        self.assertEqual(self.rf.read('NZCV'), 0)

    # ADDS (immediate).

    # 32-bit.

    @itest_setregs('W1=0x41424344')
    @itest('adds w0, w1, #0')
    def test_adds_imm_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344')
    @itest('adds w0, w1, #4095')
    def test_adds_imm_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x41425343)
        self.assertEqual(self.rf.read('W0'), 0x41425343)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344')
    @itest('adds w0, w1, #1')
    def test_adds_imm32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424345)
        self.assertEqual(self.rf.read('W0'), 0x41424345)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344')
    @itest('adds w0, w1, #1, lsl #0')
    def test_adds_imm_lsl0_32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424345)
        self.assertEqual(self.rf.read('W0'), 0x41424345)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344')
    @itest('adds w0, w1, #1, lsl #12')
    def test_adds_imm_lsl12_32(self):
        self.assertEqual(self.rf.read('X0'), 0x41425344)
        self.assertEqual(self.rf.read('W0'), 0x41425344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748')
    @itest('adds x0, x1, #0')
    def test_adds_imm_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748')
    @itest('adds x0, x1, #4095')
    def test_adds_imm_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445465747)
        self.assertEqual(self.rf.read('W0'), 0x45465747)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748')
    @itest('adds x0, x1, #1')
    def test_adds_imm64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464749)
        self.assertEqual(self.rf.read('W0'), 0x45464749)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748')
    @itest('adds x0, x1, #1, lsl #0')
    def test_adds_imm_lsl0_64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464749)
        self.assertEqual(self.rf.read('W0'), 0x45464749)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748')
    @itest('adds x0, x1, #1, lsl #12')
    def test_adds_imm_lsl12_64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445465748)
        self.assertEqual(self.rf.read('W0'), 0x45465748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    # ADDS (shifted register).

    # 32-bit.

    @itest_setregs('W1=0x41424344', 'W2=0x45464748')
    @itest('adds w0, w1, w2')
    def test_adds_sft_reg32(self):
        self.assertEqual(self.rf.read('X0'), 0x86888a8c)
        self.assertEqual(self.rf.read('W0'), 0x86888a8c)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('W1=0x41424344', 'W2=0x45464748')
    @itest('adds w0, w1, w2, lsl #0')
    def test_adds_sft_reg_lsl_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x86888a8c)
        self.assertEqual(self.rf.read('W0'), 0x86888a8c)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('W1=0x41424344', 'W2=1')
    @itest('adds w0, w1, w2, lsl #31')
    def test_adds_sft_reg_lsl_max32(self):
        self.assertEqual(self.rf.read('X0'), 0xc1424344)
        self.assertEqual(self.rf.read('W0'), 0xc1424344)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0x45464748')
    @itest('adds w0, w1, w2, lsl #1')
    def test_adds_sft_reg_lsl32(self):
        self.assertEqual(self.rf.read('X0'), 0xcbced1d4)
        self.assertEqual(self.rf.read('W0'), 0xcbced1d4)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0x45464748')
    @itest('adds w0, w1, w2, lsr #0')
    def test_adds_sft_reg_lsr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x86888a8c)
        self.assertEqual(self.rf.read('W0'), 0x86888a8c)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('W1=0x41424344', 'W2=0x80000000')
    @itest('adds w0, w1, w2, lsr #31')
    def test_adds_sft_reg_lsr_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424345)
        self.assertEqual(self.rf.read('W0'), 0x41424345)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x80000000')
    @itest('adds w0, w1, w2, lsr #1')
    def test_adds_sft_reg_lsr32(self):
        self.assertEqual(self.rf.read('X0'), 0x81424344)
        self.assertEqual(self.rf.read('W0'), 0x81424344)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('W1=0x41424344', 'W2=0x45464748')
    @itest('adds w0, w1, w2, asr #0')
    def test_adds_sft_reg_asr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x86888a8c)
        self.assertEqual(self.rf.read('W0'), 0x86888a8c)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('W1=0x41424344', 'W2=0x80000000')
    @itest('adds w0, w1, w2, asr #31')
    def test_adds_sft_reg_asr_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424343)
        self.assertEqual(self.rf.read('W0'), 0x41424343)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344', 'W2=0x80000000')
    @itest('adds w0, w1, w2, asr #1')
    def test_adds_sft_reg_asr32(self):
        self.assertEqual(self.rf.read('X0'), 0x01424344)
        self.assertEqual(self.rf.read('W0'), 0x01424344)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748', 'X2=0x5152535455565758')
    @itest('adds x0, x1, x2')
    def test_adds_sft_reg64(self):
        self.assertEqual(self.rf.read('X0'), 0x929496989a9c9ea0)
        self.assertEqual(self.rf.read('W0'), 0x9a9c9ea0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x5152535455565758')
    @itest('adds x0, x1, x2, lsl #0')
    def test_adds_sft_reg_lsl_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x929496989a9c9ea0)
        self.assertEqual(self.rf.read('W0'), 0x9a9c9ea0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=1')
    @itest('adds x0, x1, x2, lsl #63')
    def test_adds_sft_reg_lsl_max64(self):
        self.assertEqual(self.rf.read('X0'), 0xc142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x5152535455565758')
    @itest('adds x0, x1, x2, lsl #1')
    def test_adds_sft_reg_lsl64(self):
        self.assertEqual(self.rf.read('X0'), 0xe3e6e9eceff2f5f8)
        self.assertEqual(self.rf.read('W0'), 0xeff2f5f8)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x5152535455565758')
    @itest('adds x0, x1, x2, lsr #0')
    def test_adds_sft_reg_lsr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x929496989a9c9ea0)
        self.assertEqual(self.rf.read('W0'), 0x9a9c9ea0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8000000000000000')
    @itest('adds x0, x1, x2, lsr #63')
    def test_adds_sft_reg_lsr_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464749)
        self.assertEqual(self.rf.read('W0'), 0x45464749)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8000000000000000')
    @itest('adds x0, x1, x2, lsr #1')
    def test_adds_sft_reg_lsr64(self):
        self.assertEqual(self.rf.read('X0'), 0x8142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x5152535455565758')
    @itest('adds x0, x1, x2, asr #0')
    def test_adds_sft_reg_asr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x929496989a9c9ea0)
        self.assertEqual(self.rf.read('W0'), 0x9a9c9ea0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8000000000000000')
    @itest('adds x0, x1, x2, asr #63')
    def test_adds_sft_reg_asr_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464747)
        self.assertEqual(self.rf.read('W0'), 0x45464747)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8000000000000000')
    @itest('adds x0, x1, x2, asr #1')
    def test_adds_sft_reg_asr64(self):
        self.assertEqual(self.rf.read('X0'), 0x0142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    # ADR.

    @itest_custom('adr x0, .0')
    def test_adr_0(self):
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        self._execute()
        self.assertEqual(self.rf.read('X0'), pc)

    @itest_custom('adr x0, .-8')
    def test_adr_neg(self):
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        self._execute()
        self.assertEqual(self.rf.read('X0'), pc - 8)

    @itest_custom('adr x0, .+8')
    def test_adr_pos(self):
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        self._execute()
        self.assertEqual(self.rf.read('X0'), pc + 8)

    # ADRP.

    @itest_custom('adrp x0, .0')
    def test_adrp_0(self):
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        self._execute()
        self.assertEqual(self.rf.read('X0'), pc)

    @itest_custom('adrp x0, .-0x1000')
    def test_adrp_neg(self):
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        self._execute()
        self.assertEqual(self.rf.read('X0'), pc - 0x1000)

    @itest_custom('adrp x0, .+0x1000')
    def test_adrp_pos(self):
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        self._execute()
        self.assertEqual(self.rf.read('X0'), pc + 0x1000)

    # AND (immediate).

    # 32-bit.

    @itest_setregs('W1=0x41424344')
    @itest('and w0, w1, #0xffff')
    def test_and_imm32(self):
        self.assertEqual(self.rf.read('X0'), 0x4344)
        self.assertEqual(self.rf.read('W0'), 0x4344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344')
    @itest('and w0, w1, #0xffff0000')
    def test_and_imm2_32(self):
        self.assertEqual(self.rf.read('X0'), 0x41420000)
        self.assertEqual(self.rf.read('W0'), 0x41420000)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x44434241')
    @itest('and w0, w1, #1')
    def test_and_imm3_32(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)
        self.assertEqual(self.rf.read('NZCV'), 0)

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748')
    @itest('and x0, x1, #0xffff0000ffff0000')
    def test_and_imm64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142000045460000)
        self.assertEqual(self.rf.read('W0'), 0x45460000)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748')
    @itest('and x0, x1, #0x0000ffff0000ffff')
    def test_and_imm2_64(self):
        self.assertEqual(self.rf.read('X0'), 0x434400004748)
        self.assertEqual(self.rf.read('W0'), 0x4748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4847464544434241')
    @itest('and x0, x1, #1')
    def test_and_imm3_64(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)
        self.assertEqual(self.rf.read('NZCV'), 0)

    # AND (shifted register).

    # 32-bit.

    @itest_setregs('W1=0x4142ffff', 'W2=0xffff4344')
    @itest('and w0, w1, w2')
    def test_and_sft_reg32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x4142ffff', 'W2=0xffff4344')
    @itest('and w0, w1, w2, lsl #0')
    def test_and_sft_reg_lsl_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0xffffffff', 'W2=0x80000001')
    @itest('and w0, w1, w2, lsl #31')
    def test_and_sft_reg_lsl_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x80000000)
        self.assertEqual(self.rf.read('W0'), 0x80000000)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0xffffffff', 'W2=0x81424344')
    @itest('and w0, w1, w2, lsl #4')
    def test_and_sft_reg_lsl32(self):
        self.assertEqual(self.rf.read('X0'), 0x14243440)
        self.assertEqual(self.rf.read('W0'), 0x14243440)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x4142ffff', 'W2=0xffff4344')
    @itest('and w0, w1, w2, lsr #0')
    def test_and_sft_reg_lsr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0xffffffff', 'W2=0x80000001')
    @itest('and w0, w1, w2, lsr #31')
    def test_and_sft_reg_lsr_max32(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0xffffffff', 'W2=0x81424344')
    @itest('and w0, w1, w2, lsr #4')
    def test_and_sft_reg_lsr32(self):
        self.assertEqual(self.rf.read('X0'), 0x8142434)
        self.assertEqual(self.rf.read('W0'), 0x8142434)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x4142ffff', 'W2=0xffff4344')
    @itest('and w0, w1, w2, asr #0')
    def test_and_sft_reg_asr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0xffffffff', 'W2=0x80000001')
    @itest('and w0, w1, w2, asr #31')
    def test_and_sft_reg_asr_max32(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0xffffffff', 'W2=0x81424344')
    @itest('and w0, w1, w2, asr #4')
    def test_and_sft_reg_asr32(self):
        self.assertEqual(self.rf.read('X0'), 0xf8142434)
        self.assertEqual(self.rf.read('W0'), 0xf8142434)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x4142ffff', 'W2=0xffff4344')
    @itest('and w0, w1, w2, ror #0')
    def test_and_sft_reg_ror_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0xffffffff', 'W2=0x80000001')
    @itest('and w0, w1, w2, ror #31')
    def test_and_sft_reg_ror_max32(self):
        self.assertEqual(self.rf.read('X0'), 3)
        self.assertEqual(self.rf.read('W0'), 3)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0xffffffff', 'W2=0x81424344')
    @itest('and w0, w1, w2, ror #4')
    def test_and_sft_reg_ror32(self):
        self.assertEqual(self.rf.read('X0'), 0x48142434)
        self.assertEqual(self.rf.read('W0'), 0x48142434)
        self.assertEqual(self.rf.read('NZCV'), 0)

    # 64-bit.

    @itest_setregs('X1=0x41424344ffffffff', 'X2=0xffffffff45464748')
    @itest('and x0, x1, x2')
    def test_and_sft_reg64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x41424344ffffffff', 'X2=0xffffffff45464748')
    @itest('and x0, x1, x2, lsl #0')
    def test_and_sft_reg_lsl_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8000000000000001')
    @itest('and x0, x1, x2, lsl #63')
    def test_and_sft_reg_lsl_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x8000000000000000)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8142434445464748')
    @itest('and x0, x1, x2, lsl #4')
    def test_and_sft_reg_lsl64(self):
        self.assertEqual(self.rf.read('X0'), 0x1424344454647480)
        self.assertEqual(self.rf.read('W0'), 0x54647480)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x41424344ffffffff', 'X2=0xffffffff45464748')
    @itest('and x0, x1, x2, lsr #0')
    def test_and_sft_reg_lsr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8000000000000001')
    @itest('and x0, x1, x2, lsr #63')
    def test_and_sft_reg_lsr_max64(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8142434445464748')
    @itest('and x0, x1, x2, lsr #4')
    def test_and_sft_reg_lsr64(self):
        self.assertEqual(self.rf.read('X0'), 0x814243444546474)
        self.assertEqual(self.rf.read('W0'), 0x44546474)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x41424344ffffffff', 'X2=0xffffffff45464748')
    @itest('and x0, x1, x2, asr #0')
    def test_and_sft_reg_asr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8000000000000001')
    @itest('and x0, x1, x2, asr #63')
    def test_and_sft_reg_asr_max64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8142434445464748')
    @itest('and x0, x1, x2, asr #4')
    def test_and_sft_reg_asr64(self):
        self.assertEqual(self.rf.read('X0'), 0xf814243444546474)
        self.assertEqual(self.rf.read('W0'), 0x44546474)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x41424344ffffffff', 'X2=0xffffffff45464748')
    @itest('and x0, x1, x2, ror #0')
    def test_and_sft_reg_ror_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8000000000000001')
    @itest('and x0, x1, x2, ror #63')
    def test_and_sft_reg_ror_max64(self):
        self.assertEqual(self.rf.read('X0'), 3)
        self.assertEqual(self.rf.read('W0'), 3)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8142434445464748')
    @itest('and x0, x1, x2, ror #4')
    def test_and_sft_reg_ror64(self):
        self.assertEqual(self.rf.read('X0'), 0x8814243444546474)
        self.assertEqual(self.rf.read('W0'), 0x44546474)
        self.assertEqual(self.rf.read('NZCV'), 0)

    # AND (vector).

    # XXX: Uses 'reset'.

    # 8b.

    @itest_setregs(
        'V1=0x41424344454647485152535455565758',
        'V2=0x61626364656667687172737475767778'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'and v0.8b, v1.8b, v2.8b'],
        multiple_insts=True
    )
    def test_and_vector_8b(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0x5152535455565758)
        self.assertEqual(self.rf.read('Q0'), 0x5152535455565758)
        self.assertEqual(self.rf.read('D0'), 0x5152535455565758)
        self.assertEqual(self.rf.read('S0'), 0x55565758)
        self.assertEqual(self.rf.read('H0'), 0x5758)
        self.assertEqual(self.rf.read('B0'), 0x58)

    @itest_setregs(
        'V1=0xffffffffffffffffffffffffffffffff',
        'V2=0xffffffffffffffffffffffffffffffff'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'and v0.8b, v1.8b, v2.8b'],
        multiple_insts=True
    )
    def test_and_vector_8b_max(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('Q0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('D0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('S0'), 0xffffffff)
        self.assertEqual(self.rf.read('H0'), 0xffff)
        self.assertEqual(self.rf.read('B0'), 0xff)

    # 16b.

    @itest_setregs(
        'V1=0x41424344454647485152535455565758',
        'V2=0x61626364656667687172737475767778'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'and v0.16b, v1.16b, v2.16b'],
        multiple_insts=True
    )
    def test_and_vector_16b(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0x41424344454647485152535455565758)
        self.assertEqual(self.rf.read('Q0'), 0x41424344454647485152535455565758)
        self.assertEqual(self.rf.read('D0'), 0x5152535455565758)
        self.assertEqual(self.rf.read('S0'), 0x55565758)
        self.assertEqual(self.rf.read('H0'), 0x5758)
        self.assertEqual(self.rf.read('B0'), 0x58)

    @itest_setregs(
        'V1=0xffffffffffffffffffffffffffffffff',
        'V2=0xffffffffffffffffffffffffffffffff'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'and v0.16b, v1.16b, v2.16b'],
        multiple_insts=True
    )
    def test_and_vector_16b_max(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xffffffffffffffffffffffffffffffff)
        self.assertEqual(self.rf.read('Q0'), 0xffffffffffffffffffffffffffffffff)
        self.assertEqual(self.rf.read('D0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('S0'), 0xffffffff)
        self.assertEqual(self.rf.read('H0'), 0xffff)
        self.assertEqual(self.rf.read('B0'), 0xff)

    # ANDS (immediate).

    # 32-bit.

    @itest_setregs('W1=0x41424344')
    @itest('ands w0, w1, #0xffff')
    def test_ands_imm32(self):
        self.assertEqual(self.rf.read('X0'), 0x4344)
        self.assertEqual(self.rf.read('W0'), 0x4344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x81424344')
    @itest('ands w0, w1, #0xffff0000')
    def test_ands_imm2_32(self):
        self.assertEqual(self.rf.read('X0'), 0x81420000)
        self.assertEqual(self.rf.read('W0'), 0x81420000)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x44434241')
    @itest('ands w0, w1, #1')
    def test_ands_imm3_32(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0')
    @itest('ands w0, w1, #1')
    def test_ands_imm4_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x40000000)

    # 64-bit.

    @itest_setregs('X1=0x8142434445464748')
    @itest('ands x0, x1, #0xffff0000ffff0000')
    def test_ands_imm64(self):
        self.assertEqual(self.rf.read('X0'), 0x8142000045460000)
        self.assertEqual(self.rf.read('W0'), 0x45460000)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0x4142434445464748')
    @itest('ands x0, x1, #0x0000ffff0000ffff')
    def test_ands_imm2_64(self):
        self.assertEqual(self.rf.read('X0'), 0x434400004748)
        self.assertEqual(self.rf.read('W0'), 0x4748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4847464544434241')
    @itest('ands x0, x1, #1')
    def test_ands_imm3_64(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0')
    @itest('ands x0, x1, #1')
    def test_ands_imm4_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x40000000)

    # ANDS (shifted register).

    # 32-bit.

    @itest_setregs('W1=0x4142ffff', 'W2=0xffff4344')
    @itest('ands w0, w1, w2')
    def test_ands_sft_reg32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0xffffffff', 'W2=0')
    @itest('ands w0, w1, w2')
    def test_ands_sft_reg_zero32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x40000000)

    @itest_setregs('W1=0x4142ffff', 'W2=0xffff4344')
    @itest('ands w0, w1, w2, lsl #0')
    def test_ands_sft_reg_lsl_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0xffffffff', 'W2=0x80000001')
    @itest('ands w0, w1, w2, lsl #31')
    def test_ands_sft_reg_lsl_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x80000000)
        self.assertEqual(self.rf.read('W0'), 0x80000000)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0xffffffff', 'W2=0x81424344')
    @itest('ands w0, w1, w2, lsl #4')
    def test_ands_sft_reg_lsl32(self):
        self.assertEqual(self.rf.read('X0'), 0x14243440)
        self.assertEqual(self.rf.read('W0'), 0x14243440)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x4142ffff', 'W2=0xffff4344')
    @itest('ands w0, w1, w2, lsr #0')
    def test_ands_sft_reg_lsr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0xffffffff', 'W2=0x80000001')
    @itest('ands w0, w1, w2, lsr #31')
    def test_ands_sft_reg_lsr_max32(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0xffffffff', 'W2=0x81424344')
    @itest('ands w0, w1, w2, lsr #4')
    def test_ands_sft_reg_lsr32(self):
        self.assertEqual(self.rf.read('X0'), 0x8142434)
        self.assertEqual(self.rf.read('W0'), 0x8142434)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x4142ffff', 'W2=0xffff4344')
    @itest('ands w0, w1, w2, asr #0')
    def test_ands_sft_reg_asr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0xffffffff', 'W2=0x80000001')
    @itest('ands w0, w1, w2, asr #31')
    def test_ands_sft_reg_asr_max32(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0xffffffff', 'W2=0x81424344')
    @itest('ands w0, w1, w2, asr #4')
    def test_ands_sft_reg_asr32(self):
        self.assertEqual(self.rf.read('X0'), 0xf8142434)
        self.assertEqual(self.rf.read('W0'), 0xf8142434)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x4142ffff', 'W2=0xffff4344')
    @itest('ands w0, w1, w2, ror #0')
    def test_ands_sft_reg_ror_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0xffffffff', 'W2=0x80000001')
    @itest('ands w0, w1, w2, ror #31')
    def test_ands_sft_reg_ror_max32(self):
        self.assertEqual(self.rf.read('X0'), 3)
        self.assertEqual(self.rf.read('W0'), 3)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0xffffffff', 'W2=0x81424344')
    @itest('ands w0, w1, w2, ror #4')
    def test_ands_sft_reg_ror32(self):
        self.assertEqual(self.rf.read('X0'), 0x48142434)
        self.assertEqual(self.rf.read('W0'), 0x48142434)
        self.assertEqual(self.rf.read('NZCV'), 0)

    # 64-bit.

    @itest_setregs('X1=0x41424344ffffffff', 'X2=0xffffffff45464748')
    @itest('ands x0, x1, x2')
    def test_ands_sft_reg64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0')
    @itest('ands x0, x1, x2')
    def test_ands_sft_reg_zero64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x40000000)

    @itest_setregs('X1=0x41424344ffffffff', 'X2=0xffffffff45464748')
    @itest('ands x0, x1, x2, lsl #0')
    def test_ands_sft_reg_lsl_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8000000000000001')
    @itest('ands x0, x1, x2, lsl #63')
    def test_ands_sft_reg_lsl_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x8000000000000000)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8142434445464748')
    @itest('ands x0, x1, x2, lsl #4')
    def test_ands_sft_reg_lsl64(self):
        self.assertEqual(self.rf.read('X0'), 0x1424344454647480)
        self.assertEqual(self.rf.read('W0'), 0x54647480)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x41424344ffffffff', 'X2=0xffffffff45464748')
    @itest('ands x0, x1, x2, lsr #0')
    def test_ands_sft_reg_lsr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8000000000000001')
    @itest('ands x0, x1, x2, lsr #63')
    def test_ands_sft_reg_lsr_max64(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8142434445464748')
    @itest('ands x0, x1, x2, lsr #4')
    def test_ands_sft_reg_lsr64(self):
        self.assertEqual(self.rf.read('X0'), 0x814243444546474)
        self.assertEqual(self.rf.read('W0'), 0x44546474)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x41424344ffffffff', 'X2=0xffffffff45464748')
    @itest('ands x0, x1, x2, asr #0')
    def test_ands_sft_reg_asr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8000000000000001')
    @itest('ands x0, x1, x2, asr #63')
    def test_ands_sft_reg_asr_max64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8142434445464748')
    @itest('ands x0, x1, x2, asr #4')
    def test_ands_sft_reg_asr64(self):
        self.assertEqual(self.rf.read('X0'), 0xf814243444546474)
        self.assertEqual(self.rf.read('W0'), 0x44546474)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0x41424344ffffffff', 'X2=0xffffffff45464748')
    @itest('ands x0, x1, x2, ror #0')
    def test_ands_sft_reg_ror_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8000000000000001')
    @itest('ands x0, x1, x2, ror #63')
    def test_ands_sft_reg_ror_max64(self):
        self.assertEqual(self.rf.read('X0'), 3)
        self.assertEqual(self.rf.read('W0'), 3)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8142434445464748')
    @itest('ands x0, x1, x2, ror #4')
    def test_ands_sft_reg_ror64(self):
        self.assertEqual(self.rf.read('X0'), 0x8814243444546474)
        self.assertEqual(self.rf.read('W0'), 0x44546474)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    # ASR (immediate).

    # 32-bit.

    @itest_setregs('W1=0x81424344')
    @itest('asr w0, w1, #0')
    def test_asr_imm_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x81424344)
        self.assertEqual(self.rf.read('W0'), 0x81424344)

    @itest_setregs('W1=0x81424344')
    @itest('asr w0, w1, #31')
    def test_asr_imm_max32(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    @itest_setregs('W1=0x81424344')
    @itest('asr w0, w1, #4')
    def test_asr_imm32(self):
        self.assertEqual(self.rf.read('X0'), 0xf8142434)
        self.assertEqual(self.rf.read('W0'), 0xf8142434)

    # 64-bit.

    @itest_setregs('X1=0x8142434445464748')
    @itest('asr x0, x1, #0')
    def test_asr_imm_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x8142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0x8142434445464748')
    @itest('asr x0, x1, #63')
    def test_asr_imm_max64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    @itest_setregs('X1=0x8142434445464748')
    @itest('asr x0, x1, #4')
    def test_asr_imm64(self):
        self.assertEqual(self.rf.read('X0'), 0xf814243444546474)
        self.assertEqual(self.rf.read('W0'), 0x44546474)

    # ASR (register).

    # 32-bit.

    @itest_setregs('W1=0x81424344', 'W2=0')
    @itest('asr w0, w1, w2')
    def test_asr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x81424344)
        self.assertEqual(self.rf.read('W0'), 0x81424344)

    @itest_setregs('W1=0x81424344', 'W2=0xffffffff')
    @itest('asr w0, w1, w2')
    def test_asr_max32(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    @itest_setregs('W1=0x81424344', 'W2=4')
    @itest('asr w0, w1, w2')
    def test_asr32(self):
        self.assertEqual(self.rf.read('X0'), 0xf8142434)
        self.assertEqual(self.rf.read('W0'), 0xf8142434)

    # 64-bit.

    @itest_setregs('X1=0x8142434445464748', 'X2=0')
    @itest('asr x0, x1, x2')
    def test_asr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x8142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0x8142434445464748', 'X2=0xffffffffffffffff')
    @itest('asr x0, x1, x2')
    def test_asr_max64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    @itest_setregs('X1=0x8142434445464748', 'X2=4')
    @itest('asr x0, x1, x2')
    def test_asr64(self):
        self.assertEqual(self.rf.read('X0'), 0xf814243444546474)
        self.assertEqual(self.rf.read('W0'), 0x44546474)

    # ASRV.

    # 32-bit.

    @itest_setregs('W1=0x81424344', 'W2=0')
    @itest('asrv w0, w1, w2')
    def test_asrv_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x81424344)
        self.assertEqual(self.rf.read('W0'), 0x81424344)

    @itest_setregs('W1=0x81424344', 'W2=0xffffffff')
    @itest('asrv w0, w1, w2')
    def test_asrv_max32(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    @itest_setregs('W1=0x81424344', 'W2=4')
    @itest('asrv w0, w1, w2')
    def test_asrv32(self):
        self.assertEqual(self.rf.read('X0'), 0xf8142434)
        self.assertEqual(self.rf.read('W0'), 0xf8142434)

    # 64-bit.

    @itest_setregs('X1=0x8142434445464748', 'X2=0')
    @itest('asrv x0, x1, x2')
    def test_asrv_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x8142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0x8142434445464748', 'X2=0xffffffffffffffff')
    @itest('asrv x0, x1, x2')
    def test_asrv_max64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    @itest_setregs('X1=0x8142434445464748', 'X2=4')
    @itest('asrv x0, x1, x2')
    def test_asrv64(self):
        self.assertEqual(self.rf.read('X0'), 0xf814243444546474)
        self.assertEqual(self.rf.read('W0'), 0x44546474)

    # B.cond.

    # XXX: Bundles everything into one testcase.
    def test_b_cond(self):
        for cond in NZCV_COND_MAP:
            cond_true, cond_false = NZCV_COND_MAP[cond]
            asms = [f'b.{cond} .+8', 'mov x1, 42', 'mov x2, 43']

            def b_cond(self, add_pc, x1, x2):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                pc = self.cpu.PC
                # Execute just two instructions, so it doesn't attempt to run
                # beyond valid code.
                self._execute(check_pc=False)
                assertEqual(self.rf.read('PC'), pc + add_pc)
                assertEqual(self.rf.read('LR'), 0)
                assertEqual(self.rf.read('X30'), 0)
                self._execute()
                assertEqual(self.rf.read('X1'), x1)
                assertEqual(self.rf.read('X2'), x2)

            @itest_setregs(f'NZCV={cond_true}')
            @itest_custom(asms, multiple_insts=True)
            def b_cond_true(self):
                b_cond(self, add_pc=8, x1=0, x2=43)

            @itest_setregs(f'NZCV={cond_false}')
            @itest_custom(asms, multiple_insts=True)
            def b_cond_false(self):
                b_cond(self, add_pc=4, x1=42, x2=0)

            if cond_true:
                self.setUp()
                b_cond_true(self)

            if cond_false:
                self.setUp()
                b_cond_false(self)

    # B.

    # Jump over the second instruction.
    @itest_custom(['b .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_b_pos(self):
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        # Execute just two instructions, so it doesn't attempt to run beyond
        # valid code.
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 8)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0)
        self.assertEqual(self.rf.read('X2'), 43)

    # Jump two instructions back.
    @itest_custom(['mov x1, 42', 'mov x2, 43', 'b .-8'], multiple_insts=True)
    def test_b_neg(self):
        self.cpu.PC += 8  # start at 'b'
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        # Execute just two instructions, so it doesn't loop indefinitely.
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc - 8)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 42)
        self.assertEqual(self.rf.read('X2'), 0)

    # BFC.

    # 32-bit.

    # This is actually bfxil.
    @itest_setregs('W0=0xffffffff')
    @itest('bfc w0, #0, #1')
    def test_bfc_min_min32(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffe)
        self.assertEqual(self.rf.read('W0'), 0xfffffffe)

    # This is actually bfxil.
    @itest_setregs('W0=0xffffffff')
    @itest('bfc w0, #0, #32')
    def test_bfc_min_max32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('W0=0xffffffff')
    @itest('bfc w0, #31, #1')
    def test_bfc_max_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x7fffffff)
        self.assertEqual(self.rf.read('W0'), 0x7fffffff)

    @itest_setregs('W0=0xffffffff')
    @itest('bfc w0, #17, #15')
    def test_bfc32(self):
        self.assertEqual(self.rf.read('X0'), 0x1ffff)
        self.assertEqual(self.rf.read('W0'), 0x1ffff)

    # 64-bit.

    # This is actually bfxil.
    @itest_setregs('X0=0xffffffffffffffff')
    @itest('bfc x0, #0, #1')
    def test_bfc_min_min64(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffffffffffe)
        self.assertEqual(self.rf.read('W0'), 0xfffffffe)

    # This is actually bfxil.
    @itest_setregs('X0=0xffffffffffffffff')
    @itest('bfc x0, #0, #64')
    def test_bfc_min_max64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('X0=0xffffffffffffffff')
    @itest('bfc x0, #63, #1')
    def test_bfc_max_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x7fffffffffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    @itest_setregs('X0=0xffffffffffffffff')
    @itest('bfc x0, #33, #31')
    def test_bfc64(self):
        self.assertEqual(self.rf.read('X0'), 0x1ffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    # BFI.

    # 32-bit.

    # This is actually bfxil.
    @itest_setregs('W0=0xffffffff', 'W1=0x4142434e')
    @itest('bfi w0, w1, #0, #1')
    def test_bfi_min_min32(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffe)
        self.assertEqual(self.rf.read('W0'), 0xfffffffe)

    # This is actually bfxil.
    @itest_setregs('W0=0xffffffff', 'W1=0x41424344')
    @itest('bfi w0, w1, #0, #32')
    def test_bfi_min_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    @itest_setregs('W0=0xffffffff', 'W1=0x4142434e')
    @itest('bfi w0, w1, #31, #1')
    def test_bfi_max_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x7fffffff)
        self.assertEqual(self.rf.read('W0'), 0x7fffffff)

    @itest_setregs('W0=0xffffffff', 'W1=0x41428000')
    @itest('bfi w0, w1, #17, #15')
    def test_bfi32(self):
        self.assertEqual(self.rf.read('X0'), 0x1ffff)
        self.assertEqual(self.rf.read('W0'), 0x1ffff)

    # 64-bit.

    # This is actually bfxil.
    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x414243444546474e')
    @itest('bfi x0, x1, #0, #1')
    def test_bfi_min_min64(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffffffffffe)
        self.assertEqual(self.rf.read('W0'), 0xfffffffe)

    # This is actually bfxil.
    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x4142434445464748')
    @itest('bfi x0, x1, #0, #64')
    def test_bfi_min_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x414243444546474e')
    @itest('bfi x0, x1, #63, #1')
    def test_bfi_max_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x7fffffffffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x4142434480000000')
    @itest('bfi x0, x1, #33, #31')
    def test_bfi64(self):
        self.assertEqual(self.rf.read('X0'), 0x1ffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    # BFM.

    # 32-bit.

    # This is actually bfxil.
    @itest_setregs('W0=0xffffffff', 'W1=0x414243c7')
    @itest('bfm w0, w1, #3, #5')
    def test_bfm_ge32(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffff8)
        self.assertEqual(self.rf.read('W0'), 0xfffffff8)

    # This is actually bfi.
    @itest_setregs('W0=0xffffffff', 'W1=0x41424340')
    @itest('bfm w0, w1, #5, #3')
    def test_bfm_lt32(self):
        self.assertEqual(self.rf.read('X0'), 0x87ffffff)
        self.assertEqual(self.rf.read('W0'), 0x87ffffff)

    # This is actually bfxil.
    @itest_setregs('W0=0xffffffff', 'W1=0x41424344')
    @itest('bfm w0, w1, #0, #31')
    def test_bfm_ge_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    # This is actually bfi.
    @itest_setregs('W0=0xffffffff', 'W1=0x4142434e')
    @itest('bfm w0, w1, #31, #0')
    def test_bfm_lt_max32(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffd)
        self.assertEqual(self.rf.read('W0'), 0xfffffffd)

    # This is actually bfxil.
    @itest_setregs('W0=0xffffffff', 'W1=0x41424346')
    @itest('bfm w0, w1, #0, #0')
    def test_bfm_ge_min32(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffe)
        self.assertEqual(self.rf.read('W0'), 0xfffffffe)

    # This is actually bfi.
    @itest_setregs('W0=0xffffffff', 'W1=0x4142434e')
    @itest('bfm w0, w1, #1, #0')
    def test_bfm_lt_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x7fffffff)
        self.assertEqual(self.rf.read('W0'), 0x7fffffff)

    # 64-bit.

    # This is actually bfxil.
    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x41424344454647c7')
    @itest('bfm x0, x1, #3, #5')
    def test_bfm_ge64(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffffffffff8)
        self.assertEqual(self.rf.read('W0'), 0xfffffff8)

    # This is actually bfi.
    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x4142434445464740')
    @itest('bfm x0, x1, #5, #3')
    def test_bfm_lt64(self):
        self.assertEqual(self.rf.read('X0'), 0x87ffffffffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    # This is actually bfxil.
    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x4142434445464748')
    @itest('bfm x0, x1, #0, #63')
    def test_bfm_ge_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    # This is actually bfi.
    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x414243444546474e')
    @itest('bfm x0, x1, #63, #0')
    def test_bfm_lt_max64(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffffffffffd)
        self.assertEqual(self.rf.read('W0'), 0xfffffffd)

    # This is actually bfxil.
    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x4142434445464746')
    @itest('bfm x0, x1, #0, #0')
    def test_bfm_ge_min64(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffffffffffe)
        self.assertEqual(self.rf.read('W0'), 0xfffffffe)

    # This is actually bfi.
    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x414243444546474e')
    @itest('bfm x0, x1, #1, #0')
    def test_bfm_lt_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x7fffffffffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    # BFXIL.

    # 32-bit.

    @itest_setregs('W0=0xffffffff', 'W1=0x4142434e')
    @itest('bfxil w0, w1, #0, #1')
    def test_bfxil_min_min32(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffe)
        self.assertEqual(self.rf.read('W0'), 0xfffffffe)

    @itest_setregs('W0=0xffffffff', 'W1=0x41424344')
    @itest('bfxil w0, w1, #0, #32')
    def test_bfxil_min_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    @itest_setregs('W0=0xffffffff', 'W1=0x71424344')
    @itest('bfxil w0, w1, #31, #1')
    def test_bfxil_max_min32(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffe)
        self.assertEqual(self.rf.read('W0'), 0xfffffffe)

    @itest_setregs('W0=0xffffffff', 'W1=0x4344')
    @itest('bfxil w0, w1, #16, #16')
    def test_bfxil32(self):
        self.assertEqual(self.rf.read('X0'), 0xffff0000)
        self.assertEqual(self.rf.read('W0'), 0xffff0000)

    # 64-bit.

    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x414243444546474e')
    @itest('bfxil x0, x1, #0, #1')
    def test_bfxil_min_min64(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffffffffffe)
        self.assertEqual(self.rf.read('W0'), 0xfffffffe)

    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x4142434445464748')
    @itest('bfxil x0, x1, #0, #64')
    def test_bfxil_min_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x7142434445464748')
    @itest('bfxil x0, x1, #63, #1')
    def test_bfxil_max_min64(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffffffffffe)
        self.assertEqual(self.rf.read('W0'), 0xfffffffe)

    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x45464748')
    @itest('bfxil x0, x1, #32, #32')
    def test_bfxil64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffff00000000)
        self.assertEqual(self.rf.read('W0'), 0)

    # BIC (shifted register).

    # 32-bit.

    @itest_setregs('W1=0x41424344', 'W2=0xffff0000')
    @itest('bic w0, w1, w2')
    def test_bic32(self):
        self.assertEqual(self.rf.read('X0'), 0x4344)
        self.assertEqual(self.rf.read('W0'), 0x4344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0xffff0000')
    @itest('bic w0, w1, w2, lsl #0')
    def test_bic_lsl_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x4344)
        self.assertEqual(self.rf.read('W0'), 0x4344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0xf1424344', 'W2=1')
    @itest('bic w0, w1, w2, lsl #31')
    def test_bic_lsl_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x71424344)
        self.assertEqual(self.rf.read('W0'), 0x71424344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0xffff000')
    @itest('bic w0, w1, w2, lsl #4')
    def test_bic_lsl32(self):
        self.assertEqual(self.rf.read('X0'), 0x4344)
        self.assertEqual(self.rf.read('W0'), 0x4344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0xffff0000')
    @itest('bic w0, w1, w2, lsr #0')
    def test_bic_lsr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x4344)
        self.assertEqual(self.rf.read('W0'), 0x4344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x4142434f', 'W2=0x80000000')
    @itest('bic w0, w1, w2, lsr #31')
    def test_bic_lsr_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434e)
        self.assertEqual(self.rf.read('W0'), 0x4142434e)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0xffff0000')
    @itest('bic w0, w1, w2, lsr #4')
    def test_bic_lsr32(self):
        self.assertEqual(self.rf.read('X0'), 0x40000344)
        self.assertEqual(self.rf.read('W0'), 0x40000344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0xffff0000')
    @itest('bic w0, w1, w2, asr #0')
    def test_bic_asr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x4344)
        self.assertEqual(self.rf.read('W0'), 0x4344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x80000000')
    @itest('bic w0, w1, w2, asr #31')
    def test_bic_asr_max32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0xf0000000')
    @itest('bic w0, w1, w2, asr #4')
    def test_bic_asr32(self):
        self.assertEqual(self.rf.read('X0'), 0x424344)
        self.assertEqual(self.rf.read('W0'), 0x424344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0xffff0000')
    @itest('bic w0, w1, w2, ror #0')
    def test_bic_ror_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x4344)
        self.assertEqual(self.rf.read('W0'), 0x4344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x4142434f', 'W2=0x80000001')
    @itest('bic w0, w1, w2, ror #31')
    def test_bic_ror_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434c)
        self.assertEqual(self.rf.read('W0'), 0x4142434c)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0xffff000f')
    @itest('bic w0, w1, w2, ror #4')
    def test_bic_ror32(self):
        self.assertEqual(self.rf.read('X0'), 0x344)
        self.assertEqual(self.rf.read('W0'), 0x344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff00000000')
    @itest('bic x0, x1, x2')
    def test_bic64(self):
        self.assertEqual(self.rf.read('X0'), 0x45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff00000000')
    @itest('bic x0, x1, x2, lsl #0')
    def test_bic_lsl_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0xf142434445464748', 'X2=1')
    @itest('bic x0, x1, x2, lsl #63')
    def test_bic_lsl_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x7142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff0000000')
    @itest('bic x0, x1, x2, lsl #4')
    def test_bic_lsl64(self):
        self.assertEqual(self.rf.read('X0'), 0x45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff00000000')
    @itest('bic x0, x1, x2, lsr #0')
    def test_bic_lsr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x414243444546474f', 'X2=0x8000000000000000')
    @itest('bic x0, x1, x2, lsr #63')
    def test_bic_lsr_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x414243444546474e)
        self.assertEqual(self.rf.read('W0'), 0x4546474e)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff00000000')
    @itest('bic x0, x1, x2, lsr #4')
    def test_bic_lsr64(self):
        self.assertEqual(self.rf.read('X0'), 0x4000000005464748)
        self.assertEqual(self.rf.read('W0'), 0x5464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff00000000')
    @itest('bic x0, x1, x2, asr #0')
    def test_bic_asr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8000000000000000')
    @itest('bic x0, x1, x2, asr #63')
    def test_bic_asr_max64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xf000000000000000')
    @itest('bic x0, x1, x2, asr #4')
    def test_bic_asr64(self):
        self.assertEqual(self.rf.read('X0'), 0x42434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff00000000')
    @itest('bic x0, x1, x2, ror #0')
    def test_bic_ror_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x414243444546474f', 'X2=0x8000000000000001')
    @itest('bic x0, x1, x2, ror #63')
    def test_bic_ror_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x414243444546474c)
        self.assertEqual(self.rf.read('W0'), 0x4546474c)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff0000000f')
    @itest('bic x0, x1, x2, ror #4')
    def test_bic_ror64(self):
        self.assertEqual(self.rf.read('X0'), 0x5464748)
        self.assertEqual(self.rf.read('W0'), 0x5464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    # BICS (shifted register).

    # 32-bit.

    @itest_setregs('W1=0x41424344', 'W2=0xffff0000')
    @itest('bics w0, w1, w2')
    def test_bics32(self):
        self.assertEqual(self.rf.read('X0'), 0x4344)
        self.assertEqual(self.rf.read('W0'), 0x4344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0xffff0000')
    @itest('bics w0, w1, w2, lsl #0')
    def test_bics_lsl_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x4344)
        self.assertEqual(self.rf.read('W0'), 0x4344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0xf1424344', 'W2=1')
    @itest('bics w0, w1, w2, lsl #31')
    def test_bics_lsl_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x71424344)
        self.assertEqual(self.rf.read('W0'), 0x71424344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0xffff000')
    @itest('bics w0, w1, w2, lsl #4')
    def test_bics_lsl32(self):
        self.assertEqual(self.rf.read('X0'), 0x4344)
        self.assertEqual(self.rf.read('W0'), 0x4344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0xffff0000')
    @itest('bics w0, w1, w2, lsr #0')
    def test_bics_lsr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x4344)
        self.assertEqual(self.rf.read('W0'), 0x4344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x9142434f', 'W2=0x80000000')
    @itest('bics w0, w1, w2, lsr #31')
    def test_bics_lsr_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x9142434e)
        self.assertEqual(self.rf.read('W0'), 0x9142434e)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x91424344', 'W2=0xffff0000')
    @itest('bics w0, w1, w2, lsr #4')
    def test_bics_lsr32(self):
        self.assertEqual(self.rf.read('X0'), 0x90000344)
        self.assertEqual(self.rf.read('W0'), 0x90000344)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0xffff0000')
    @itest('bics w0, w1, w2, asr #0')
    def test_bics_asr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x4344)
        self.assertEqual(self.rf.read('W0'), 0x4344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x80000000')
    @itest('bics w0, w1, w2, asr #31')
    def test_bics_asr_max32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x40000000)

    @itest_setregs('W1=0x41424344', 'W2=0xf0000000')
    @itest('bics w0, w1, w2, asr #4')
    def test_bics_asr32(self):
        self.assertEqual(self.rf.read('X0'), 0x424344)
        self.assertEqual(self.rf.read('W0'), 0x424344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0xffff0000')
    @itest('bics w0, w1, w2, ror #0')
    def test_bics_ror_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x4344)
        self.assertEqual(self.rf.read('W0'), 0x4344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x9142434f', 'W2=0x80000001')
    @itest('bics w0, w1, w2, ror #31')
    def test_bics_ror_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x9142434c)
        self.assertEqual(self.rf.read('W0'), 0x9142434c)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0xffff000f')
    @itest('bics w0, w1, w2, ror #4')
    def test_bics_ror32(self):
        self.assertEqual(self.rf.read('X0'), 0x344)
        self.assertEqual(self.rf.read('W0'), 0x344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff00000000')
    @itest('bics x0, x1, x2')
    def test_bics64(self):
        self.assertEqual(self.rf.read('X0'), 0x45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff00000000')
    @itest('bics x0, x1, x2, lsl #0')
    def test_bics_lsl_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0xf142434445464748', 'X2=1')
    @itest('bics x0, x1, x2, lsl #63')
    def test_bics_lsl_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x7142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff0000000')
    @itest('bics x0, x1, x2, lsl #4')
    def test_bics_lsl64(self):
        self.assertEqual(self.rf.read('X0'), 0x45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff00000000')
    @itest('bics x0, x1, x2, lsr #0')
    def test_bics_lsr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x914243444546474f', 'X2=0x8000000000000000')
    @itest('bics x0, x1, x2, lsr #63')
    def test_bics_lsr_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x914243444546474e)
        self.assertEqual(self.rf.read('W0'), 0x4546474e)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0x9142434445464748', 'X2=0xffffffff00000000')
    @itest('bics x0, x1, x2, lsr #4')
    def test_bics_lsr64(self):
        self.assertEqual(self.rf.read('X0'), 0x9000000005464748)
        self.assertEqual(self.rf.read('W0'), 0x5464748)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff00000000')
    @itest('bics x0, x1, x2, asr #0')
    def test_bics_asr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8000000000000000')
    @itest('bics x0, x1, x2, asr #63')
    def test_bics_asr_max64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x40000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xf000000000000000')
    @itest('bics x0, x1, x2, asr #4')
    def test_bics_asr64(self):
        self.assertEqual(self.rf.read('X0'), 0x42434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff00000000')
    @itest('bics x0, x1, x2, ror #0')
    def test_bics_ror_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x914243444546474f', 'X2=0x8000000000000001')
    @itest('bics x0, x1, x2, ror #63')
    def test_bics_ror_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x914243444546474c)
        self.assertEqual(self.rf.read('W0'), 0x4546474c)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff0000000f')
    @itest('bics x0, x1, x2, ror #4')
    def test_bics_ror64(self):
        self.assertEqual(self.rf.read('X0'), 0x5464748)
        self.assertEqual(self.rf.read('W0'), 0x5464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    # BL.

    # Jump over the second instruction.
    @itest_custom(['bl .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_bl_pos(self):
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        # Execute just two instructions, so it doesn't attempt to run beyond
        # valid code.
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 8)
        self.assertEqual(self.rf.read('LR'), pc + 4)
        self.assertEqual(self.rf.read('X30'), pc + 4)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0)
        self.assertEqual(self.rf.read('X2'), 43)

    # Jump two instructions back.
    @itest_custom(['mov x1, 42', 'mov x2, 43', 'bl .-8'], multiple_insts=True)
    def test_bl_neg(self):
        self.cpu.PC += 8  # start at 'bl'
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        # Execute just two instructions, so it doesn't loop indefinitely.
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc - 8)
        self.assertEqual(self.rf.read('LR'), pc + 4)
        self.assertEqual(self.rf.read('X30'), pc + 4)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 42)
        self.assertEqual(self.rf.read('X2'), 0)

    # BLR.

    # Jump over the second instruction.
    @itest_custom(['blr x0', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_blr_pos(self):
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        self.cpu.X0 = pc + 8
        # Execute just two instructions, so it doesn't attempt to run beyond
        # valid code.
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 8)
        self.assertEqual(self.rf.read('LR'), pc + 4)
        self.assertEqual(self.rf.read('X30'), pc + 4)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0)
        self.assertEqual(self.rf.read('X2'), 43)

    # Jump two instructions back.
    @itest_custom(['mov x1, 42', 'mov x2, 43', 'blr x0'], multiple_insts=True)
    def test_blr_neg(self):
        self.cpu.PC += 8  # start at 'blr'
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        self.cpu.X0 = pc - 8
        # Execute just two instructions, so it doesn't loop indefinitely.
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc - 8)
        self.assertEqual(self.rf.read('LR'), pc + 4)
        self.assertEqual(self.rf.read('X30'), pc + 4)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 42)
        self.assertEqual(self.rf.read('X2'), 0)

    # BR.

    # Jump over the second instruction.
    @itest_custom(['br x0', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_br_pos(self):
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        self.cpu.X0 = pc + 8
        # Execute just two instructions, so it doesn't attempt to run beyond
        # valid code.
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 8)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0)
        self.assertEqual(self.rf.read('X2'), 43)

    # Jump two instructions back.
    @itest_custom(['mov x1, 42', 'mov x2, 43', 'br x0'], multiple_insts=True)
    def test_br_neg(self):
        self.cpu.PC += 8  # start at 'br'
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        self.cpu.X0 = pc - 8
        # Execute just two instructions, so it doesn't loop indefinitely.
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc - 8)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 42)
        self.assertEqual(self.rf.read('X2'), 0)

    # CBNZ.

    # 32-bit.

    # Execute sequentially.
    @itest_custom(['cbnz w0, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_cbnz_pos_zero32(self):
        self._setreg('W0', 0)
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 4)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 42)
        self.assertEqual(self.rf.read('X2'), 0)

    # Jump over the second instruction.
    @itest_custom(['cbnz w0, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_cbnz_pos_non_zero32(self):
        self._setreg('W0', 1)
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 8)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0)
        self.assertEqual(self.rf.read('X2'), 43)

    # Execute sequentially.
    @itest_custom(['mov x1, 42', 'cbnz w0, .-4', 'mov x2, 43'], multiple_insts=True)
    def test_cbnz_neg_zero32(self):
        self._setreg('W0', 0)
        self.cpu.PC += 4
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 4)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0)
        self.assertEqual(self.rf.read('X2'), 43)

    # Jump one instruction back.
    @itest_custom(['mov x1, 42', 'cbnz w0, .-4', 'mov x2, 43'], multiple_insts=True)
    def test_cbnz_neg_non_zero32(self):
        self._setreg('W0', 1)
        self.cpu.PC += 4
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc - 4)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 42)
        self.assertEqual(self.rf.read('X2'), 0)

    # 64-bit.

    # Execute sequentially.
    @itest_custom(['cbnz x0, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_cbnz_pos_zero64(self):
        self._setreg('X0', 0)
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 4)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 42)
        self.assertEqual(self.rf.read('X2'), 0)

    # Jump over the second instruction.
    @itest_custom(['cbnz x0, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_cbnz_pos_non_zero64(self):
        self._setreg('X0', 1)
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 8)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0)
        self.assertEqual(self.rf.read('X2'), 43)

    # Execute sequentially.
    @itest_custom(['mov x1, 42', 'cbnz x0, .-4', 'mov x2, 43'], multiple_insts=True)
    def test_cbnz_neg_zero64(self):
        self._setreg('X0', 0)
        self.cpu.PC += 4
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 4)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0)
        self.assertEqual(self.rf.read('X2'), 43)

    # Jump one instruction back.
    @itest_custom(['mov x1, 42', 'cbnz x0, .-4', 'mov x2, 43'], multiple_insts=True)
    def test_cbnz_neg_non_zero64(self):
        self._setreg('X0', 1)
        self.cpu.PC += 4
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc - 4)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 42)
        self.assertEqual(self.rf.read('X2'), 0)

    # CBZ.

    # 32-bit.

    # Jump over the second instruction.
    @itest_custom(['cbz w0, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_cbz_pos_zero32(self):
        self._setreg('W0', 0)
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 8)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0)
        self.assertEqual(self.rf.read('X2'), 43)

    # Execute sequentially.
    @itest_custom(['cbz w0, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_cbz_pos_non_zero32(self):
        self._setreg('W0', 1)
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 4)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 42)
        self.assertEqual(self.rf.read('X2'), 0)

    # Jump one instruction back.
    @itest_custom(['mov x1, 42', 'cbz w0, .-4', 'mov x2, 43'], multiple_insts=True)
    def test_cbz_neg_zero32(self):
        self._setreg('W0', 0)
        self.cpu.PC += 4
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc - 4)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 42)
        self.assertEqual(self.rf.read('X2'), 0)

    # Execute sequentially.
    @itest_custom(['mov x1, 42', 'cbz w0, .-4', 'mov x2, 43'], multiple_insts=True)
    def test_cbz_neg_non_zero32(self):
        self._setreg('W0', 1)
        self.cpu.PC += 4
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 4)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0)
        self.assertEqual(self.rf.read('X2'), 43)

    # 64-bit.

    # Jump over the second instruction.
    @itest_custom(['cbz x0, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_cbz_pos_zero64(self):
        self._setreg('X0', 0)
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 8)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0)
        self.assertEqual(self.rf.read('X2'), 43)

    # Execute sequentially.
    @itest_custom(['cbz x0, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_cbz_pos_non_zero64(self):
        self._setreg('X0', 1)
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 4)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 42)
        self.assertEqual(self.rf.read('X2'), 0)

    # Jump one instruction back.
    @itest_custom(['mov x1, 42', 'cbz x0, .-4', 'mov x2, 43'], multiple_insts=True)
    def test_cbz_neg_zero64(self):
        self._setreg('X0', 0)
        self.cpu.PC += 4
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc - 4)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 42)
        self.assertEqual(self.rf.read('X2'), 0)

    # Execute sequentially.
    @itest_custom(['mov x1, 42', 'cbz x0, .-4', 'mov x2, 43'], multiple_insts=True)
    def test_cbz_neg_non_zero64(self):
        self._setreg('X0', 1)
        self.cpu.PC += 4
        self._setreg('PC', self.cpu.PC)
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 4)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0)
        self.assertEqual(self.rf.read('X2'), 43)

    # CCMP (immediate).

    # XXX: Bundles everything into one testcase.
    def test_ccmp_imm(self):
        for cond in NZCV_COND_MAP:
            cond_true, cond_false = NZCV_COND_MAP[cond]

            # 32-bit.

            @itest_setregs(f'NZCV={cond_true}', 'W0=0')
            @itest(f'ccmp w0, #0, #15, {cond}')
            def ccmp_imm_true_zc32(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('NZCV'), 0x60000000)

            @itest_setregs(f'NZCV={cond_true}', 'W0=0x8fffffff')
            @itest(f'ccmp w0, #31, #15, {cond}')
            def ccmp_imm_true_nc32(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('NZCV'), 0xa0000000)

            @itest_setregs(f'NZCV={cond_false}', 'W0=0xffffffff')
            @itest(f'ccmp w0, #0, #15, {cond}')
            def ccmp_imm_false32(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('NZCV'), 0xf0000000)

            # 64-bit.

            @itest_setregs(f'NZCV={cond_true}', 'X0=0')
            @itest(f'ccmp x0, #0, #15, {cond}')
            def ccmp_imm_true_zc64(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('NZCV'), 0x60000000)

            @itest_setregs(f'NZCV={cond_true}', 'X0=0x8fffffffffffffff')
            @itest(f'ccmp x0, #31, #15, {cond}')
            def ccmp_imm_true_nc64(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('NZCV'), 0xa0000000)

            @itest_setregs(f'NZCV={cond_false}', 'X0=0xffffffffffffffff')
            @itest(f'ccmp x0, #0, #15, {cond}')
            def ccmp_imm_false64(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('NZCV'), 0xf0000000)

            if cond_true:
                self.setUp()
                ccmp_imm_true_zc32(self)

                self.setUp()
                ccmp_imm_true_nc32(self)

                self.setUp()
                ccmp_imm_true_zc64(self)

                self.setUp()
                ccmp_imm_true_nc64(self)

            if cond_false:
                self.setUp()
                ccmp_imm_false32(self)

                self.setUp()
                ccmp_imm_false64(self)

    # CCMP (register).

    # XXX: Bundles everything into one testcase.
    def test_ccmp_reg(self):
        for cond in NZCV_COND_MAP:
            cond_true, cond_false = NZCV_COND_MAP[cond]

            # 32-bit.

            @itest_setregs(f'NZCV={cond_true}', 'W0=0xffffffff', 'W1=0xffffffff')
            @itest(f'ccmp w0, w1, #15, {cond}')
            def ccmp_reg_true_zc32(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('NZCV'), 0x60000000)

            @itest_setregs(f'NZCV={cond_true}', 'W0=0x7fffffff', 'W1=0xffffffff')
            @itest(f'ccmp w0, w1, #15, {cond}')
            def ccmp_reg_true_nv32(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('NZCV'), 0x90000000)

            @itest_setregs(f'NZCV={cond_false}', 'W0=0xffffffff', 'W1=0xffffffff')
            @itest(f'ccmp w0, w1, #15, {cond}')
            def ccmp_reg_false32(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('NZCV'), 0xf0000000)

            # 64-bit.

            @itest_setregs(
                f'NZCV={cond_true}',
                'X0=0xffffffffffffffff',
                'X1=0xffffffffffffffff'
            )
            @itest(f'ccmp x0, x1, #15, {cond}')
            def ccmp_reg_true_zc64(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('NZCV'), 0x60000000)

            @itest_setregs(
                f'NZCV={cond_true}',
                'X0=0x7fffffffffffffff',
                'X1=0xffffffffffffffff'
            )
            @itest(f'ccmp x0, x1, #15, {cond}')
            def ccmp_reg_true_nv64(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('NZCV'), 0x90000000)

            @itest_setregs(
                f'NZCV={cond_false}',
                'X0=0xffffffffffffffff',
                'X1=0xffffffffffffffff'
            )
            @itest(f'ccmp x0, x1, #15, {cond}')
            def ccmp_reg_false64(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('NZCV'), 0xf0000000)

            if cond_true:
                self.setUp()
                ccmp_reg_true_zc32(self)

                self.setUp()
                ccmp_reg_true_nv32(self)

                self.setUp()
                ccmp_reg_true_zc64(self)

                self.setUp()
                ccmp_reg_true_nv64(self)

            if cond_false:
                self.setUp()
                ccmp_reg_false32(self)

                self.setUp()
                ccmp_reg_false64(self)

    # CINC.

    # XXX: Bundles everything into one testcase.
    def test_cinc(self):
        for cond in NZCV_COND_MAP:
            if cond in ['al', 'nv']:
                continue
            cond_true, cond_false = NZCV_COND_MAP[cond]

            # 32-bit.

            @itest_setregs(f'NZCV={cond_true}', 'W1=0x41424344')
            @itest(f'cinc w0, w1, {cond}')
            def cinc_true32(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0x41424345)
                assertEqual(self.rf.read('W0'), 0x41424345)

            @itest_setregs(f'NZCV={cond_true}', 'W1=0xffffffff')
            @itest(f'cinc w0, w1, {cond}')
            def cinc_true_of32(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0)
                assertEqual(self.rf.read('W0'), 0)

            @itest_setregs(f'NZCV={cond_false}', 'W1=0x41424344')
            @itest(f'cinc w0, w1, {cond}')
            def cinc_false32(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0x41424344)
                assertEqual(self.rf.read('W0'), 0x41424344)

            # 64-bit.

            @itest_setregs(f'NZCV={cond_true}', 'X1=0x4142434445464748')
            @itest(f'cinc x0, x1, {cond}')
            def cinc_true64(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0x4142434445464749)
                assertEqual(self.rf.read('W0'), 0x45464749)

            @itest_setregs(f'NZCV={cond_true}', 'X1=0xffffffffffffffff')
            @itest(f'cinc x0, x1, {cond}')
            def cinc_true_of64(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0)
                assertEqual(self.rf.read('W0'), 0)

            @itest_setregs(f'NZCV={cond_false}', 'X1=0x4142434445464748')
            @itest(f'cinc x0, x1, {cond}')
            def cinc_false64(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0x4142434445464748)
                assertEqual(self.rf.read('W0'), 0x45464748)

            if cond_true:
                self.setUp()
                cinc_true32(self)

                self.setUp()
                cinc_true64(self)

                self.setUp()
                cinc_true_of32(self)

                self.setUp()
                cinc_true_of64(self)

            if cond_false:
                self.setUp()
                cinc_false32(self)

                self.setUp()
                cinc_false64(self)

    # CINV.

    # XXX: Bundles everything into one testcase.
    def test_cinv(self):
        for cond in NZCV_COND_MAP:
            if cond in ['al', 'nv']:
                continue
            cond_true, cond_false = NZCV_COND_MAP[cond]

            # 32-bit.

            @itest_setregs(f'NZCV={cond_true}', 'W1=0x41424344')
            @itest(f'cinv w0, w1, {cond}')
            def cinv_true32(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0xbebdbcbb)
                assertEqual(self.rf.read('W0'), 0xbebdbcbb)

            @itest_setregs(f'NZCV={cond_false}', 'W1=0x41424344')
            @itest(f'cinv w0, w1, {cond}')
            def cinv_false32(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0x41424344)
                assertEqual(self.rf.read('W0'), 0x41424344)

            # 64-bit.

            @itest_setregs(f'NZCV={cond_true}', 'X1=0x4142434445464748')
            @itest(f'cinv x0, x1, {cond}')
            def cinv_true64(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0xbebdbcbbbab9b8b7)
                assertEqual(self.rf.read('W0'), 0xbab9b8b7)

            @itest_setregs(f'NZCV={cond_false}', 'X1=0x4142434445464748')
            @itest(f'cinv x0, x1, {cond}')
            def cinv_false64(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0x4142434445464748)
                assertEqual(self.rf.read('W0'), 0x45464748)

            if cond_true:
                self.setUp()
                cinv_true32(self)

                self.setUp()
                cinv_true64(self)

            if cond_false:
                self.setUp()
                cinv_false32(self)

                self.setUp()
                cinv_false64(self)

    # CLZ.

    # 32-bit.

    @itest_setregs('W1=0')
    @itest('clz w0, w1')
    def test_clz_min32(self):
        self.assertEqual(self.rf.read('X0'), 32)
        self.assertEqual(self.rf.read('W0'), 32)

    @itest_setregs('W1=0xffffffff')
    @itest('clz w0, w1')
    def test_clz_max32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('W1=0x70f010')
    @itest('clz w0, w1')
    def test_clz32(self):
        self.assertEqual(self.rf.read('X0'), 9)
        self.assertEqual(self.rf.read('W0'), 9)

    # 64-bit.

    @itest_setregs('X1=0')
    @itest('clz x0, x1')
    def test_clz_min64(self):
        self.assertEqual(self.rf.read('X0'), 64)
        self.assertEqual(self.rf.read('W0'), 64)

    @itest_setregs('X1=0xffffffffffffffff')
    @itest('clz x0, x1')
    def test_clz_max64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('X1=0x70f0100000')
    @itest('clz x0, x1')
    def test_clz64(self):
        self.assertEqual(self.rf.read('X0'), 25)
        self.assertEqual(self.rf.read('W0'), 25)

    # CMEQ (register, scalar).

    # XXX: Uses 'reset'.

    @itest_setregs(
        'V1=0x81828384858687889192939495969798',
        'V2=0x81828384858687889192939495969798'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'cmeq d0, d1, d2'],
        multiple_insts=True
    )
    def test_cmeq_reg_scalar_eq(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('Q0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('D0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('S0'), 0xffffffff)
        self.assertEqual(self.rf.read('H0'), 0xffff)
        self.assertEqual(self.rf.read('B0'), 0xff)

    @itest_setregs(
        'V1=0x41424344454647485152535455565758',
        'V2=0x61626364656667687172737475767778'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'cmeq d0, d1, d2'],
        multiple_insts=True
    )
    def test_cmeq_reg_scalar_neq(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0)
        self.assertEqual(self.rf.read('Q0'), 0)
        self.assertEqual(self.rf.read('D0'), 0)
        self.assertEqual(self.rf.read('S0'), 0)
        self.assertEqual(self.rf.read('H0'), 0)
        self.assertEqual(self.rf.read('B0'), 0)

    # CMEQ (register, vector).

    # XXX: Uses 'reset'.

    # 8b.

    @itest_setregs(
        'V1=0x81428344854687489152935495569758',
        'V2=0x81628364856687689172937495769778'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'cmeq v0.8b, v1.8b, v2.8b'],
        multiple_insts=True
    )
    def test_cmeq_reg_vector_8b(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xff00ff00ff00ff00)
        self.assertEqual(self.rf.read('Q0'), 0xff00ff00ff00ff00)
        self.assertEqual(self.rf.read('D0'), 0xff00ff00ff00ff00)
        self.assertEqual(self.rf.read('S0'), 0xff00ff00)
        self.assertEqual(self.rf.read('H0'), 0xff00)
        self.assertEqual(self.rf.read('B0'), 0)

    # 16b.

    @itest_setregs(
        'V1=0x81428344854687489152935495569758',
        'V2=0x81628364856687689172937495769778'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'cmeq v0.16b, v1.16b, v2.16b'],
        multiple_insts=True
    )
    def test_cmeq_reg_vector_16b(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xff00ff00ff00ff00ff00ff00ff00ff00)
        self.assertEqual(self.rf.read('Q0'), 0xff00ff00ff00ff00ff00ff00ff00ff00)
        self.assertEqual(self.rf.read('D0'), 0xff00ff00ff00ff00)
        self.assertEqual(self.rf.read('S0'), 0xff00ff00)
        self.assertEqual(self.rf.read('H0'), 0xff00)
        self.assertEqual(self.rf.read('B0'), 0)

    # 4h.

    @itest_setregs(
        'V1=0x81828344858687489192935495969758',
        'V2=0x81828364858687689192937495969778'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'cmeq v0.4h, v1.4h, v2.4h'],
        multiple_insts=True
    )
    def test_cmeq_reg_vector_4h(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xffff0000ffff0000)
        self.assertEqual(self.rf.read('Q0'), 0xffff0000ffff0000)
        self.assertEqual(self.rf.read('D0'), 0xffff0000ffff0000)
        self.assertEqual(self.rf.read('S0'), 0xffff0000)
        self.assertEqual(self.rf.read('H0'), 0)
        self.assertEqual(self.rf.read('B0'), 0)

    # 8h.

    @itest_setregs(
        'V1=0x81828344858687489192935495969758',
        'V2=0x81828364858687689192937495969778'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'cmeq v0.8h, v1.8h, v2.8h'],
        multiple_insts=True
    )
    def test_cmeq_reg_vector_8h(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xffff0000ffff0000ffff0000ffff0000)
        self.assertEqual(self.rf.read('Q0'), 0xffff0000ffff0000ffff0000ffff0000)
        self.assertEqual(self.rf.read('D0'), 0xffff0000ffff0000)
        self.assertEqual(self.rf.read('S0'), 0xffff0000)
        self.assertEqual(self.rf.read('H0'), 0)
        self.assertEqual(self.rf.read('B0'), 0)

    # 2s.

    @itest_setregs(
        'V1=0x81828384854687489192939495569758',
        'V2=0x81828384856687689192939495769778'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'cmeq v0.2s, v1.2s, v2.2s'],
        multiple_insts=True
    )
    def test_cmeq_reg_vector_2s(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xffffffff00000000)
        self.assertEqual(self.rf.read('Q0'), 0xffffffff00000000)
        self.assertEqual(self.rf.read('D0'), 0xffffffff00000000)
        self.assertEqual(self.rf.read('S0'), 0)
        self.assertEqual(self.rf.read('H0'), 0)
        self.assertEqual(self.rf.read('B0'), 0)

    # 4s.

    @itest_setregs(
        'V1=0x81828384854687489192939495569758',
        'V2=0x81828384856687689192939495769778'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'cmeq v0.4s, v1.4s, v2.4s'],
        multiple_insts=True
    )
    def test_cmeq_reg_vector_4s(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xffffffff00000000ffffffff00000000)
        self.assertEqual(self.rf.read('Q0'), 0xffffffff00000000ffffffff00000000)
        self.assertEqual(self.rf.read('D0'), 0xffffffff00000000)
        self.assertEqual(self.rf.read('S0'), 0)
        self.assertEqual(self.rf.read('H0'), 0)
        self.assertEqual(self.rf.read('B0'), 0)

    # 2d.

    @itest_setregs(
        'V1=0x81828384858687889152935495569758',
        'V2=0x81828384858687889172937495769778'
    )
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'cmeq v0.2d, v1.2d, v2.2d'],
        multiple_insts=True
    )
    def test_cmeq_reg_vector_2d(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xffffffffffffffff0000000000000000)
        self.assertEqual(self.rf.read('Q0'), 0xffffffffffffffff0000000000000000)
        self.assertEqual(self.rf.read('D0'), 0)
        self.assertEqual(self.rf.read('S0'), 0)
        self.assertEqual(self.rf.read('H0'), 0)
        self.assertEqual(self.rf.read('B0'), 0)

    # CMEQ (zero, scalar).

    # XXX: Uses 'reset'.

    @itest_setregs('V1=0x81828384858687880000000000000000')
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'cmeq d0, d1, #0'],
        multiple_insts=True
    )
    def test_cmeq_zero_scalar_eq(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('Q0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('D0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('S0'), 0xffffffff)
        self.assertEqual(self.rf.read('H0'), 0xffff)
        self.assertEqual(self.rf.read('B0'), 0xff)

    @itest_setregs('V1=0x41424344454647485152535455565758')
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'cmeq d0, d1, #0'],
        multiple_insts=True
    )
    def test_cmeq_zero_scalar_neq(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0)
        self.assertEqual(self.rf.read('Q0'), 0)
        self.assertEqual(self.rf.read('D0'), 0)
        self.assertEqual(self.rf.read('S0'), 0)
        self.assertEqual(self.rf.read('H0'), 0)
        self.assertEqual(self.rf.read('B0'), 0)

    # CMEQ (zero, vector).

    # XXX: Uses 'reset'.

    # 8b.

    @itest_setregs('V1=0x00420044004600480052005400560058')
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'cmeq v0.8b, v1.8b, #0'],
        multiple_insts=True
    )
    def test_cmeq_zero_vector_8b(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xff00ff00ff00ff00)
        self.assertEqual(self.rf.read('Q0'), 0xff00ff00ff00ff00)
        self.assertEqual(self.rf.read('D0'), 0xff00ff00ff00ff00)
        self.assertEqual(self.rf.read('S0'), 0xff00ff00)
        self.assertEqual(self.rf.read('H0'), 0xff00)
        self.assertEqual(self.rf.read('B0'), 0)

    # 16b.

    @itest_setregs('V1=0x00420044004600480052005400560058')
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'cmeq v0.16b, v1.16b, #0'],
        multiple_insts=True
    )
    def test_cmeq_zero_vector_16b(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xff00ff00ff00ff00ff00ff00ff00ff00)
        self.assertEqual(self.rf.read('Q0'), 0xff00ff00ff00ff00ff00ff00ff00ff00)
        self.assertEqual(self.rf.read('D0'), 0xff00ff00ff00ff00)
        self.assertEqual(self.rf.read('S0'), 0xff00ff00)
        self.assertEqual(self.rf.read('H0'), 0xff00)
        self.assertEqual(self.rf.read('B0'), 0)

    # 4h.

    @itest_setregs('V1=0x00008344000087480000935400009758')
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'cmeq v0.4h, v1.4h, #0'],
        multiple_insts=True
    )
    def test_cmeq_zero_vector_4h(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xffff0000ffff0000)
        self.assertEqual(self.rf.read('Q0'), 0xffff0000ffff0000)
        self.assertEqual(self.rf.read('D0'), 0xffff0000ffff0000)
        self.assertEqual(self.rf.read('S0'), 0xffff0000)
        self.assertEqual(self.rf.read('H0'), 0)
        self.assertEqual(self.rf.read('B0'), 0)

    # 8h.

    @itest_setregs('V1=0x00008344000087480000935400009758')
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'cmeq v0.8h, v1.8h, #0'],
        multiple_insts=True
    )
    def test_cmeq_zero_vector_8h(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xffff0000ffff0000ffff0000ffff0000)
        self.assertEqual(self.rf.read('Q0'), 0xffff0000ffff0000ffff0000ffff0000)
        self.assertEqual(self.rf.read('D0'), 0xffff0000ffff0000)
        self.assertEqual(self.rf.read('S0'), 0xffff0000)
        self.assertEqual(self.rf.read('H0'), 0)
        self.assertEqual(self.rf.read('B0'), 0)

    # 2s.

    @itest_setregs('V1=0x00000000854687480000000095569758')
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'cmeq v0.2s, v1.2s, #0'],
        multiple_insts=True
    )
    def test_cmeq_zero_vector_2s(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xffffffff00000000)
        self.assertEqual(self.rf.read('Q0'), 0xffffffff00000000)
        self.assertEqual(self.rf.read('D0'), 0xffffffff00000000)
        self.assertEqual(self.rf.read('S0'), 0)
        self.assertEqual(self.rf.read('H0'), 0)
        self.assertEqual(self.rf.read('B0'), 0)

    # 4s.

    @itest_setregs('V1=0x00000000854687480000000095569758')
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'cmeq v0.4s, v1.4s, #0'],
        multiple_insts=True
    )
    def test_cmeq_zero_vector_4s(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xffffffff00000000ffffffff00000000)
        self.assertEqual(self.rf.read('Q0'), 0xffffffff00000000ffffffff00000000)
        self.assertEqual(self.rf.read('D0'), 0xffffffff00000000)
        self.assertEqual(self.rf.read('S0'), 0)
        self.assertEqual(self.rf.read('H0'), 0)
        self.assertEqual(self.rf.read('B0'), 0)

    # 2d.

    @itest_setregs('V1=0x00000000000000009152935495569758')
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'cmeq v0.2d, v1.2d, #0'],
        multiple_insts=True
    )
    def test_cmeq_zero_vector_2d(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0xffffffffffffffff0000000000000000)
        self.assertEqual(self.rf.read('Q0'), 0xffffffffffffffff0000000000000000)
        self.assertEqual(self.rf.read('D0'), 0)
        self.assertEqual(self.rf.read('S0'), 0)
        self.assertEqual(self.rf.read('H0'), 0)
        self.assertEqual(self.rf.read('B0'), 0)

    # CMN (extended register).

    # 32-bit.

    @itest_setregs('W1=0x41424344', 'W2=0x51525384')
    @itest('cmn w1, w2, uxtb')
    def test_cmn_ext_reg_uxtb32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51525384')
    @itest('cmn w1, w2, uxtb #0')
    def test_cmn_ext_reg_uxtb0_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51525384')
    @itest('cmn w1, w2, uxtb #4')
    def test_cmn_ext_reg_uxtb4_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51528354')
    @itest('cmn w1, w2, uxth')
    def test_cmn_ext_reg_uxth32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51528354')
    @itest('cmn w1, w2, uxth #0')
    def test_cmn_ext_reg_uxth0_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51528354')
    @itest('cmn w1, w2, uxth #4')
    def test_cmn_ext_reg_uxth4_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmn w1, w2, uxtw')
    def test_cmn_ext_reg_uxtw32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmn w1, w2, uxtw #0')
    def test_cmn_ext_reg_uxtw0_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmn w1, w2, uxtw #4')
    def test_cmn_ext_reg_uxtw4_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmn w1, w2, uxtx')
    def test_cmn_ext_reg_uxtx32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmn w1, w2, uxtx #0')
    def test_cmn_ext_reg_uxtx0_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmn w1, w2, uxtx #4')
    def test_cmn_ext_reg_uxtx4_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51525384')
    @itest('cmn w1, w2, sxtb')
    def test_cmn_ext_reg_sxtb32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344', 'W2=0x51525384')
    @itest('cmn w1, w2, sxtb #0')
    def test_cmn_ext_reg_sxtb0_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344', 'W2=0x51525384')
    @itest('cmn w1, w2, sxtb #4')
    def test_cmn_ext_reg_sxtb4_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344', 'W2=0x51528354')
    @itest('cmn w1, w2, sxth')
    def test_cmn_ext_reg_sxth32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344', 'W2=0x51528354')
    @itest('cmn w1, w2, sxth #0')
    def test_cmn_ext_reg_sxth0_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344', 'W2=0x51528354')
    @itest('cmn w1, w2, sxth #4')
    def test_cmn_ext_reg_sxth4_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmn w1, w2, sxtw')
    def test_cmn_ext_reg_sxtw32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmn w1, w2, sxtw #0')
    def test_cmn_ext_reg_sxtw0_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmn w1, w2, sxtw #4')
    def test_cmn_ext_reg_sxtw4_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmn w1, w2, sxtx')
    def test_cmn_ext_reg_sxtx32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmn w1, w2, sxtx #0')
    def test_cmn_ext_reg_sxtx0_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmn w1, w2, sxtx #4')
    def test_cmn_ext_reg_sxtx4_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmn w1, w2, lsl #0')
    def test_cmn_ext_reg_lsl0_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmn w1, w2, lsl #4')
    def test_cmn_ext_reg_lsl4_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51525384')
    @itest('cmn x1, w2, uxtb')
    def test_cmn_ext_reg_uxtb64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51525384')
    @itest('cmn x1, w2, uxtb #0')
    def test_cmn_ext_reg_uxtb0_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51525384')
    @itest('cmn x1, w2, uxtb #4')
    def test_cmn_ext_reg_uxtb4_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51528354')
    @itest('cmn x1, w2, uxth')
    def test_cmn_ext_reg_uxth64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51528354')
    @itest('cmn x1, w2, uxth #0')
    def test_cmn_ext_reg_uxth0_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51528354')
    @itest('cmn x1, w2, uxth #4')
    def test_cmn_ext_reg_uxth4_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x81525354')
    @itest('cmn x1, w2, uxtw')
    def test_cmn_ext_reg_uxtw64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x81525354')
    @itest('cmn x1, w2, uxtw #0')
    def test_cmn_ext_reg_uxtw0_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x81525354')
    @itest('cmn x1, w2, uxtw #4')
    def test_cmn_ext_reg_uxtw4_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('cmn x1, x2, uxtx')
    def test_cmn_ext_reg_uxtx64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('cmn x1, x2, uxtx #0')
    def test_cmn_ext_reg_uxtx0_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('cmn x1, x2, uxtx #4')
    def test_cmn_ext_reg_uxtx4_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51525384')
    @itest('cmn x1, w2, sxtb')
    def test_cmn_ext_reg_sxtb64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51525384')
    @itest('cmn x1, w2, sxtb #0')
    def test_cmn_ext_reg_sxtb0_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51525384')
    @itest('cmn x1, w2, sxtb #4')
    def test_cmn_ext_reg_sxtb4_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51528354')
    @itest('cmn x1, w2, sxth')
    def test_cmn_ext_reg_sxth64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51528354')
    @itest('cmn x1, w2, sxth #0')
    def test_cmn_ext_reg_sxth0_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51528354')
    @itest('cmn x1, w2, sxth #4')
    def test_cmn_ext_reg_sxth4_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x81525354')
    @itest('cmn x1, w2, sxtw')
    def test_cmn_ext_reg_sxtw64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x81525354')
    @itest('cmn x1, w2, sxtw #0')
    def test_cmn_ext_reg_sxtw0_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x81525354')
    @itest('cmn x1, w2, sxtw #4')
    def test_cmn_ext_reg_sxtw4_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('cmn x1, x2, sxtx')
    def test_cmn_ext_reg_sxtx64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('cmn x1, x2, sxtx #0')
    def test_cmn_ext_reg_sxtx0_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('cmn x1, x2, sxtx #4')
    def test_cmn_ext_reg_sxtx4_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('cmn x1, x2, lsl #0')
    def test_cmn_ext_reg_lsl0_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('cmn x1, x2, lsl #4')
    def test_cmn_ext_reg_lsl4_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    # CMN (immediate).

    # 32-bit.

    @itest_setregs('W1=0x41424344')
    @itest('cmn w1, #0')
    def test_cmn_imm_min32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344')
    @itest('cmn w1, #4095')
    def test_cmn_imm_max32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344')
    @itest('cmn w1, #1')
    def test_cmn_imm32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344')
    @itest('cmn w1, #1, lsl #0')
    def test_cmn_imm_lsl0_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344')
    @itest('cmn w1, #1, lsl #12')
    def test_cmn_imm_lsl12_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748')
    @itest('cmn x1, #0')
    def test_cmn_imm_min64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748')
    @itest('cmn x1, #4095')
    def test_cmn_imm_max64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748')
    @itest('cmn x1, #1')
    def test_cmn_imm64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748')
    @itest('cmn x1, #1, lsl #0')
    def test_cmn_imm_lsl0_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748')
    @itest('cmn x1, #1, lsl #12')
    def test_cmn_imm_lsl12_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    # CMN (shifted register).

    # 32-bit.

    @itest_setregs('W1=0x41424344', 'W2=0x45464748')
    @itest('cmn w1, w2')
    def test_cmn_sft_reg32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('W1=0x41424344', 'W2=0x45464748')
    @itest('cmn w1, w2, lsl #0')
    def test_cmn_sft_reg_lsl_min32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('W1=0x41424344', 'W2=1')
    @itest('cmn w1, w2, lsl #31')
    def test_cmn_sft_reg_lsl_max32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0x45464748')
    @itest('cmn w1, w2, lsl #1')
    def test_cmn_sft_reg_lsl32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0x45464748')
    @itest('cmn w1, w2, lsr #0')
    def test_cmn_sft_reg_lsr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('W1=0x41424344', 'W2=0x80000000')
    @itest('cmn w1, w2, lsr #31')
    def test_cmn_sft_reg_lsr_max32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x80000000')
    @itest('cmn w1, w2, lsr #1')
    def test_cmn_sft_reg_lsr32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('W1=0x41424344', 'W2=0x45464748')
    @itest('cmn w1, w2, asr #0')
    def test_cmn_sft_reg_asr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('W1=0x41424344', 'W2=0x80000000')
    @itest('cmn w1, w2, asr #31')
    def test_cmn_sft_reg_asr_max32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344', 'W2=0x80000000')
    @itest('cmn w1, w2, asr #1')
    def test_cmn_sft_reg_asr32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748', 'X2=0x5152535455565758')
    @itest('cmn x1, x2')
    def test_cmn_sft_reg64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x5152535455565758')
    @itest('cmn x1, x2, lsl #0')
    def test_cmn_sft_reg_lsl_min64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=1')
    @itest('cmn x1, x2, lsl #63')
    def test_cmn_sft_reg_lsl_max64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x5152535455565758')
    @itest('cmn x1, x2, lsl #1')
    def test_cmn_sft_reg_lsl64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x5152535455565758')
    @itest('cmn x1, x2, lsr #0')
    def test_cmn_sft_reg_lsr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8000000000000000')
    @itest('cmn x1, x2, lsr #63')
    def test_cmn_sft_reg_lsr_max64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8000000000000000')
    @itest('cmn x1, x2, lsr #1')
    def test_cmn_sft_reg_lsr64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x5152535455565758')
    @itest('cmn x1, x2, asr #0')
    def test_cmn_sft_reg_asr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8000000000000000')
    @itest('cmn x1, x2, asr #63')
    def test_cmn_sft_reg_asr_max64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8000000000000000')
    @itest('cmn x1, x2, asr #1')
    def test_cmn_sft_reg_asr64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    # CMP (extended register).

    # 32-bit.

    @itest_setregs('W1=0x41424344', 'W2=0x51525384')
    @itest('cmp w1, w2, uxtb')
    def test_cmp_ext_reg_uxtb32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344', 'W2=0x51525384')
    @itest('cmp w1, w2, uxtb #0')
    def test_cmp_ext_reg_uxtb0_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344', 'W2=0x51525384')
    @itest('cmp w1, w2, uxtb #4')
    def test_cmp_ext_reg_uxtb4_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344', 'W2=0x51528354')
    @itest('cmp w1, w2, uxth')
    def test_cmp_ext_reg_uxth32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344', 'W2=0x51528354')
    @itest('cmp w1, w2, uxth #0')
    def test_cmp_ext_reg_uxth0_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344', 'W2=0x51528354')
    @itest('cmp w1, w2, uxth #4')
    def test_cmp_ext_reg_uxth4_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmp w1, w2, uxtw')
    def test_cmp_ext_reg_uxtw32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmp w1, w2, uxtw #0')
    def test_cmp_ext_reg_uxtw0_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmp w1, w2, uxtw #4')
    def test_cmp_ext_reg_uxtw4_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmp w1, w2, uxtx')
    def test_cmp_ext_reg_uxtx32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmp w1, w2, uxtx #0')
    def test_cmp_ext_reg_uxtx0_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmp w1, w2, uxtx #4')
    def test_cmp_ext_reg_uxtx4_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344', 'W2=0x51525384')
    @itest('cmp w1, w2, sxtb')
    def test_cmp_ext_reg_sxtb32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51525384')
    @itest('cmp w1, w2, sxtb #0')
    def test_cmp_ext_reg_sxtb0_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51525384')
    @itest('cmp w1, w2, sxtb #4')
    def test_cmp_ext_reg_sxtb4_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51528354')
    @itest('cmp w1, w2, sxth')
    def test_cmp_ext_reg_sxth32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51528354')
    @itest('cmp w1, w2, sxth #0')
    def test_cmp_ext_reg_sxth0_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x51528354')
    @itest('cmp w1, w2, sxth #4')
    def test_cmp_ext_reg_sxth4_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmp w1, w2, sxtw')
    def test_cmp_ext_reg_sxtw32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmp w1, w2, sxtw #0')
    def test_cmp_ext_reg_sxtw0_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmp w1, w2, sxtw #4')
    def test_cmp_ext_reg_sxtw4_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmp w1, w2, sxtx')
    def test_cmp_ext_reg_sxtx32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmp w1, w2, sxtx #0')
    def test_cmp_ext_reg_sxtx0_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmp w1, w2, sxtx #4')
    def test_cmp_ext_reg_sxtx4_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmp w1, w2, lsl #0')
    def test_cmp_ext_reg_lsl0_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('W1=0x41424344', 'W2=0x81525354')
    @itest('cmp w1, w2, lsl #4')
    def test_cmp_ext_reg_lsl4_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51525384')
    @itest('cmp x1, w2, uxtb')
    def test_cmp_ext_reg_uxtb64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51525384')
    @itest('cmp x1, w2, uxtb #0')
    def test_cmp_ext_reg_uxtb0_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51525384')
    @itest('cmp x1, w2, uxtb #4')
    def test_cmp_ext_reg_uxtb4_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51528354')
    @itest('cmp x1, w2, uxth')
    def test_cmp_ext_reg_uxth64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51528354')
    @itest('cmp x1, w2, uxth #0')
    def test_cmp_ext_reg_uxth0_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51528354')
    @itest('cmp x1, w2, uxth #4')
    def test_cmp_ext_reg_uxth4_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x81525354')
    @itest('cmp x1, w2, uxtw')
    def test_cmp_ext_reg_uxtw64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x81525354')
    @itest('cmp x1, w2, uxtw #0')
    def test_cmp_ext_reg_uxtw0_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x81525354')
    @itest('cmp x1, w2, uxtw #4')
    def test_cmp_ext_reg_uxtw4_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('cmp x1, x2, uxtx')
    def test_cmp_ext_reg_uxtx64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('cmp x1, x2, uxtx #0')
    def test_cmp_ext_reg_uxtx0_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('cmp x1, x2, uxtx #4')
    def test_cmp_ext_reg_uxtx4_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51525384')
    @itest('cmp x1, w2, sxtb')
    def test_cmp_ext_reg_sxtb64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51525384')
    @itest('cmp x1, w2, sxtb #0')
    def test_cmp_ext_reg_sxtb0_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51525384')
    @itest('cmp x1, w2, sxtb #4')
    def test_cmp_ext_reg_sxtb4_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51528354')
    @itest('cmp x1, w2, sxth')
    def test_cmp_ext_reg_sxth64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51528354')
    @itest('cmp x1, w2, sxth #0')
    def test_cmp_ext_reg_sxth0_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x51528354')
    @itest('cmp x1, w2, sxth #4')
    def test_cmp_ext_reg_sxth4_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x81525354')
    @itest('cmp x1, w2, sxtw')
    def test_cmp_ext_reg_sxtw64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x81525354')
    @itest('cmp x1, w2, sxtw #0')
    def test_cmp_ext_reg_sxtw0_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'W2=0x81525354')
    @itest('cmp x1, w2, sxtw #4')
    def test_cmp_ext_reg_sxtw4_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('cmp x1, x2, sxtx')
    def test_cmp_ext_reg_sxtx64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('cmp x1, x2, sxtx #0')
    def test_cmp_ext_reg_sxtx0_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('cmp x1, x2, sxtx #4')
    def test_cmp_ext_reg_sxtx4_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('cmp x1, x2, lsl #0')
    def test_cmp_ext_reg_lsl0_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8152535455565758')
    @itest('cmp x1, x2, lsl #4')
    def test_cmp_ext_reg_lsl4_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    # CMP (immediate).

    # 32-bit.

    @itest_setregs('W1=0x41424344')
    @itest('cmp w1, #0')
    def test_cmp_imm_min32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344')
    @itest('cmp w1, #4095')
    def test_cmp_imm_max32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344')
    @itest('cmp w1, #1')
    def test_cmp_imm32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344')
    @itest('cmp w1, #1, lsl #0')
    def test_cmp_imm_lsl0_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344')
    @itest('cmp w1, #1, lsl #12')
    def test_cmp_imm_lsl12_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748')
    @itest('cmp x1, #0')
    def test_cmp_imm_min64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748')
    @itest('cmp x1, #4095')
    def test_cmp_imm_max64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748')
    @itest('cmp x1, #1')
    def test_cmp_imm64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748')
    @itest('cmp x1, #1, lsl #0')
    def test_cmp_imm_lsl0_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748')
    @itest('cmp x1, #1, lsl #12')
    def test_cmp_imm_lsl12_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    # CMP (shifted register).

    # 32-bit.

    @itest_setregs('W1=0x41424344', 'W2=0x45464748')
    @itest('cmp w1, w2')
    def test_cmp_sft_reg32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0x45464748')
    @itest('cmp w1, w2, lsl #0')
    def test_cmp_sft_reg_lsl_min32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=1')
    @itest('cmp w1, w2, lsl #31')
    def test_cmp_sft_reg_lsl_max32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('W1=0x41424344', 'W2=0x45464748')
    @itest('cmp w1, w2, lsl #1')
    def test_cmp_sft_reg_lsl32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('W1=0x41424344', 'W2=0x45464748')
    @itest('cmp w1, w2, lsr #0')
    def test_cmp_sft_reg_lsr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0x80000000')
    @itest('cmp w1, w2, lsr #31')
    def test_cmp_sft_reg_lsr_max32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344', 'W2=0x80000000')
    @itest('cmp w1, w2, lsr #1')
    def test_cmp_sft_reg_lsr32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('W1=0x41424344', 'W2=0x45464748')
    @itest('cmp w1, w2, asr #0')
    def test_cmp_sft_reg_asr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=0x80000000')
    @itest('cmp w1, w2, asr #31')
    def test_cmp_sft_reg_asr_max32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x80000000')
    @itest('cmp w1, w2, asr #1')
    def test_cmp_sft_reg_asr32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748', 'X2=0x5152535455565758')
    @itest('cmp x1, x2')
    def test_cmp_sft_reg64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x5152535455565758')
    @itest('cmp x1, x2, lsl #0')
    def test_cmp_sft_reg_lsl_min64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=1')
    @itest('cmp x1, x2, lsl #63')
    def test_cmp_sft_reg_lsl_max64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x5152535455565758')
    @itest('cmp x1, x2, lsl #1')
    def test_cmp_sft_reg_lsl64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x5152535455565758')
    @itest('cmp x1, x2, lsr #0')
    def test_cmp_sft_reg_lsr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8000000000000000')
    @itest('cmp x1, x2, lsr #63')
    def test_cmp_sft_reg_lsr_max64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8000000000000000')
    @itest('cmp x1, x2, lsr #1')
    def test_cmp_sft_reg_lsr64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x20000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x5152535455565758')
    @itest('cmp x1, x2, asr #0')
    def test_cmp_sft_reg_asr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8000000000000000')
    @itest('cmp x1, x2, asr #63')
    def test_cmp_sft_reg_asr_max64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8000000000000000')
    @itest('cmp x1, x2, asr #1')
    def test_cmp_sft_reg_asr64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x90000000)

    # CSEL.

    # XXX: Bundles everything into one testcase.
    def test_csel(self):
        for cond in NZCV_COND_MAP:
            cond_true, cond_false = NZCV_COND_MAP[cond]

            # 32-bit.

            @itest_setregs(f'NZCV={cond_true}', 'W1=0x41424344', 'W2=0x51525354')
            @itest(f'csel w0, w1, w2, {cond}')
            def csel_true32(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0x41424344)
                assertEqual(self.rf.read('W0'), 0x41424344)

            @itest_setregs(f'NZCV={cond_false}', 'W1=0x41424344', 'W2=0x51525354')
            @itest(f'csel w0, w1, w2, {cond}')
            def csel_false32(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0x51525354)
                assertEqual(self.rf.read('W0'), 0x51525354)

            # 64-bit.

            @itest_setregs(
                f'NZCV={cond_true}',
                'X1=0x4142434445464748',
                'X2=0x5152535455565758'
            )
            @itest(f'csel x0, x1, x2, {cond}')
            def csel_true64(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0x4142434445464748)
                assertEqual(self.rf.read('W0'), 0x45464748)

            @itest_setregs(
                f'NZCV={cond_false}',
                'X1=0x4142434445464748',
                'X2=0x5152535455565758'
            )
            @itest(f'csel x0, x1, x2, {cond}')
            def csel_false64(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0x5152535455565758)
                assertEqual(self.rf.read('W0'), 0x55565758)

            if cond_true:
                self.setUp()
                csel_true32(self)

                self.setUp()
                csel_true64(self)

            if cond_false:
                self.setUp()
                csel_false32(self)

                self.setUp()
                csel_false64(self)

    # CSET.

    # XXX: Bundles everything into one testcase.
    def test_cset(self):
        for cond in NZCV_COND_MAP:
            if cond in ['al', 'nv']:
                continue
            cond_true, cond_false = NZCV_COND_MAP[cond]

            # 32-bit.

            @itest_setregs(f'NZCV={cond_true}')
            @itest(f'cset w0, {cond}')
            def cset_true32(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 1)
                assertEqual(self.rf.read('W0'), 1)

            @itest_setregs(f'NZCV={cond_false}')
            @itest(f'cset w0, {cond}')
            def cset_false32(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0)
                assertEqual(self.rf.read('W0'), 0)

            # 64-bit.

            @itest_setregs(f'NZCV={cond_true}')
            @itest(f'cset x0, {cond}')
            def cset_true64(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 1)
                assertEqual(self.rf.read('W0'), 1)

            @itest_setregs(f'NZCV={cond_false}')
            @itest(f'cset x0, {cond}')
            def cset_false64(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0)
                assertEqual(self.rf.read('W0'), 0)

            if cond_true:
                self.setUp()
                cset_true32(self)

                self.setUp()
                cset_true64(self)

            if cond_false:
                self.setUp()
                cset_false32(self)

                self.setUp()
                cset_false64(self)

    # CSETM.

    # XXX: Bundles everything into one testcase.
    def test_csetm(self):
        for cond in NZCV_COND_MAP:
            if cond in ['al', 'nv']:
                continue
            cond_true, cond_false = NZCV_COND_MAP[cond]

            # 32-bit.

            @itest_setregs(f'NZCV={cond_true}')
            @itest(f'csetm w0, {cond}')
            def csetm_true32(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0xffffffff)
                assertEqual(self.rf.read('W0'), 0xffffffff)

            @itest_setregs(f'NZCV={cond_false}')
            @itest(f'csetm w0, {cond}')
            def csetm_false32(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0)
                assertEqual(self.rf.read('W0'), 0)

            # 64-bit.

            @itest_setregs(f'NZCV={cond_true}')
            @itest(f'csetm x0, {cond}')
            def csetm_true64(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0xffffffffffffffff)
                assertEqual(self.rf.read('W0'), 0xffffffff)

            @itest_setregs(f'NZCV={cond_false}')
            @itest(f'csetm x0, {cond}')
            def csetm_false64(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0)
                assertEqual(self.rf.read('W0'), 0)

            if cond_true:
                self.setUp()
                csetm_true32(self)

                self.setUp()
                csetm_true64(self)

            if cond_false:
                self.setUp()
                csetm_false32(self)

                self.setUp()
                csetm_false64(self)

    # CSINC.

    # XXX: Bundles everything into one testcase.
    def test_csinc(self):
        for cond in NZCV_COND_MAP:
            cond_true, cond_false = NZCV_COND_MAP[cond]

            # 32-bit.

            @itest_setregs(f'NZCV={cond_true}', 'W1=0x41424344', 'W2=0x51525354')
            @itest(f'csinc w0, w1, w2, {cond}')
            def csinc_true32(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0x41424344)
                assertEqual(self.rf.read('W0'), 0x41424344)

            @itest_setregs(f'NZCV={cond_false}', 'W1=0x41424344', 'W2=0x51525354')
            @itest(f'csinc w0, w1, w2, {cond}')
            def csinc_false32(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0x51525355)
                assertEqual(self.rf.read('W0'), 0x51525355)

            @itest_setregs(f'NZCV={cond_false}', 'W1=0x41424344', 'W2=0xffffffff')
            @itest(f'csinc w0, w1, w2, {cond}')
            def csinc_false_of32(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0)
                assertEqual(self.rf.read('W0'), 0)

            # 64-bit.

            @itest_setregs(
                f'NZCV={cond_true}',
                'X1=0x4142434445464748',
                'X2=0x5152535455565758'
            )
            @itest(f'csinc x0, x1, x2, {cond}')
            def csinc_true64(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0x4142434445464748)
                assertEqual(self.rf.read('W0'), 0x45464748)

            @itest_setregs(
                f'NZCV={cond_false}',
                'X1=0x4142434445464748',
                'X2=0x5152535455565758'
            )
            @itest(f'csinc x0, x1, x2, {cond}')
            def csinc_false64(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0x5152535455565759)
                assertEqual(self.rf.read('W0'), 0x55565759)

            @itest_setregs(
                f'NZCV={cond_false}',
                'X1=0x4142434445464748',
                'X2=0xffffffffffffffff'
            )
            @itest(f'csinc x0, x1, x2, {cond}')
            def csinc_false_of64(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0)
                assertEqual(self.rf.read('W0'), 0)

            if cond_true:
                self.setUp()
                csinc_true32(self)

                self.setUp()
                csinc_true64(self)

            if cond_false:
                self.setUp()
                csinc_false32(self)

                self.setUp()
                csinc_false64(self)

                self.setUp()
                csinc_false_of32(self)

                self.setUp()
                csinc_false_of64(self)

    # CSINV.

    # XXX: Bundles everything into one testcase.
    def test_csinv(self):
        for cond in NZCV_COND_MAP:
            cond_true, cond_false = NZCV_COND_MAP[cond]

            # 32-bit.

            @itest_setregs(f'NZCV={cond_true}', 'W1=0x41424344', 'W2=0x51525354')
            @itest(f'csinv w0, w1, w2, {cond}')
            def csinv_true32(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0x41424344)
                assertEqual(self.rf.read('W0'), 0x41424344)

            @itest_setregs(f'NZCV={cond_false}', 'W1=0x41424344', 'W2=0x51525354')
            @itest(f'csinv w0, w1, w2, {cond}')
            def csinv_false32(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0xaeadacab)
                assertEqual(self.rf.read('W0'), 0xaeadacab)

            # 64-bit.

            @itest_setregs(
                f'NZCV={cond_true}',
                'X1=0x4142434445464748',
                'X2=0x5152535455565758'
            )
            @itest(f'csinv x0, x1, x2, {cond}')
            def csinv_true64(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0x4142434445464748)
                assertEqual(self.rf.read('W0'), 0x45464748)

            @itest_setregs(
                f'NZCV={cond_false}',
                'X1=0x4142434445464748',
                'X2=0x5152535455565758'
            )
            @itest(f'csinv x0, x1, x2, {cond}')
            def csinv_false64(self):
                def assertEqual(x, y):
                    self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0xaeadacabaaa9a8a7)
                assertEqual(self.rf.read('W0'), 0xaaa9a8a7)

            if cond_true:
                self.setUp()
                csinv_true32(self)

                self.setUp()
                csinv_true64(self)

            if cond_false:
                self.setUp()
                csinv_false32(self)

                self.setUp()
                csinv_false64(self)

    # DC.

    @skip_sym('dczid_el0 is read-only')
    # XXX: Check that Manticore prohibits DC ZVA until it's implemented.
    @itest('mrs x0, dczid_el0')
    def test_dczid_el0(self):
        if self.__class__.__name__ == 'Aarch64CpuInstructions':
            self.assertEqual(self.rf.read('X0'), 16)
        elif self.__class__.__name__ == 'Aarch64UnicornInstructions':
            self.assertEqual(self.rf.read('X0'), 4)
        else:
            self.fail()

    # DMB.

    def test_dmb(self):
        def dmb(x):
            @skip_sym('nothing to set')
            @itest(f'dmb {x}')
            def f(self):
                pass

            self.setUp()
            f(self)

        for imm in range(16):
            dmb(f'#{imm}')

        for bar in (
            'sy', 'st', 'ld',
            'ish', 'ishst', 'ishld',
            'nsh', 'nshst', 'nshld',
            'osh', 'oshst', 'oshld'
        ):
            dmb(f'{bar}')

    # DUP (general).

    # XXX: Uses 'reset'.

    # 8b.

    @itest_setregs('X1=0x9192939495969798')
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'dup v0.8b, w1'],
        multiple_insts=True
    )
    def test_dup_gen_8b(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0x9898989898989898)
        self.assertEqual(self.rf.read('Q0'), 0x9898989898989898)
        self.assertEqual(self.rf.read('D0'), 0x9898989898989898)
        self.assertEqual(self.rf.read('S0'), 0x98989898)
        self.assertEqual(self.rf.read('H0'), 0x9898)
        self.assertEqual(self.rf.read('B0'), 0x98)

    # 16b.

    @itest_setregs('X1=0x9192939495969798')
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'dup v0.16b, w1'],
        multiple_insts=True
    )
    def test_dup_gen_16b(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0x98989898989898989898989898989898)
        self.assertEqual(self.rf.read('Q0'), 0x98989898989898989898989898989898)
        self.assertEqual(self.rf.read('D0'), 0x9898989898989898)
        self.assertEqual(self.rf.read('S0'), 0x98989898)
        self.assertEqual(self.rf.read('H0'), 0x9898)
        self.assertEqual(self.rf.read('B0'), 0x98)

    # 4h.

    @itest_setregs('X1=0x9192939495969798')
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'dup v0.4h, w1'],
        multiple_insts=True
    )
    def test_dup_gen_4h(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0x9798979897989798)
        self.assertEqual(self.rf.read('Q0'), 0x9798979897989798)
        self.assertEqual(self.rf.read('D0'), 0x9798979897989798)
        self.assertEqual(self.rf.read('S0'), 0x97989798)
        self.assertEqual(self.rf.read('H0'), 0x9798)
        self.assertEqual(self.rf.read('B0'), 0x98)

    # 8h.

    @itest_setregs('X1=0x9192939495969798')
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'dup v0.8h, w1'],
        multiple_insts=True
    )
    def test_dup_gen_8h(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0x97989798979897989798979897989798)
        self.assertEqual(self.rf.read('Q0'), 0x97989798979897989798979897989798)
        self.assertEqual(self.rf.read('D0'), 0x9798979897989798)
        self.assertEqual(self.rf.read('S0'), 0x97989798)
        self.assertEqual(self.rf.read('H0'), 0x9798)
        self.assertEqual(self.rf.read('B0'), 0x98)

    # 2s.

    @itest_setregs('X1=0x9192939495969798')
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'dup v0.2s, w1'],
        multiple_insts=True
    )
    def test_dup_gen_2s(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0x9596979895969798)
        self.assertEqual(self.rf.read('Q0'), 0x9596979895969798)
        self.assertEqual(self.rf.read('D0'), 0x9596979895969798)
        self.assertEqual(self.rf.read('S0'), 0x95969798)
        self.assertEqual(self.rf.read('H0'), 0x9798)
        self.assertEqual(self.rf.read('B0'), 0x98)

    # 4s.

    @itest_setregs('X1=0x9192939495969798')
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'dup v0.4s, w1'],
        multiple_insts=True
    )
    def test_dup_gen_4s(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0x95969798959697989596979895969798)
        self.assertEqual(self.rf.read('Q0'), 0x95969798959697989596979895969798)
        self.assertEqual(self.rf.read('D0'), 0x9596979895969798)
        self.assertEqual(self.rf.read('S0'), 0x95969798)
        self.assertEqual(self.rf.read('H0'), 0x9798)
        self.assertEqual(self.rf.read('B0'), 0x98)

    # 2d.

    @itest_setregs('X1=0x9192939495969798')
    @itest_custom(
        # Disable traps first.
        ['mrs x30, cpacr_el1',
         'orr x30, x30, #0x300000',
         'msr cpacr_el1, x30',
         'dup v0.2d, x1'],
        multiple_insts=True
    )
    def test_dup_gen_2d(self):
        for i in range(4):
            self._execute(reset=i == 0)
        self.assertEqual(self.rf.read('V0'), 0x91929394959697989192939495969798)
        self.assertEqual(self.rf.read('Q0'), 0x91929394959697989192939495969798)
        self.assertEqual(self.rf.read('D0'), 0x9192939495969798)
        self.assertEqual(self.rf.read('S0'), 0x95969798)
        self.assertEqual(self.rf.read('H0'), 0x9798)
        self.assertEqual(self.rf.read('B0'), 0x98)

    # EOR (shifted register).

    # 32-bit.

    @itest_setregs('W1=0x41424344', 'W2=0xffff0000')
    @itest('eor w0, w1, w2')
    def test_eor32(self):
        self.assertEqual(self.rf.read('X0'), 0xbebd4344)
        self.assertEqual(self.rf.read('W0'), 0xbebd4344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0xffff0000')
    @itest('eor w0, w1, w2, lsl #0')
    def test_eor_lsl_min32(self):
        self.assertEqual(self.rf.read('X0'), 0xbebd4344)
        self.assertEqual(self.rf.read('W0'), 0xbebd4344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=1')
    @itest('eor w0, w1, w2, lsl #31')
    def test_eor_lsl_max32(self):
        self.assertEqual(self.rf.read('X0'), 0xc1424344)
        self.assertEqual(self.rf.read('W0'), 0xc1424344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0xffff000')
    @itest('eor w0, w1, w2, lsl #4')
    def test_eor_lsl32(self):
        self.assertEqual(self.rf.read('X0'), 0xbebd4344)
        self.assertEqual(self.rf.read('W0'), 0xbebd4344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0xffff0000')
    @itest('eor w0, w1, w2, lsr #0')
    def test_eor_lsr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0xbebd4344)
        self.assertEqual(self.rf.read('W0'), 0xbebd4344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x80000000')
    @itest('eor w0, w1, w2, lsr #31')
    def test_eor_lsr_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424345)
        self.assertEqual(self.rf.read('W0'), 0x41424345)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0xffff0000')
    @itest('eor w0, w1, w2, lsr #4')
    def test_eor_lsr32(self):
        self.assertEqual(self.rf.read('X0'), 0x4ebdb344)
        self.assertEqual(self.rf.read('W0'), 0x4ebdb344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0xffff0000')
    @itest('eor w0, w1, w2, asr #0')
    def test_eor_asr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0xbebd4344)
        self.assertEqual(self.rf.read('W0'), 0xbebd4344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x80000000')
    @itest('eor w0, w1, w2, asr #31')
    def test_eor_asr_max32(self):
        self.assertEqual(self.rf.read('X0'), 0xbebdbcbb)
        self.assertEqual(self.rf.read('W0'), 0xbebdbcbb)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0xf0000000')
    @itest('eor w0, w1, w2, asr #4')
    def test_eor_asr32(self):
        self.assertEqual(self.rf.read('X0'), 0xbe424344)
        self.assertEqual(self.rf.read('W0'), 0xbe424344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0xffff0000')
    @itest('eor w0, w1, w2, ror #0')
    def test_eor_ror_min32(self):
        self.assertEqual(self.rf.read('X0'), 0xbebd4344)
        self.assertEqual(self.rf.read('W0'), 0xbebd4344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0x80000001')
    @itest('eor w0, w1, w2, ror #31')
    def test_eor_ror_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424347)
        self.assertEqual(self.rf.read('W0'), 0x41424347)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0xffff000f')
    @itest('eor w0, w1, w2, ror #4')
    def test_eor_ror32(self):
        self.assertEqual(self.rf.read('X0'), 0xbebdb344)
        self.assertEqual(self.rf.read('W0'), 0xbebdb344)
        self.assertEqual(self.rf.read('NZCV'), 0)

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff00000000')
    @itest('eor x0, x1, x2')
    def test_eor64(self):
        self.assertEqual(self.rf.read('X0'), 0xbebdbcbb45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff00000000')
    @itest('eor x0, x1, x2, lsl #0')
    def test_eor_lsl_min64(self):
        self.assertEqual(self.rf.read('X0'), 0xbebdbcbb45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=1')
    @itest('eor x0, x1, x2, lsl #63')
    def test_eor_lsl_max64(self):
        self.assertEqual(self.rf.read('X0'), 0xc142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff0000000')
    @itest('eor x0, x1, x2, lsl #4')
    def test_eor_lsl64(self):
        self.assertEqual(self.rf.read('X0'), 0xbebdbcbb45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff00000000')
    @itest('eor x0, x1, x2, lsr #0')
    def test_eor_lsr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0xbebdbcbb45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8000000000000000')
    @itest('eor x0, x1, x2, lsr #63')
    def test_eor_lsr_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464749)
        self.assertEqual(self.rf.read('W0'), 0x45464749)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff00000000')
    @itest('eor x0, x1, x2, lsr #4')
    def test_eor_lsr64(self):
        self.assertEqual(self.rf.read('X0'), 0x4ebdbcbbb5464748)
        self.assertEqual(self.rf.read('W0'), 0xb5464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff00000000')
    @itest('eor x0, x1, x2, asr #0')
    def test_eor_asr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0xbebdbcbb45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8000000000000000')
    @itest('eor x0, x1, x2, asr #63')
    def test_eor_asr_max64(self):
        self.assertEqual(self.rf.read('X0'), 0xbebdbcbbbab9b8b7)
        self.assertEqual(self.rf.read('W0'), 0xbab9b8b7)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xf000000000000000')
    @itest('eor x0, x1, x2, asr #4')
    def test_eor_asr64(self):
        self.assertEqual(self.rf.read('X0'), 0xbe42434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff00000000')
    @itest('eor x0, x1, x2, ror #0')
    def test_eor_ror_min64(self):
        self.assertEqual(self.rf.read('X0'), 0xbebdbcbb45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8000000000000001')
    @itest('eor x0, x1, x2, ror #63')
    def test_eor_ror_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x414243444546474b)
        self.assertEqual(self.rf.read('W0'), 0x4546474b)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff0000000f')
    @itest('eor x0, x1, x2, ror #4')
    def test_eor_ror64(self):
        self.assertEqual(self.rf.read('X0'), 0xbebdbcbbb5464748)
        self.assertEqual(self.rf.read('W0'), 0xb5464748)
        self.assertEqual(self.rf.read('NZCV'), 0)

    # LD1 (multiple structures).

    # XXX: Uses 'reset'.

    @nottest
    def _ld1_mlt_structs(self, vess, elem_size, elem_count):
        for reg_count in range(1, 5):
            for mode in ('no_offset', 'post_indexed_reg', 'post_indexed_imm'):
                val = 0x4142434445464748
                step = 0x1010101010101010

                size = elem_size * elem_count
                dword_size = 64

                # Writeback.
                if mode == 'post_indexed_imm':
                    wback = (size // 8) * reg_count
                elif mode == 'post_indexed_reg':
                    wback = Mask(64)  # write the maximum value
                else:
                    wback = 0
                wback_reg = 'x29'

                # Create the instruction.
                insn = 'ld1 {'

                # Target registers.
                for i in range(reg_count):
                    if i != 0:
                        insn += ', '
                    insn += f'v{i}.{elem_count}{vess}'

                insn += '}, [sp]'

                # Writeback, if applicable.
                if mode == 'post_indexed_reg':
                    insn += f', {wback_reg}'
                elif mode == 'post_indexed_imm':
                    insn += f', #{wback}'

                # Create the test function.
                @itest_custom(
                    ['mrs x30, cpacr_el1',
                     'orr x30, x30, #0x300000',
                     'msr cpacr_el1, x30',
                     insn],
                    multiple_insts=True
                )
                def f(self):
                    # Disable traps first.
                    for i in range(3):
                        self._execute(reset=i == 0, check_cs=False)

                    # Push in reverse order.
                    for i in range(reg_count * (size // dword_size) - 1, -1, -1):
                        self.cpu.push_int(val + i * step)

                    # Save the stack pointer.
                    self._setreg('STACK', self.cpu.STACK)
                    stack = self.cpu.STACK

                    # Write to the writeback register, if applicable.
                    if mode == 'post_indexed_reg':
                        self.rf.write(wback_reg.upper(), wback)

                    # Execute the target instruction.
                    self._execute(reset=False)

                    def assertEqual(x, y):
                        self.assertEqual(x, y, msg=insn)
                    for i in range(reg_count):
                        # Calculate the result.
                        j = i * (size // dword_size)
                        res = val + j * step
                        res |= (val + (j + 1) * step) << dword_size
                        res = res & Mask(size)

                        # Test the target registers.
                        assertEqual(self.rf.read(f'V{i}'), res & Mask(128))
                        assertEqual(self.rf.read(f'Q{i}'), res & Mask(128))
                        assertEqual(self.rf.read(f'D{i}'), res & Mask(64))
                        assertEqual(self.rf.read(f'S{i}'), res & Mask(32))
                        assertEqual(self.rf.read(f'H{i}'), res & Mask(16))
                        assertEqual(self.rf.read(f'B{i}'), res & Mask(8))

                    # Test writeback.
                    if mode in ('post_indexed_reg', 'post_indexed_imm'):
                        assertEqual(self.rf.read('SP'), (stack + wback) & Mask(64))  # writeback
                    else:
                        assertEqual(self.rf.read('SP'), stack)  # no writeback

                self.setUp()
                f(self)

    def test_ld1_mlt_structs(self):
        self._ld1_mlt_structs(vess='b', elem_size=8, elem_count=8)
        self._ld1_mlt_structs(vess='b', elem_size=8, elem_count=16)

        self._ld1_mlt_structs(vess='h', elem_size=16, elem_count=4)
        self._ld1_mlt_structs(vess='h', elem_size=16, elem_count=8)

        self._ld1_mlt_structs(vess='s', elem_size=32, elem_count=2)
        self._ld1_mlt_structs(vess='s', elem_size=32, elem_count=4)

        self._ld1_mlt_structs(vess='d', elem_size=64, elem_count=1)
        self._ld1_mlt_structs(vess='d', elem_size=64, elem_count=2)

    # LDAXR.

    # 32-bit.

    @itest_custom('ldaxr w1, [sp]')
    def test_ldaxr32(self):
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldaxr w1, [sp, #0]')
    def test_ldaxr_0_32(self):
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    # 64-bit.

    @itest_custom('ldaxr x1, [sp]')
    def test_ldaxr64(self):
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldaxr x1, [sp, #0]')
    def test_ldaxr_0_64(self):
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    # LDP.

    # ldp w1, w2, [x27]       base register:     w1 = [x27],     w2 = [x27 + 4]
    # ldp w3, w4, [x28, #8]   base plus offset:  w3 = [x28 + 8], w4 = [x28 + 8 + 4]
    # ldp w5, w6, [x29], #8   post-indexed:      w5 = [x29],     w6 = [x29 + 4],     x29 += 8
    # ldp w7, w8, [x30, #8]!  pre-indexed:       w7 = [x30 + 8], w8 = [x30 + 8 + 4], x30 += 8

    # 32-bit.

    @itest_custom('ldp w1, w2, [sp]')
    def test_ldp_base32(self):
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('X2'), 0x41424344)
        self.assertEqual(self.rf.read('W2'), 0x41424344)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldp w1, w2, [sp, #8]')
    def test_ldp_base_offset32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('X2'), 0x41424344)
        self.assertEqual(self.rf.read('W2'), 0x41424344)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldp w1, w2, [sp, #252]')
    def test_ldp_base_offset_max32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK -= 252
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('X2'), 0x41424344)
        self.assertEqual(self.rf.read('W2'), 0x41424344)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldp w1, w2, [sp, #-256]')
    def test_ldp_base_offset_min32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK += 256
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('X2'), 0x41424344)
        self.assertEqual(self.rf.read('W2'), 0x41424344)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldp w1, w2, [sp], #8')
    def test_ldp_post_indexed32(self):
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('X2'), 0x41424344)
        self.assertEqual(self.rf.read('W2'), 0x41424344)
        self.assertEqual(self.rf.read('SP'), stack + 8)  # writeback

    @itest_custom('ldp w1, w2, [sp], #252')
    def test_ldp_post_indexed_max32(self):
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('X2'), 0x41424344)
        self.assertEqual(self.rf.read('W2'), 0x41424344)
        self.assertEqual(self.rf.read('SP'), stack + 252)  # writeback

    @itest_custom('ldp w1, w2, [sp], #-256')
    def test_ldp_post_indexed_min32(self):
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('X2'), 0x41424344)
        self.assertEqual(self.rf.read('W2'), 0x41424344)
        self.assertEqual(self.rf.read('SP'), stack - 256)  # writeback

    @itest_custom('ldp w1, w2, [sp, #8]!')
    def test_ldp_pre_indexed32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('X2'), 0x41424344)
        self.assertEqual(self.rf.read('W2'), 0x41424344)
        self.assertEqual(self.rf.read('SP'), stack + 8)  # writeback

    @itest_custom('ldp w1, w2, [sp, #252]!')
    def test_ldp_pre_indexed_max32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK -= 252
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('X2'), 0x41424344)
        self.assertEqual(self.rf.read('W2'), 0x41424344)
        self.assertEqual(self.rf.read('SP'), stack + 252)  # writeback

    @itest_custom('ldp w1, w2, [sp, #-256]!')
    def test_ldp_pre_indexed_min32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK += 256
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('X2'), 0x41424344)
        self.assertEqual(self.rf.read('W2'), 0x41424344)
        self.assertEqual(self.rf.read('SP'), stack - 256)  # writeback

    # 64-bit.

    @itest_custom('ldp x1, x2, [sp]')
    def test_ldp_base64(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('X2'), 0x5152535455565758)
        self.assertEqual(self.rf.read('W2'), 0x55565758)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldp x1, x2, [sp, #8]')
    def test_ldp_base_offset64(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x6162636465666768)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('X2'), 0x5152535455565758)
        self.assertEqual(self.rf.read('W2'), 0x55565758)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldp x1, x2, [sp, #504]')
    def test_ldp_base_offset_max64(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK -= 504
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('X2'), 0x5152535455565758)
        self.assertEqual(self.rf.read('W2'), 0x55565758)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldp x1, x2, [sp, #-512]')
    def test_ldp_base_offset_min64(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK += 512
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('X2'), 0x5152535455565758)
        self.assertEqual(self.rf.read('W2'), 0x55565758)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldp x1, x2, [sp], #8')
    def test_ldp_post_indexed64(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('X2'), 0x5152535455565758)
        self.assertEqual(self.rf.read('W2'), 0x55565758)
        self.assertEqual(self.rf.read('SP'), stack + 8)  # writeback

    @itest_custom('ldp x1, x2, [sp], #504')
    def test_ldp_post_indexed_max64(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('X2'), 0x5152535455565758)
        self.assertEqual(self.rf.read('W2'), 0x55565758)
        self.assertEqual(self.rf.read('SP'), stack + 504)  # writeback

    @itest_custom('ldp x1, x2, [sp], #-512')
    def test_ldp_post_indexed_min64(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('X2'), 0x5152535455565758)
        self.assertEqual(self.rf.read('W2'), 0x55565758)
        self.assertEqual(self.rf.read('SP'), stack - 512)  # writeback

    @itest_custom('ldp x1, x2, [sp, #8]!')
    def test_ldp_pre_indexed64(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x6162636465666768)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('X2'), 0x5152535455565758)
        self.assertEqual(self.rf.read('W2'), 0x55565758)
        self.assertEqual(self.rf.read('SP'), stack + 8)  # writeback

    @itest_custom('ldp x1, x2, [sp, #504]!')
    def test_ldp_pre_indexed_max64(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK -= 504
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('X2'), 0x5152535455565758)
        self.assertEqual(self.rf.read('W2'), 0x55565758)
        self.assertEqual(self.rf.read('SP'), stack + 504)  # writeback

    @itest_custom('ldp x1, x2, [sp, #-512]!')
    def test_ldp_pre_indexed_min64(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK += 512
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('X2'), 0x5152535455565758)
        self.assertEqual(self.rf.read('W2'), 0x55565758)
        self.assertEqual(self.rf.read('SP'), stack - 512)  # writeback

    # LDR (immediate).

    # ldr w1, [x27]          base register (opt. offset omitted):  w1 = [x27]
    # ldr w2, [x28, #8]      base plus offset:                     w2 = [x28 + 8]
    # ldr w3, [x29], #8      post-indexed:                         w3 = [x29],     x29 += 8
    # ldr w4, [x30, #8]!     pre-indexed:                          w4 = [x30 + 8], x30 += 8

    # 32-bit.

    @itest_custom('ldr w1, [sp]')
    def test_ldr_imm_base32(self):
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldr w1, [sp, #8]')
    def test_ldr_imm_base_offset32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldr w1, [sp, #16380]')
    def test_ldr_imm_base_offset_max32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK -= 16380
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldr w1, [sp], #8')
    def test_ldr_imm_post_indexed32(self):
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack + 8)  # writeback

    @itest_custom('ldr w1, [sp], #-256')
    def test_ldr_imm_post_indexed_neg32(self):
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack - 256)  # writeback

    @itest_custom('ldr w1, [sp, #8]!')
    def test_ldr_imm_pre_indexed32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack + 8)  # writeback

    @itest_custom('ldr w1, [sp, #-256]!')
    def test_ldr_imm_pre_indexed_neg32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK += 256
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack - 256)  # writeback

    # 64-bit.

    @itest_custom('ldr x1, [sp]')
    def test_ldr_imm_base64(self):
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldr x1, [sp, #8]')
    def test_ldr_imm_base_offset64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldr x1, [sp, #32760]')
    def test_ldr_imm_base_offset_max64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK -= 32760
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldr x1, [sp], #8')
    def test_ldr_imm_post_indexed64(self):
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack + 8)  # writeback

    @itest_custom('ldr x1, [sp], #-256')
    def test_ldr_imm_post_indexed_neg64(self):
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack - 256)  # writeback

    @itest_custom('ldr x1, [sp, #8]!')
    def test_ldr_imm_pre_indexed64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack + 8)  # writeback

    @itest_custom('ldr x1, [sp, #-256]!')
    def test_ldr_imm_pre_indexed_neg64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK += 256
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack - 256)  # writeback

    # LDR (literal).

    @itest_custom('ldr w0, .+8')
    def test_ldr_lit32(self):
        self._setreg('PC', self.cpu.PC)
        self.cpu.STACK = self.cpu.PC + 16
        self.cpu.push_int(0x4142434445464748)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_custom('ldr x0, .+8')
    def test_ldr_lit64(self):
        self._setreg('PC', self.cpu.PC)
        self.cpu.STACK = self.cpu.PC + 16
        self.cpu.push_int(0x4142434445464748)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_custom('ldr w0, .-8')
    def test_ldr_lit_neg32(self):
        insn = self.mem.read(self.code, 4)
        self.mem.write(self.code + 16, insn)
        self.cpu.PC += 16
        self._setreg('PC', self.cpu.PC)
        self.cpu.STACK = self.cpu.PC
        self.cpu.push_int(0x4142434445464748)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_custom('ldr x0, .-8')
    def test_ldr_lit_neg64(self):
        insn = self.mem.read(self.code, 4)
        self.mem.write(self.code + 16, insn)
        self.cpu.PC += 16
        self._setreg('PC', self.cpu.PC)
        self.cpu.STACK = self.cpu.PC
        self.cpu.push_int(0x4142434445464748)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

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
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x55565758)
        self.assertEqual(self.rf.read('W0'), 0x55565758)

    @itest_setregs('W1=-8')
    @itest_custom('ldr w0, [sp, w1, uxtw #2]')
    def test_ldr_reg_uxtw2_32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        # Account for -8 (0xfffffff8) being treated like a large positive value
        # after zero extension to 64 bits.
        self.cpu.STACK -= LSL(0xfffffff8, 2, 64)
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x55565758)
        self.assertEqual(self.rf.read('W0'), 0x55565758)

    @itest_setregs('X1=8')
    @itest_custom('ldr w0, [sp, x1]')
    def test_ldr_reg32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=2')
    @itest_custom('ldr w0, [sp, x1, lsl #2]')
    def test_ldr_reg_lsl32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('W1=-8')
    @itest_custom('ldr w0, [sp, w1, sxtw]')
    def test_ldr_reg_sxtw32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 8
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x55565758)
        self.assertEqual(self.rf.read('W0'), 0x55565758)

    @itest_setregs('W1=-8')
    @itest_custom('ldr w0, [sp, w1, sxtw #2]')
    def test_ldr_reg_sxtw2_32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += LSL(8, 2, 64)
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x55565758)
        self.assertEqual(self.rf.read('W0'), 0x55565758)

    @itest_setregs('X1=-8')
    @itest_custom('ldr w0, [sp, x1, sxtx]')
    def test_ldr_reg_sxtx32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 8
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x55565758)
        self.assertEqual(self.rf.read('W0'), 0x55565758)

    @itest_setregs('X1=-2')
    @itest_custom('ldr w0, [sp, x1, sxtx #2]')
    def test_ldr_reg_sxtx2_32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 8
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x55565758)
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
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x5152535455565758)
        self.assertEqual(self.rf.read('W0'), 0x55565758)

    @itest_setregs('W1=-8')
    @itest_custom('ldr x0, [sp, w1, uxtw #3]')
    def test_ldr_reg_uxtw3_64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        # Account for -8 (0xfffffff8) being treated like a large positive value
        # after zero extension to 64 bits.
        self.cpu.STACK -= LSL(0xfffffff8, 3, 64)
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x5152535455565758)
        self.assertEqual(self.rf.read('W0'), 0x55565758)

    @itest_setregs('X1=8')
    @itest_custom('ldr x0, [sp, x1]')
    def test_ldr_reg64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=2')
    @itest_custom('ldr x0, [sp, x1, lsl #3]')
    def test_ldr_reg_lsl64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.push_int(0x5152535455565758)
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('W1=-8')
    @itest_custom('ldr x0, [sp, w1, sxtw]')
    def test_ldr_reg_sxtw64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 8
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x5152535455565758)
        self.assertEqual(self.rf.read('W0'), 0x55565758)

    @itest_setregs('W1=-8')
    @itest_custom('ldr x0, [sp, w1, sxtw #3]')
    def test_ldr_reg_sxtw3_64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += LSL(8, 3, 64)
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x5152535455565758)
        self.assertEqual(self.rf.read('W0'), 0x55565758)

    @itest_setregs('X1=-8')
    @itest_custom('ldr x0, [sp, x1, sxtx]')
    def test_ldr_reg_sxtx64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 8
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x5152535455565758)
        self.assertEqual(self.rf.read('W0'), 0x55565758)

    @itest_setregs('X1=-2')
    @itest_custom('ldr x0, [sp, x1, sxtx #3]')
    def test_ldr_reg_sxtx3_64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 16
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x5152535455565758)
        self.assertEqual(self.rf.read('W0'), 0x55565758)

    # LDRB (immediate).

    # ldrb w1, [x27]          base register (opt. offset omitted):  w1 = [x27]
    # ldrb w2, [x28, #8]      base plus offset:                     w2 = [x28 + 8]
    # ldrb w3, [x29], #8      post-indexed:                         w3 = [x29],     x29 += 8
    # ldrb w4, [x30, #8]!     pre-indexed:                          w4 = [x30 + 8], x30 += 8

    @itest_custom('ldrb w1, [sp]')
    def test_ldrb_imm_base32(self):
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x48)
        self.assertEqual(self.rf.read('W1'), 0x48)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldrb w1, [sp, #8]')
    def test_ldrb_imm_base_offset32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x48)
        self.assertEqual(self.rf.read('W1'), 0x48)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldrb w1, [sp, #4095]')
    def test_ldrb_imm_base_offset_max32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK -= 4095
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x48)
        self.assertEqual(self.rf.read('W1'), 0x48)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldrb w1, [sp], #8')
    def test_ldrb_imm_post_indexed32(self):
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x48)
        self.assertEqual(self.rf.read('W1'), 0x48)
        self.assertEqual(self.rf.read('SP'), stack + 8)  # writeback

    @itest_custom('ldrb w1, [sp], #-256')
    def test_ldrb_imm_post_indexed_neg32(self):
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x48)
        self.assertEqual(self.rf.read('W1'), 0x48)
        self.assertEqual(self.rf.read('SP'), stack - 256)  # writeback

    @itest_custom('ldrb w1, [sp, #8]!')
    def test_ldrb_imm_pre_indexed32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x48)
        self.assertEqual(self.rf.read('W1'), 0x48)
        self.assertEqual(self.rf.read('SP'), stack + 8)  # writeback

    @itest_custom('ldrb w1, [sp, #-256]!')
    def test_ldrb_imm_pre_indexed_neg32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK += 256
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x48)
        self.assertEqual(self.rf.read('W1'), 0x48)
        self.assertEqual(self.rf.read('SP'), stack - 256)  # writeback

    # LDRB (register).

    @itest_setregs('W1=-8')
    @itest_custom('ldrb w0, [sp, w1, uxtw]')
    def test_ldrb_reg_uxtw32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        # Account for -8 (0xfffffff8) being treated like a large positive value
        # after zero extension to 64 bits.
        self.cpu.STACK -= 0xfffffff8
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x58)
        self.assertEqual(self.rf.read('W0'), 0x58)

    @itest_setregs('W1=-8')
    @itest_custom('ldrb w0, [sp, w1, uxtw #0]')
    def test_ldrb_reg_uxtw0_32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        # Account for -8 (0xfffffff8) being treated like a large positive value
        # after zero extension to 64 bits.
        self.cpu.STACK -= 0xfffffff8
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x58)
        self.assertEqual(self.rf.read('W0'), 0x58)

    @itest_setregs('X1=8')
    @itest_custom('ldrb w0, [sp, x1]')
    def test_ldrb_reg32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x48)
        self.assertEqual(self.rf.read('W0'), 0x48)

    @itest_setregs('X1=8')
    @itest_custom('ldrb w0, [sp, x1, lsl #0]')
    def test_ldrb_reg_lsl32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x48)
        self.assertEqual(self.rf.read('W0'), 0x48)

    @itest_setregs('W1=-8')
    @itest_custom('ldrb w0, [sp, w1, sxtw]')
    def test_ldrb_reg_sxtw32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 8
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x58)
        self.assertEqual(self.rf.read('W0'), 0x58)

    @itest_setregs('W1=-8')
    @itest_custom('ldrb w0, [sp, w1, sxtw #0]')
    def test_ldrb_reg_sxtw0_32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 8
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x58)
        self.assertEqual(self.rf.read('W0'), 0x58)

    @itest_setregs('X1=-8')
    @itest_custom('ldrb w0, [sp, x1, sxtx]')
    def test_ldrb_reg_sxtx32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 8
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x58)
        self.assertEqual(self.rf.read('W0'), 0x58)

    @itest_setregs('X1=-8')
    @itest_custom('ldrb w0, [sp, x1, sxtx #0]')
    def test_ldrb_reg_sxtx0_32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 8
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x58)
        self.assertEqual(self.rf.read('W0'), 0x58)

    # LDRH (immediate).

    # ldrh w1, [x27]          base register (opt. offset omitted):  w1 = [x27]
    # ldrh w2, [x28, #8]      base plus offset:                     w2 = [x28 + 8]
    # ldrh w3, [x29], #8      post-indexed:                         w3 = [x29],     x29 += 8
    # ldrh w4, [x30, #8]!     pre-indexed:                          w4 = [x30 + 8], x30 += 8

    @itest_custom('ldrh w1, [sp]')
    def test_ldrh_imm_base32(self):
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4748)
        self.assertEqual(self.rf.read('W1'), 0x4748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldrh w1, [sp, #8]')
    def test_ldrh_imm_base_offset32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4748)
        self.assertEqual(self.rf.read('W1'), 0x4748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldrh w1, [sp, #8190]')
    def test_ldrh_imm_base_offset_max32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK -= 8190
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4748)
        self.assertEqual(self.rf.read('W1'), 0x4748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldrh w1, [sp], #8')
    def test_ldrh_imm_post_indexed32(self):
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4748)
        self.assertEqual(self.rf.read('W1'), 0x4748)
        self.assertEqual(self.rf.read('SP'), stack + 8)  # writeback

    @itest_custom('ldrh w1, [sp], #-256')
    def test_ldrh_imm_post_indexed_neg32(self):
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4748)
        self.assertEqual(self.rf.read('W1'), 0x4748)
        self.assertEqual(self.rf.read('SP'), stack - 256)  # writeback

    @itest_custom('ldrh w1, [sp, #8]!')
    def test_ldrh_imm_pre_indexed32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4748)
        self.assertEqual(self.rf.read('W1'), 0x4748)
        self.assertEqual(self.rf.read('SP'), stack + 8)  # writeback

    @itest_custom('ldrh w1, [sp, #-256]!')
    def test_ldrh_imm_pre_indexed_neg32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK += 256
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4748)
        self.assertEqual(self.rf.read('W1'), 0x4748)
        self.assertEqual(self.rf.read('SP'), stack - 256)  # writeback

    # LDRH (register).

    @itest_setregs('W1=-8')
    @itest_custom('ldrh w0, [sp, w1, uxtw]')
    def test_ldrh_reg_uxtw32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        # Account for -8 (0xfffffff8) being treated like a large positive value
        # after zero extension to 64 bits.
        self.cpu.STACK -= 0xfffffff8
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x5758)
        self.assertEqual(self.rf.read('W0'), 0x5758)

    @itest_setregs('W1=-4')
    @itest_custom('ldrh w0, [sp, w1, uxtw #1]')
    def test_ldrh_reg_uxtw1_32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        # Account for -4 (0xfffffffc) being treated like a large positive value
        # after zero extension to 64 bits.
        self.cpu.STACK -= LSL(0xfffffffc, 1, 64)
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x5758)
        self.assertEqual(self.rf.read('W0'), 0x5758)

    @itest_setregs('X1=8')
    @itest_custom('ldrh w0, [sp, x1]')
    def test_ldrh_reg32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x4748)
        self.assertEqual(self.rf.read('W0'), 0x4748)

    @itest_setregs('X1=4')
    @itest_custom('ldrh w0, [sp, x1, lsl #1]')
    def test_ldrh_reg_lsl32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x4748)
        self.assertEqual(self.rf.read('W0'), 0x4748)

    @itest_setregs('W1=-8')
    @itest_custom('ldrh w0, [sp, w1, sxtw]')
    def test_ldrh_reg_sxtw32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 8
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x5758)
        self.assertEqual(self.rf.read('W0'), 0x5758)

    @itest_setregs('W1=-4')
    @itest_custom('ldrh w0, [sp, w1, sxtw #1]')
    def test_ldrh_reg_sxtw1_32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += LSL(4, 1, 64)
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x5758)
        self.assertEqual(self.rf.read('W0'), 0x5758)

    @itest_setregs('X1=-8')
    @itest_custom('ldrh w0, [sp, x1, sxtx]')
    def test_ldrh_reg_sxtx32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 8
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x5758)
        self.assertEqual(self.rf.read('W0'), 0x5758)

    @itest_setregs('X1=-4')
    @itest_custom('ldrh w0, [sp, x1, sxtx #1]')
    def test_ldrh_reg_sxtx1_32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 8
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x5758)
        self.assertEqual(self.rf.read('W0'), 0x5758)

    # LDRSW (immediate).

    # ldrsw x1, [x27]          base register (opt. offset omitted):  x1 = [x27]
    # ldrsw x2, [x28, #8]      base plus offset:                     x2 = [x28 + 8]
    # ldrsw x3, [x29], #8      post-indexed:                         x3 = [x29],     x29 += 8
    # ldrsw x4, [x30, #8]!     pre-indexed:                          x4 = [x30 + 8], x30 += 8

    @itest_custom('ldrsw x1, [sp]')
    def test_ldrsw_imm_base64(self):
        self.cpu.push_int(0x4142434485464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0xffffffff85464748)
        self.assertEqual(self.rf.read('W1'), 0x85464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldrsw x1, [sp, #8]')
    def test_ldrsw_imm_base_offset64(self):
        self.cpu.push_int(0x4142434485464748)
        self.cpu.push_int(0x5152535455565758)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0xffffffff85464748)
        self.assertEqual(self.rf.read('W1'), 0x85464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldrsw x1, [sp, #16380]')
    def test_ldrsw_imm_base_offset_max64(self):
        self.cpu.push_int(0x4142434485464748)
        self.cpu.STACK -= 16380
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0xffffffff85464748)
        self.assertEqual(self.rf.read('W1'), 0x85464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldrsw x1, [sp], #8')
    def test_ldrsw_imm_post_indexed64(self):
        self.cpu.push_int(0x4142434485464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0xffffffff85464748)
        self.assertEqual(self.rf.read('W1'), 0x85464748)
        self.assertEqual(self.rf.read('SP'), stack + 8)  # writeback

    @itest_custom('ldrsw x1, [sp], #-256')
    def test_ldrsw_imm_post_indexed_neg64(self):
        self.cpu.push_int(0x4142434485464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0xffffffff85464748)
        self.assertEqual(self.rf.read('W1'), 0x85464748)
        self.assertEqual(self.rf.read('SP'), stack - 256)  # writeback

    @itest_custom('ldrsw x1, [sp, #8]!')
    def test_ldrsw_imm_pre_indexed64(self):
        self.cpu.push_int(0x4142434485464748)
        self.cpu.push_int(0x5152535455565758)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0xffffffff85464748)
        self.assertEqual(self.rf.read('W1'), 0x85464748)
        self.assertEqual(self.rf.read('SP'), stack + 8)  # writeback

    @itest_custom('ldrsw x1, [sp, #-256]!')
    def test_ldrsw_imm_pre_indexed_neg64(self):
        self.cpu.push_int(0x4142434485464748)
        self.cpu.STACK += 256
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0xffffffff85464748)
        self.assertEqual(self.rf.read('W1'), 0x85464748)
        self.assertEqual(self.rf.read('SP'), stack - 256)  # writeback

    # LDRSW (literal).

    @itest_custom('ldrsw x0, .+8')
    def test_ldrsw_lit64(self):
        self._setreg('PC', self.cpu.PC)
        self.cpu.STACK = self.cpu.PC + 16
        self.cpu.push_int(0x4142434485464748)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0xffffffff85464748)
        self.assertEqual(self.rf.read('W0'), 0x85464748)

    @itest_custom('ldrsw x0, .-8')
    def test_ldrsw_lit_neg64(self):
        insn = self.mem.read(self.code, 4)
        self.mem.write(self.code + 16, insn)
        self.cpu.PC += 16
        self._setreg('PC', self.cpu.PC)
        self.cpu.STACK = self.cpu.PC
        self.cpu.push_int(0x4142434485464748)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0xffffffff85464748)
        self.assertEqual(self.rf.read('W0'), 0x85464748)

    # LDRSW (register).

    @itest_setregs('W1=-8')
    @itest_custom('ldrsw x0, [sp, w1, uxtw]')
    def test_ldrsw_reg_uxtw64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535485565758)
        # Account for -8 (0xfffffff8) being treated like a large positive value
        # after zero extension to 64 bits.
        self.cpu.STACK -= 0xfffffff8
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0xffffffff85565758)
        self.assertEqual(self.rf.read('W0'), 0x85565758)

    @itest_setregs('W1=-8')
    @itest_custom('ldrsw x0, [sp, w1, uxtw #2]')
    def test_ldrsw_reg_uxtw2_64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535485565758)
        # Account for -8 (0xfffffff8) being treated like a large positive value
        # after zero extension to 64 bits.
        self.cpu.STACK -= LSL(0xfffffff8, 2, 64)
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0xffffffff85565758)
        self.assertEqual(self.rf.read('W0'), 0x85565758)

    @itest_setregs('X1=8')
    @itest_custom('ldrsw x0, [sp, x1]')
    def test_ldrsw_reg64(self):
        self.cpu.push_int(0x4142434485464748)
        self.cpu.push_int(0x5152535455565758)
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0xffffffff85464748)
        self.assertEqual(self.rf.read('W0'), 0x85464748)

    @itest_setregs('X1=2')
    @itest_custom('ldrsw x0, [sp, x1, lsl #2]')
    def test_ldrsw_reg_lsl64(self):
        self.cpu.push_int(0x4142434485464748)
        self.cpu.push_int(0x5152535455565758)
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0xffffffff85464748)
        self.assertEqual(self.rf.read('W0'), 0x85464748)

    @itest_setregs('W1=-8')
    @itest_custom('ldrsw x0, [sp, w1, sxtw]')
    def test_ldrsw_reg_sxtw64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535485565758)
        self.cpu.STACK += 8
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0xffffffff85565758)
        self.assertEqual(self.rf.read('W0'), 0x85565758)

    @itest_setregs('W1=-8')
    @itest_custom('ldrsw x0, [sp, w1, sxtw #2]')
    def test_ldrsw_reg_sxtw2_64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535485565758)
        self.cpu.STACK += LSL(8, 2, 64)
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0xffffffff85565758)
        self.assertEqual(self.rf.read('W0'), 0x85565758)

    @itest_setregs('X1=-8')
    @itest_custom('ldrsw x0, [sp, x1, sxtx]')
    def test_ldrsw_reg_sxtx64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535485565758)
        self.cpu.STACK += 8
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0xffffffff85565758)
        self.assertEqual(self.rf.read('W0'), 0x85565758)

    @itest_setregs('X1=-2')
    @itest_custom('ldrsw x0, [sp, x1, sxtx #2]')
    def test_ldrsw_reg_sxtx2_64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535485565758)
        self.cpu.STACK += 8
        self._setreg('STACK', self.cpu.STACK)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0xffffffff85565758)
        self.assertEqual(self.rf.read('W0'), 0x85565758)

    # LDUR.

    # 32-bit.

    # This is actually ldur since a positive offset must be a multiple of 4 for
    # the 32-bit variant of ldr (immediate).
    @itest_custom('ldr w1, [sp, #1]')
    def test_ldr_ldur32(self):
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x44454647)
        self.assertEqual(self.rf.read('W1'), 0x44454647)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    # This is actually ldur since negative offsets are not allowed with ldr
    # (immediate).
    @itest_custom('ldr w1, [sp, #-256]')
    def test_ldr_ldur_neg32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK += 256
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldur w1, [sp, #-256]')
    def test_ldur_min32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK += 256
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldur w1, [sp, #255]')
    def test_ldur_max32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK -= 255
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldur w1, [sp, #1]')
    def test_ldur32(self):
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x44454647)
        self.assertEqual(self.rf.read('W1'), 0x44454647)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    # 64-bit.

    # This is actually ldur since a positive offset must be a multiple of 8 for
    # the 64-bit variant of ldr (immediate).
    @itest_custom('ldr x1, [sp, #4]')
    def test_ldr_ldur64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4546474851525354)
        self.assertEqual(self.rf.read('W1'), 0x51525354)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    # This is actually ldur since negative offsets are not allowed with ldr
    # (immediate).
    @itest_custom('ldr x1, [sp, #-256]')
    def test_ldr_ldur_neg64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK += 256
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldur x1, [sp, #-256]')
    def test_ldur_min64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK += 256
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldur x1, [sp, #255]')
    def test_ldur_max64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK -= 255
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldur x1, [sp, #4]')
    def test_ldur64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4546474851525354)
        self.assertEqual(self.rf.read('W1'), 0x51525354)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    # LDXR.

    # 32-bit.

    @itest_custom('ldxr w1, [sp]')
    def test_ldxr32(self):
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldxr w1, [sp, #0]')
    def test_ldxr_0_32(self):
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    # 64-bit.

    @itest_custom('ldxr x1, [sp]')
    def test_ldxr64(self):
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldxr x1, [sp, #0]')
    def test_ldxr_0_64(self):
        self.cpu.push_int(0x4142434445464748)
        self._setreg('STACK', self.cpu.STACK)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    # LSL (register).

    # 32-bit.

    @itest_setregs('W1=0x41424344', 'W2=0')
    @itest('lsl w0, w1, w2')
    def test_lsl_reg_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    @itest_setregs('W1=0x44434241', 'W2=0xffffffff')
    @itest('lsl w0, w1, w2')
    def test_lsl_reg_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x80000000)
        self.assertEqual(self.rf.read('W0'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=4')
    @itest('lsl w0, w1, w2')
    def test_lsl_reg32(self):
        self.assertEqual(self.rf.read('X0'), 0x14243440)
        self.assertEqual(self.rf.read('W0'), 0x14243440)

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748', 'X2=0')
    @itest('lsl x0, x1, x2')
    def test_lsl_reg_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0x4847464544434241', 'X2=0xffffffffffffffff')
    @itest('lsl x0, x1, x2')
    def test_lsl_reg_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x8000000000000000)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=4')
    @itest('lsl x0, x1, x2')
    def test_lsl_reg64(self):
        self.assertEqual(self.rf.read('X0'), 0x1424344454647480)
        self.assertEqual(self.rf.read('W0'), 0x54647480)

    # LSL (immediate).

    # 32-bit.

    @itest_setregs('W1=0x41424344')
    @itest('lsl w0, w1, #0')
    def test_lsl_imm_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    @itest_setregs('W1=0x44434241')
    @itest('lsl w0, w1, #31')
    def test_lsl_imm_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x80000000)
        self.assertEqual(self.rf.read('W0'), 0x80000000)

    @itest_setregs('W1=0x41424344')
    @itest('lsl w0, w1, #4')
    def test_lsl_imm32(self):
        self.assertEqual(self.rf.read('X0'), 0x14243440)
        self.assertEqual(self.rf.read('W0'), 0x14243440)

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748')
    @itest('lsl x0, x1, #0')
    def test_lsl_imm_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0x4847464544434241')
    @itest('lsl x0, x1, #63')
    def test_lsl_imm_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x8000000000000000)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('X1=0x4142434445464748')
    @itest('lsl x0, x1, #4')
    def test_lsl_imm64(self):
        self.assertEqual(self.rf.read('X0'), 0x1424344454647480)
        self.assertEqual(self.rf.read('W0'), 0x54647480)

    # LSLV.

    # 32-bit.

    @itest_setregs('W1=0x41424344', 'W2=0')
    @itest('lslv w0, w1, w2')
    def test_lslv_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    @itest_setregs('W1=0x44434241', 'W2=0xffffffff')
    @itest('lslv w0, w1, w2')
    def test_lslv_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x80000000)
        self.assertEqual(self.rf.read('W0'), 0x80000000)

    @itest_setregs('W1=0x41424344', 'W2=4')
    @itest('lslv w0, w1, w2')
    def test_lslv32(self):
        self.assertEqual(self.rf.read('X0'), 0x14243440)
        self.assertEqual(self.rf.read('W0'), 0x14243440)

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748', 'X2=0')
    @itest('lslv x0, x1, x2')
    def test_lslv_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0x4847464544434241', 'X2=0xffffffffffffffff')
    @itest('lslv x0, x1, x2')
    def test_lslv_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x8000000000000000)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=4')
    @itest('lslv x0, x1, x2')
    def test_lslv64(self):
        self.assertEqual(self.rf.read('X0'), 0x1424344454647480)
        self.assertEqual(self.rf.read('W0'), 0x54647480)

    # LSR (register).

    # 32-bit.

    @itest_setregs('W1=0x41424344', 'W2=0')
    @itest('lsr w0, w1, w2')
    def test_lsr_reg_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    @itest_setregs('W1=0x81424344', 'W2=0xffffffff')
    @itest('lsr w0, w1, w2')
    def test_lsr_reg_max32(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)

    @itest_setregs('W1=0x41424344', 'W2=4')
    @itest('lsr w0, w1, w2')
    def test_lsr_reg32(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434)
        self.assertEqual(self.rf.read('W0'), 0x4142434)

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748', 'X2=0')
    @itest('lsr x0, x1, x2')
    def test_lsr_reg_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0x8142434445464748', 'X2=0xffffffffffffffff')
    @itest('lsr x0, x1, x2')
    def test_lsr_reg_max64(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)

    @itest_setregs('X1=0x4142434445464748', 'X2=4')
    @itest('lsr x0, x1, x2')
    def test_lsr_reg64(self):
        self.assertEqual(self.rf.read('X0'), 0x414243444546474)
        self.assertEqual(self.rf.read('W0'), 0x44546474)

    # LSR (immediate).

    # 32-bit.

    @itest_setregs('W1=0x41424344')
    @itest('lsr w0, w1, #0')
    def test_lsr_imm_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    @itest_setregs('W1=0x81424344')
    @itest('lsr w0, w1, #31')
    def test_lsr_imm_max32(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)

    @itest_setregs('W1=0x41424344')
    @itest('lsr w0, w1, #4')
    def test_lsr_imm32(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434)
        self.assertEqual(self.rf.read('W0'), 0x4142434)

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748')
    @itest('lsr x0, x1, #0')
    def test_lsr_imm_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0x8142434445464748')
    @itest('lsr x0, x1, #63')
    def test_lsr_imm_max64(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)

    @itest_setregs('X1=0x4142434445464748')
    @itest('lsr x0, x1, #4')
    def test_lsr_imm64(self):
        self.assertEqual(self.rf.read('X0'), 0x414243444546474)
        self.assertEqual(self.rf.read('W0'), 0x44546474)

    # LSRV.

    # 32-bit.

    @itest_setregs('W1=0x41424344', 'W2=0')
    @itest('lsrv w0, w1, w2')
    def test_lsrv_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    @itest_setregs('W1=0x81424344', 'W2=0xffffffff')
    @itest('lsrv w0, w1, w2')
    def test_lsrv_max32(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)

    @itest_setregs('W1=0x41424344', 'W2=4')
    @itest('lsrv w0, w1, w2')
    def test_lsrv32(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434)
        self.assertEqual(self.rf.read('W0'), 0x4142434)

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748', 'X2=0')
    @itest('lsrv x0, x1, x2')
    def test_lsrv_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0x8142434445464748', 'X2=0xffffffffffffffff')
    @itest('lsrv x0, x1, x2')
    def test_lsrv_max64(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)

    @itest_setregs('X1=0x4142434445464748', 'X2=4')
    @itest('lsrv x0, x1, x2')
    def test_lsrv64(self):
        self.assertEqual(self.rf.read('X0'), 0x414243444546474)
        self.assertEqual(self.rf.read('W0'), 0x44546474)


class Aarch64CpuInstructions(unittest.TestCase, Aarch64Instructions):
    def setUp(self):
        # XXX: Adapted from the Armv7 test code.
        self.cpu = Cpu(Memory64())
        self.mem = self.cpu.memory
        self.rf = self.cpu.regfile

    def _execute(self, check_pc=True, **kwargs):
        pc = self.cpu.PC
        self.cpu.execute()
        if check_pc:
            self.assertEqual(self.cpu.PC, pc + 4)


class Aarch64UnicornInstructions(unittest.TestCase, Aarch64Instructions):
    def setUp(self):
        # XXX: Adapted from the Armv7 test code.
        self.cpu = Cpu(Memory64())
        self.mem = self.cpu.memory
        self.rf = self.cpu.regfile

    def _setupCpu(self, asm, mode=CS_MODE_ARM, multiple_insts=False):
        super()._setupCpu(asm, mode, multiple_insts)
        self.backup_emu = UnicornEmulator(self.cpu)
        # Make sure that 'self._emu' is set.
        self.backup_emu.reset()
        # XXX: Map the data region as well?
        # Map the stack.
        self.backup_emu._create_emulated_mapping(self.backup_emu._emu, self.cpu.STACK)

    # XXX: Unicorn doesn't allow to write to and read from system
    # registers directly (see 'arm64_reg_write' and 'arm64_reg_read').
    # The only way to propagate this information is via the MSR
    # (register) and MRS instructions, without resetting the emulator
    # state in between.
    # Note: in HEAD, this is fixed for some system registers, so revise
    # this after upgrading from 1.0.1.
    def _execute(self, check_pc=True, reset=True, **kwargs):
        pc = self.cpu.PC
        insn = self.cpu.decode_instruction(pc)
        self.backup_emu.emulate(insn, reset=reset)
        if check_pc:
            self.assertEqual(self.cpu.PC, pc + 4)


class Aarch64SymInstructions(unittest.TestCase, Aarch64Instructions):
    def setUp(self):
        # XXX: Adapted from the Armv7 test code.
        self.cs = ConstraintSet()
        self.cpu = Cpu(SMemory64(self.cs))
        self.mem = self.cpu.memory
        self.rf = self.cpu.regfile

    def _get_all_values1(self, expr):
        values = solver.get_all_values(self.cs, expr)
        self.assertEqual(len(values), 1)
        return values[0]

    def _execute(self, check_pc=True, check_cs=True, **kwargs):
        # Make sure there are some constraints.  Otherwise, it would be the same
        # as testing concrete values.
        if check_cs:
            self.assertTrue(len(self.cs) > 0)

        pc = self.cpu.PC

        # XXX: Copied from 'test_x86.py'.
        done = False
        while not done:
            try:
                self.cpu.execute()
                done = True
            except ConcretizeRegister as e:
                expr = getattr(self.cpu, e.reg_name)
                value = self._get_all_values1(expr)
                setattr(self.cpu, e.reg_name, value)

        if check_pc:
            self.assertEqual(self.cpu.PC, pc + 4)

    def assertEqual(self, actual, expected, *args, **kwargs):
        if isinstance(actual, int):
            pass
        else:
            actual = self._get_all_values1(actual)

        if isinstance(expected, int):
            pass
        else:
            expected = self._get_all_values1(expected)

        super().assertEqual(actual, expected, *args, **kwargs)
