import unittest

from capstone import CS_MODE_ARM
from functools import wraps
from keystone import Ks, KS_ARCH_ARM64, KS_MODE_LITTLE_ENDIAN

from manticore.core.smtlib import *
from manticore.native.memory import SMemory64, Memory64
from manticore.native.cpu.aarch64 import Aarch64Cpu as Cpu
from manticore.native.cpu.abstractcpu import (
    Interruption, InstructionNotImplementedError
)
from manticore.native.cpu.bitwise import LSL
from manticore.utils.emulate import UnicornEmulator
from .test_armv7cpu import itest_setregs
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
  'nv': (0,          None)
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


    # ADD (immediate).

    # 32-bit.

    @itest_setregs('W1=0x41424344')
    @itest('add w0, w1, #0')
    def test_add_imm_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    @itest_setregs('W1=0x41424344')
    @itest('add w0, w1, #4095')
    def test_add_imm_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x41425343)
        self.assertEqual(self.rf.read('W0'), 0x41425343)

    @itest_setregs('W1=0x41424344')
    @itest('add w0, w1, #1')
    def test_add_imm32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424345)
        self.assertEqual(self.rf.read('W0'), 0x41424345)

    @itest_setregs('W1=0x41424344')
    @itest('add w0, w1, #1, lsl #0')
    def test_add_imm_lsl0_32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424345)
        self.assertEqual(self.rf.read('W0'), 0x41424345)

    @itest_setregs('W1=0x41424344')
    @itest('add w0, w1, #1, lsl #12')
    def test_add_imm_lsl12_32(self):
        self.assertEqual(self.rf.read('X0'), 0x41425344)
        self.assertEqual(self.rf.read('W0'), 0x41425344)

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748')
    @itest('add x0, x1, #0')
    def test_add_imm_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0x4142434445464748')
    @itest('add x0, x1, #4095')
    def test_add_imm_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445465747)
        self.assertEqual(self.rf.read('W0'), 0x45465747)

    @itest_setregs('X1=0x4142434445464748')
    @itest('add x0, x1, #1')
    def test_add_imm64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464749)
        self.assertEqual(self.rf.read('W0'), 0x45464749)

    @itest_setregs('X1=0x4142434445464748')
    @itest('add x0, x1, #1, lsl #0')
    def test_add_imm_lsl0_64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464749)
        self.assertEqual(self.rf.read('W0'), 0x45464749)

    @itest_setregs('X1=0x4142434445464748')
    @itest('add x0, x1, #1, lsl #12')
    def test_add_imm_lsl12_64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445465748)
        self.assertEqual(self.rf.read('W0'), 0x45465748)


    # ADD (shifted register).

    # 32-bit.

    @itest_setregs('W1=0x41424344', 'W2=0x45464748')
    @itest('add w0, w1, w2')
    def test_add_sft_reg32(self):
        self.assertEqual(self.rf.read('X0'), 0x86888a8c)
        self.assertEqual(self.rf.read('W0'), 0x86888a8c)

    @itest_setregs('W1=0x41424344', 'W2=0x45464748')
    @itest('add w0, w1, w2, lsl #0')
    def test_add_sft_reg_lsl_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x86888a8c)
        self.assertEqual(self.rf.read('W0'), 0x86888a8c)

    @itest_setregs('W1=0x41424344', 'W2=1')
    @itest('add w0, w1, w2, lsl #31')
    def test_add_sft_reg_lsl_max32(self):
        self.assertEqual(self.rf.read('X0'), 0xc1424344)
        self.assertEqual(self.rf.read('W0'), 0xc1424344)

    @itest_setregs('W1=0x41424344', 'W2=0x45464748')
    @itest('add w0, w1, w2, lsl #1')
    def test_add_sft_reg_lsl32(self):
        self.assertEqual(self.rf.read('X0'), 0xcbced1d4)
        self.assertEqual(self.rf.read('W0'), 0xcbced1d4)

    @itest_setregs('W1=0x41424344', 'W2=0x45464748')
    @itest('add w0, w1, w2, lsr #0')
    def test_add_sft_reg_lsr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x86888a8c)
        self.assertEqual(self.rf.read('W0'), 0x86888a8c)

    @itest_setregs('W1=0x41424344', 'W2=0x80000000')
    @itest('add w0, w1, w2, lsr #31')
    def test_add_sft_reg_lsr_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424345)
        self.assertEqual(self.rf.read('W0'), 0x41424345)

    @itest_setregs('W1=0x41424344', 'W2=0x80000000')
    @itest('add w0, w1, w2, lsr #1')
    def test_add_sft_reg_lsr32(self):
        self.assertEqual(self.rf.read('X0'), 0x81424344)
        self.assertEqual(self.rf.read('W0'), 0x81424344)

    @itest_setregs('W1=0x41424344', 'W2=0x45464748')
    @itest('add w0, w1, w2, asr #0')
    def test_add_sft_reg_asr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x86888a8c)
        self.assertEqual(self.rf.read('W0'), 0x86888a8c)

    @itest_setregs('W1=0x41424344', 'W2=0x80000000')
    @itest('add w0, w1, w2, asr #31')
    def test_add_sft_reg_asr_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424343)
        self.assertEqual(self.rf.read('W0'), 0x41424343)

    @itest_setregs('W1=0x41424344', 'W2=0x80000000')
    @itest('add w0, w1, w2, asr #1')
    def test_add_sft_reg_asr32(self):
        self.assertEqual(self.rf.read('X0'), 0x01424344)
        self.assertEqual(self.rf.read('W0'), 0x01424344)

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748', 'X2=0x5152535455565758')
    @itest('add x0, x1, x2')
    def test_add_sft_reg64(self):
        self.assertEqual(self.rf.read('X0'), 0x929496989a9c9ea0)
        self.assertEqual(self.rf.read('W0'), 0x9a9c9ea0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x5152535455565758')
    @itest('add x0, x1, x2, lsl #0')
    def test_add_sft_reg_lsl_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x929496989a9c9ea0)
        self.assertEqual(self.rf.read('W0'), 0x9a9c9ea0)

    @itest_setregs('X1=0x4142434445464748', 'X2=1')
    @itest('add x0, x1, x2, lsl #63')
    def test_add_sft_reg_lsl_max64(self):
        self.assertEqual(self.rf.read('X0'), 0xc142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x5152535455565758')
    @itest('add x0, x1, x2, lsl #1')
    def test_add_sft_reg_lsl64(self):
        self.assertEqual(self.rf.read('X0'), 0xe3e6e9eceff2f5f8)
        self.assertEqual(self.rf.read('W0'), 0xeff2f5f8)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x5152535455565758')
    @itest('add x0, x1, x2, lsr #0')
    def test_add_sft_reg_lsr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x929496989a9c9ea0)
        self.assertEqual(self.rf.read('W0'), 0x9a9c9ea0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8000000000000000')
    @itest('add x0, x1, x2, lsr #63')
    def test_add_sft_reg_lsr_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464749)
        self.assertEqual(self.rf.read('W0'), 0x45464749)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8000000000000000')
    @itest('add x0, x1, x2, lsr #1')
    def test_add_sft_reg_lsr64(self):
        self.assertEqual(self.rf.read('X0'), 0x8142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x5152535455565758')
    @itest('add x0, x1, x2, asr #0')
    def test_add_sft_reg_asr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x929496989a9c9ea0)
        self.assertEqual(self.rf.read('W0'), 0x9a9c9ea0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8000000000000000')
    @itest('add x0, x1, x2, asr #63')
    def test_add_sft_reg_asr_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464747)
        self.assertEqual(self.rf.read('W0'), 0x45464747)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8000000000000000')
    @itest('add x0, x1, x2, asr #1')
    def test_add_sft_reg_asr64(self):
        self.assertEqual(self.rf.read('X0'), 0x0142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)


    # ADR.

    @itest_custom('adr x0, .0')
    def test_adr_0(self):
        pc = self.cpu.PC
        self._execute()
        self.assertEqual(self.rf.read('X0'), pc)

    @itest_custom('adr x0, .-8')
    def test_adr_neg(self):
        pc = self.cpu.PC
        self._execute()
        self.assertEqual(self.rf.read('X0'), pc - 8)

    @itest_custom('adr x0, .+8')
    def test_adr_pos(self):
        pc = self.cpu.PC
        self._execute()
        self.assertEqual(self.rf.read('X0'), pc + 8)


    # ADRP.

    @itest_custom('adrp x0, .0')
    def test_adrp_0(self):
        pc = self.cpu.PC
        self._execute()
        self.assertEqual(self.rf.read('X0'), pc)

    @itest_custom('adrp x0, .-0x1000')
    def test_adrp_neg(self):
        pc = self.cpu.PC
        self._execute()
        self.assertEqual(self.rf.read('X0'), pc - 0x1000)

    @itest_custom('adrp x0, .+0x1000')
    def test_adrp_pos(self):
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

    @itest_setregs('W1=0x41424344')
    @itest('and w0, w1, #0xffff0000')
    def test_and_imm2_32(self):
        self.assertEqual(self.rf.read('X0'), 0x41420000)
        self.assertEqual(self.rf.read('W0'), 0x41420000)

    @itest_setregs('W1=0x44434241')
    @itest('and w0, w1, #1')
    def test_and_imm3_32(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748')
    @itest('and x0, x1, #0xffff0000ffff0000')
    def test_and_imm64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142000045460000)
        self.assertEqual(self.rf.read('W0'), 0x45460000)

    @itest_setregs('X1=0x4142434445464748')
    @itest('and x0, x1, #0x0000ffff0000ffff')
    def test_and_imm2_64(self):
        self.assertEqual(self.rf.read('X0'), 0x434400004748)
        self.assertEqual(self.rf.read('W0'), 0x4748)

    @itest_setregs('X1=0x4847464544434241')
    @itest('and x0, x1, #1')
    def test_and_imm3_64(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)


    # AND (shifted register).

    # 32-bit.

    @itest_setregs('W1=0x4142ffff', 'W2=0xffff4344')
    @itest('and w0, w1, w2')
    def test_and_sft_reg32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    @itest_setregs('W1=0x4142ffff', 'W2=0xffff4344')
    @itest('and w0, w1, w2, lsl #0')
    def test_and_sft_reg_lsl_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    @itest_setregs('W1=0xffffffff', 'W2=0x80000001')
    @itest('and w0, w1, w2, lsl #31')
    def test_and_sft_reg_lsl_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x80000000)
        self.assertEqual(self.rf.read('W0'), 0x80000000)

    @itest_setregs('W1=0xffffffff', 'W2=0x81424344')
    @itest('and w0, w1, w2, lsl #4')
    def test_and_sft_reg_lsl32(self):
        self.assertEqual(self.rf.read('X0'), 0x14243440)
        self.assertEqual(self.rf.read('W0'), 0x14243440)

    @itest_setregs('W1=0x4142ffff', 'W2=0xffff4344')
    @itest('and w0, w1, w2, lsr #0')
    def test_and_sft_reg_lsr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    @itest_setregs('W1=0xffffffff', 'W2=0x80000001')
    @itest('and w0, w1, w2, lsr #31')
    def test_and_sft_reg_lsr_max32(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)

    @itest_setregs('W1=0xffffffff', 'W2=0x81424344')
    @itest('and w0, w1, w2, lsr #4')
    def test_and_sft_reg_lsr32(self):
        self.assertEqual(self.rf.read('X0'), 0x8142434)
        self.assertEqual(self.rf.read('W0'), 0x8142434)

    @itest_setregs('W1=0x4142ffff', 'W2=0xffff4344')
    @itest('and w0, w1, w2, asr #0')
    def test_and_sft_reg_asr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    @itest_setregs('W1=0xffffffff', 'W2=0x80000001')
    @itest('and w0, w1, w2, asr #31')
    def test_and_sft_reg_asr_max32(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    @itest_setregs('W1=0xffffffff', 'W2=0x81424344')
    @itest('and w0, w1, w2, asr #4')
    def test_and_sft_reg_asr32(self):
        self.assertEqual(self.rf.read('X0'), 0xf8142434)
        self.assertEqual(self.rf.read('W0'), 0xf8142434)

    @itest_setregs('W1=0x4142ffff', 'W2=0xffff4344')
    @itest('and w0, w1, w2, ror #0')
    def test_and_sft_reg_ror_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    @itest_setregs('W1=0xffffffff', 'W2=0x80000001')
    @itest('and w0, w1, w2, ror #31')
    def test_and_sft_reg_ror_max32(self):
        self.assertEqual(self.rf.read('X0'), 3)
        self.assertEqual(self.rf.read('W0'), 3)

    @itest_setregs('W1=0xffffffff', 'W2=0x81424344')
    @itest('and w0, w1, w2, ror #4')
    def test_and_sft_reg_ror32(self):
        self.assertEqual(self.rf.read('X0'), 0x48142434)
        self.assertEqual(self.rf.read('W0'), 0x48142434)

    # 64-bit.

    @itest_setregs('X1=0x41424344ffffffff', 'X2=0xffffffff45464748')
    @itest('and x0, x1, x2')
    def test_and_sft_reg64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0x41424344ffffffff', 'X2=0xffffffff45464748')
    @itest('and x0, x1, x2, lsl #0')
    def test_and_sft_reg_lsl_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8000000000000001')
    @itest('and x0, x1, x2, lsl #63')
    def test_and_sft_reg_lsl_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x8000000000000000)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8142434445464748')
    @itest('and x0, x1, x2, lsl #4')
    def test_and_sft_reg_lsl64(self):
        self.assertEqual(self.rf.read('X0'), 0x1424344454647480)
        self.assertEqual(self.rf.read('W0'), 0x54647480)

    @itest_setregs('X1=0x41424344ffffffff', 'X2=0xffffffff45464748')
    @itest('and x0, x1, x2, lsr #0')
    def test_and_sft_reg_lsr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8000000000000001')
    @itest('and x0, x1, x2, lsr #63')
    def test_and_sft_reg_lsr_max64(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8142434445464748')
    @itest('and x0, x1, x2, lsr #4')
    def test_and_sft_reg_lsr64(self):
        self.assertEqual(self.rf.read('X0'), 0x814243444546474)
        self.assertEqual(self.rf.read('W0'), 0x44546474)

    @itest_setregs('X1=0x41424344ffffffff', 'X2=0xffffffff45464748')
    @itest('and x0, x1, x2, asr #0')
    def test_and_sft_reg_asr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8000000000000001')
    @itest('and x0, x1, x2, asr #63')
    def test_and_sft_reg_asr_max64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8142434445464748')
    @itest('and x0, x1, x2, asr #4')
    def test_and_sft_reg_asr64(self):
        self.assertEqual(self.rf.read('X0'), 0xf814243444546474)
        self.assertEqual(self.rf.read('W0'), 0x44546474)

    @itest_setregs('X1=0x41424344ffffffff', 'X2=0xffffffff45464748')
    @itest('and x0, x1, x2, ror #0')
    def test_and_sft_reg_ror_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8000000000000001')
    @itest('and x0, x1, x2, ror #63')
    def test_and_sft_reg_ror_max64(self):
        self.assertEqual(self.rf.read('X0'), 3)
        self.assertEqual(self.rf.read('W0'), 3)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8142434445464748')
    @itest('and x0, x1, x2, ror #4')
    def test_and_sft_reg_ror64(self):
        self.assertEqual(self.rf.read('X0'), 0x8814243444546474)
        self.assertEqual(self.rf.read('W0'), 0x44546474)


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
                assertEqual = lambda x, y: self.assertEqual(x, y, msg=cond)
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
        pc = self.cpu.PC
        # Execute just two instructions, so it doesn't loop indefinitely.
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc - 8)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 42)
        self.assertEqual(self.rf.read('X2'), 0)


    # BIC (shifted register).

    # 32-bit.

    @itest_setregs('W1=0x41424344', 'W2=0xffff0000')
    @itest('bic w0, w1, w2')
    def test_bic32(self):
        self.assertEqual(self.rf.read('X0'), 0x4344)
        self.assertEqual(self.rf.read('W0'), 0x4344)

    @itest_setregs('W1=0x41424344', 'W2=0xffff0000')
    @itest('bic w0, w1, w2, lsl #0')
    def test_bic_lsl_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x4344)
        self.assertEqual(self.rf.read('W0'), 0x4344)

    @itest_setregs('W1=0xf1424344', 'W2=1')
    @itest('bic w0, w1, w2, lsl #31')
    def test_bic_lsl_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x71424344)
        self.assertEqual(self.rf.read('W0'), 0x71424344)

    @itest_setregs('W1=0x41424344', 'W2=0xffff000')
    @itest('bic w0, w1, w2, lsl #4')
    def test_bic_lsl32(self):
        self.assertEqual(self.rf.read('X0'), 0x4344)
        self.assertEqual(self.rf.read('W0'), 0x4344)

    @itest_setregs('W1=0x41424344', 'W2=0xffff0000')
    @itest('bic w0, w1, w2, lsr #0')
    def test_bic_lsr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x4344)
        self.assertEqual(self.rf.read('W0'), 0x4344)

    @itest_setregs('W1=0x4142434f', 'W2=0x80000000')
    @itest('bic w0, w1, w2, lsr #31')
    def test_bic_lsr_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434e)
        self.assertEqual(self.rf.read('W0'), 0x4142434e)

    @itest_setregs('W1=0x41424344', 'W2=0xffff0000')
    @itest('bic w0, w1, w2, lsr #4')
    def test_bic_lsr32(self):
        self.assertEqual(self.rf.read('X0'), 0x40000344)
        self.assertEqual(self.rf.read('W0'), 0x40000344)

    @itest_setregs('W1=0x41424344', 'W2=0xffff0000')
    @itest('bic w0, w1, w2, asr #0')
    def test_bic_asr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x4344)
        self.assertEqual(self.rf.read('W0'), 0x4344)

    @itest_setregs('W1=0x41424344', 'W2=0x80000000')
    @itest('bic w0, w1, w2, asr #31')
    def test_bic_asr_max32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('W1=0x41424344', 'W2=0xf0000000')
    @itest('bic w0, w1, w2, asr #4')
    def test_bic_asr32(self):
        self.assertEqual(self.rf.read('X0'), 0x424344)
        self.assertEqual(self.rf.read('W0'), 0x424344)

    @itest_setregs('W1=0x41424344', 'W2=0xffff0000')
    @itest('bic w0, w1, w2, ror #0')
    def test_bic_ror_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x4344)
        self.assertEqual(self.rf.read('W0'), 0x4344)

    @itest_setregs('W1=0x4142434f', 'W2=0x80000001')
    @itest('bic w0, w1, w2, ror #31')
    def test_bic_ror_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434c)
        self.assertEqual(self.rf.read('W0'), 0x4142434c)

    @itest_setregs('W1=0x41424344', 'W2=0xffff000f')
    @itest('bic w0, w1, w2, ror #4')
    def test_bic_ror32(self):
        self.assertEqual(self.rf.read('X0'), 0x344)
        self.assertEqual(self.rf.read('W0'), 0x344)

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff00000000')
    @itest('bic x0, x1, x2')
    def test_bic64(self):
        self.assertEqual(self.rf.read('X0'), 0x45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff00000000')
    @itest('bic x0, x1, x2, lsl #0')
    def test_bic_lsl_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0xf142434445464748', 'X2=1')
    @itest('bic x0, x1, x2, lsl #63')
    def test_bic_lsl_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x7142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff0000000')
    @itest('bic x0, x1, x2, lsl #4')
    def test_bic_lsl64(self):
        self.assertEqual(self.rf.read('X0'), 0x45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff00000000')
    @itest('bic x0, x1, x2, lsr #0')
    def test_bic_lsr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0x414243444546474f', 'X2=0x8000000000000000')
    @itest('bic x0, x1, x2, lsr #63')
    def test_bic_lsr_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x414243444546474e)
        self.assertEqual(self.rf.read('W0'), 0x4546474e)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff00000000')
    @itest('bic x0, x1, x2, lsr #4')
    def test_bic_lsr64(self):
        self.assertEqual(self.rf.read('X0'), 0x4000000005464748)
        self.assertEqual(self.rf.read('W0'), 0x5464748)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff00000000')
    @itest('bic x0, x1, x2, asr #0')
    def test_bic_asr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x8000000000000000')
    @itest('bic x0, x1, x2, asr #63')
    def test_bic_asr_max64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xf000000000000000')
    @itest('bic x0, x1, x2, asr #4')
    def test_bic_asr64(self):
        self.assertEqual(self.rf.read('X0'), 0x42434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff00000000')
    @itest('bic x0, x1, x2, ror #0')
    def test_bic_ror_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0x414243444546474f', 'X2=0x8000000000000001')
    @itest('bic x0, x1, x2, ror #63')
    def test_bic_ror_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x414243444546474c)
        self.assertEqual(self.rf.read('W0'), 0x4546474c)

    @itest_setregs('X1=0x4142434445464748', 'X2=0xffffffff0000000f')
    @itest('bic x0, x1, x2, ror #4')
    def test_bic_ror64(self):
        self.assertEqual(self.rf.read('X0'), 0x5464748)
        self.assertEqual(self.rf.read('W0'), 0x5464748)


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
        self.cpu.W0 = 0
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
        self.cpu.W0 = 1
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
        self.cpu.W0 = 0
        self.cpu.PC += 4
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
        self.cpu.W0 = 1
        self.cpu.PC += 4
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
        self.cpu.X0 = 0
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
        self.cpu.X0 = 1
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
        self.cpu.X0 = 0
        self.cpu.PC += 4
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
        self.cpu.X0 = 1
        self.cpu.PC += 4
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
        self.cpu.W0 = 0
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
        self.cpu.W0 = 1
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
        self.cpu.W0 = 0
        self.cpu.PC += 4
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
        self.cpu.W0 = 1
        self.cpu.PC += 4
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
        self.cpu.X0 = 0
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
        self.cpu.X0 = 1
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
        self.cpu.X0 = 0
        self.cpu.PC += 4
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
        self.cpu.X0 = 1
        self.cpu.PC += 4
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 4)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0)
        self.assertEqual(self.rf.read('X2'), 43)


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
                assertEqual = lambda x, y: self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0x41424345)
                assertEqual(self.rf.read('W0'), 0x41424345)

            @itest_setregs(f'NZCV={cond_true}', 'W1=0xffffffff')
            @itest(f'cinc w0, w1, {cond}')
            def cinc_true_of32(self):
                assertEqual = lambda x, y: self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0)
                assertEqual(self.rf.read('W0'), 0)

            @itest_setregs(f'NZCV={cond_false}', 'W1=0x41424344')
            @itest(f'cinc w0, w1, {cond}')
            def cinc_false32(self):
                assertEqual = lambda x, y: self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0x41424344)
                assertEqual(self.rf.read('W0'), 0x41424344)

            # 64-bit.

            @itest_setregs(f'NZCV={cond_true}', 'X1=0x4142434445464748')
            @itest(f'cinc x0, x1, {cond}')
            def cinc_true64(self):
                assertEqual = lambda x, y: self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0x4142434445464749)
                assertEqual(self.rf.read('W0'), 0x45464749)

            @itest_setregs(f'NZCV={cond_true}', 'X1=0xffffffffffffffff')
            @itest(f'cinc x0, x1, {cond}')
            def cinc_true_of64(self):
                assertEqual = lambda x, y: self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0)
                assertEqual(self.rf.read('W0'), 0)

            @itest_setregs(f'NZCV={cond_false}', 'X1=0x4142434445464748')
            @itest(f'cinc x0, x1, {cond}')
            def cinc_false64(self):
                assertEqual = lambda x, y: self.assertEqual(x, y, msg=cond)
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


    # CSEL.

    # XXX: Bundles everything into one testcase.
    def test_csel(self):
        for cond in NZCV_COND_MAP:
            cond_true, cond_false = NZCV_COND_MAP[cond]

            # 32-bit.

            @itest_setregs(f'NZCV={cond_true}', 'W1=0x41424344', 'W2=0x51525354')
            @itest(f'csel w0, w1, w2, {cond}')
            def csel_true32(self):
                assertEqual = lambda x, y: self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0x41424344)
                assertEqual(self.rf.read('W0'), 0x41424344)

            @itest_setregs(f'NZCV={cond_false}', 'W1=0x41424344', 'W2=0x51525354')
            @itest(f'csel w0, w1, w2, {cond}')
            def csel_false32(self):
                assertEqual = lambda x, y: self.assertEqual(x, y, msg=cond)
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
                assertEqual = lambda x, y: self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0x4142434445464748)
                assertEqual(self.rf.read('W0'), 0x45464748)

            @itest_setregs(
                f'NZCV={cond_false}',
                'X1=0x4142434445464748',
                'X2=0x5152535455565758'
            )
            @itest(f'csel x0, x1, x2, {cond}')
            def csel_false64(self):
                assertEqual = lambda x, y: self.assertEqual(x, y, msg=cond)
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
                assertEqual = lambda x, y: self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 1)
                assertEqual(self.rf.read('W0'), 1)

            @itest_setregs(f'NZCV={cond_false}')
            @itest(f'cset w0, {cond}')
            def cset_false32(self):
                assertEqual = lambda x, y: self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0)
                assertEqual(self.rf.read('W0'), 0)

            # 64-bit.

            @itest_setregs(f'NZCV={cond_true}')
            @itest(f'cset x0, {cond}')
            def cset_true64(self):
                assertEqual = lambda x, y: self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 1)
                assertEqual(self.rf.read('W0'), 1)

            @itest_setregs(f'NZCV={cond_false}')
            @itest(f'cset x0, {cond}')
            def cset_false64(self):
                assertEqual = lambda x, y: self.assertEqual(x, y, msg=cond)
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


    # CSINC.

    # XXX: Bundles everything into one testcase.
    def test_csinc(self):
        for cond in NZCV_COND_MAP:
            cond_true, cond_false = NZCV_COND_MAP[cond]

            # 32-bit.

            @itest_setregs(f'NZCV={cond_true}', 'W1=0x41424344', 'W2=0x51525354')
            @itest(f'csinc w0, w1, w2, {cond}')
            def csinc_true32(self):
                assertEqual = lambda x, y: self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0x41424344)
                assertEqual(self.rf.read('W0'), 0x41424344)

            @itest_setregs(f'NZCV={cond_false}', 'W1=0x41424344', 'W2=0x51525354')
            @itest(f'csinc w0, w1, w2, {cond}')
            def csinc_false32(self):
                assertEqual = lambda x, y: self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0x51525355)
                assertEqual(self.rf.read('W0'), 0x51525355)

            @itest_setregs(f'NZCV={cond_false}', 'W1=0x41424344', 'W2=0xffffffff')
            @itest(f'csinc w0, w1, w2, {cond}')
            def csinc_false_of32(self):
                assertEqual = lambda x, y: self.assertEqual(x, y, msg=cond)
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
                assertEqual = lambda x, y: self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0x4142434445464748)
                assertEqual(self.rf.read('W0'), 0x45464748)

            @itest_setregs(
                f'NZCV={cond_false}',
                'X1=0x4142434445464748',
                'X2=0x5152535455565758'
            )
            @itest(f'csinc x0, x1, x2, {cond}')
            def csinc_false64(self):
                assertEqual = lambda x, y: self.assertEqual(x, y, msg=cond)
                assertEqual(self.rf.read('X0'), 0x5152535455565759)
                assertEqual(self.rf.read('W0'), 0x55565759)

            @itest_setregs(
                f'NZCV={cond_false}',
                'X1=0x4142434445464748',
                'X2=0xffffffffffffffff'
            )
            @itest(f'csinc x0, x1, x2, {cond}')
            def csinc_false_of64(self):
                assertEqual = lambda x, y: self.assertEqual(x, y, msg=cond)
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


    # LDR (immediate).

    # ldr w1, [x27]          base register (opt. offset omitted):  w1 = [x27]
    # ldr w2, [x28, #8]      base plus offset:                     w2 = [x28 + 8]
    # ldr w3, [x29], #8      post-indexed:                         w3 = [x29],     x29 += 8
    # ldr w4, [x30, #8]!     pre-indexed:                          w4 = [x30 + 8], x30 += 8

    # 32-bit.

    @itest_custom('ldr w1, [sp]')
    def test_ldr_imm_base32(self):
        self.cpu.push_int(0x4142434445464748)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldr w1, [sp, #8]')
    def test_ldr_imm_base_offset32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldr w1, [sp, #16380]')
    def test_ldr_imm_base_offset_max32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK -= 16380
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldr w1, [sp], #8')
    def test_ldr_imm_post_indexed32(self):
        self.cpu.push_int(0x4142434445464748)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack + 8)  # writeback

    @itest_custom('ldr w1, [sp], #-256')
    def test_ldr_imm_post_indexed_neg32(self):
        self.cpu.push_int(0x4142434445464748)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack - 256)  # writeback

    @itest_custom('ldr w1, [sp, #8]!')
    def test_ldr_imm_pre_indexed32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack + 8)  # writeback

    @itest_custom('ldr w1, [sp, #-256]!')
    def test_ldr_imm_pre_indexed_neg32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK += 256
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack - 256)  # writeback

    # 64-bit.

    @itest_custom('ldr x1, [sp]')
    def test_ldr_imm_base64(self):
        self.cpu.push_int(0x4142434445464748)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldr x1, [sp, #8]')
    def test_ldr_imm_base_offset64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldr x1, [sp, #32760]')
    def test_ldr_imm_base_offset_max64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK -= 32760
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldr x1, [sp], #8')
    def test_ldr_imm_post_indexed64(self):
        self.cpu.push_int(0x4142434445464748)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('SP'), stack + 8)  # writeback

    @itest_custom('ldr x1, [sp], #-256')
    def test_ldr_imm_post_indexed_neg64(self):
        self.cpu.push_int(0x4142434445464748)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('SP'), stack - 256)  # writeback

    @itest_custom('ldr x1, [sp, #8]!')
    def test_ldr_imm_pre_indexed64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('SP'), stack + 8)  # writeback

    @itest_custom('ldr x1, [sp, #-256]!')
    def test_ldr_imm_pre_indexed_neg64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK += 256
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('SP'), stack - 256)  # writeback


    # LDR (literal).

    @itest_custom('ldr w0, .+8')
    def test_ldr_lit32(self):
        self.cpu.STACK = self.cpu.PC + 16
        self.cpu.push_int(0x4142434445464748)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_custom('ldr x0, .+8')
    def test_ldr_lit64(self):
        self.cpu.STACK = self.cpu.PC + 16
        self.cpu.push_int(0x4142434445464748)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)

    @itest_custom('ldr w0, .-8')
    def test_ldr_lit_neg32(self):
        insn = self.mem.read(self.code, 4)
        self.mem.write(self.code + 16, insn)
        self.cpu.PC += 16
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
        self.cpu.STACK = self.cpu.PC
        self.cpu.push_int(0x4142434445464748)
        self._execute()
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
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x55565758)
        self.assertEqual(self.rf.read('W0'), 0x55565758)

    @itest_setregs('X1=8')
    @itest_custom('ldr w0, [sp, x1]')
    def test_ldr_reg32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=2')
    @itest_custom('ldr w0, [sp, x1, lsl #2]')
    def test_ldr_reg_lsl32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('W1=-8')
    @itest_custom('ldr w0, [sp, w1, sxtw]')
    def test_ldr_reg_sxtw32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 8
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x55565758)
        self.assertEqual(self.rf.read('W0'), 0x55565758)

    @itest_setregs('W1=-8')
    @itest_custom('ldr w0, [sp, w1, sxtw #2]')
    def test_ldr_reg_sxtw2_32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += LSL(8, 2, 32)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x55565758)
        self.assertEqual(self.rf.read('W0'), 0x55565758)

    @itest_setregs('X1=-8')
    @itest_custom('ldr w0, [sp, x1, sxtx]')
    def test_ldr_reg_sxtx32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 8
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x55565758)
        self.assertEqual(self.rf.read('W0'), 0x55565758)

    @itest_setregs('X1=-2')
    @itest_custom('ldr w0, [sp, x1, sxtx #2]')
    def test_ldr_reg_sxtx2_32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 8
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
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x5152535455565758)

    @itest_setregs('W1=-8')
    @itest_custom('ldr x0, [sp, w1, uxtw #3]')
    def test_ldr_reg_uxtw3_64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        # Account for -8 (0xfffffff8) being treated like a large positive value
        # after zero extension to 64 bits.
        self.cpu.STACK -= LSL(0xfffffff8, 3, 64)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x5152535455565758)

    @itest_setregs('X1=8')
    @itest_custom('ldr x0, [sp, x1]')
    def test_ldr_reg64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)

    @itest_setregs('X1=2')
    @itest_custom('ldr x0, [sp, x1, lsl #3]')
    def test_ldr_reg_lsl64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.push_int(0x5152535455565758)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)

    @itest_setregs('W1=-8')
    @itest_custom('ldr x0, [sp, w1, sxtw]')
    def test_ldr_reg_sxtw64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 8
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x5152535455565758)

    @itest_setregs('W1=-8')
    @itest_custom('ldr x0, [sp, w1, sxtw #3]')
    def test_ldr_reg_sxtw3_64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += LSL(8, 3, 32)
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x5152535455565758)

    @itest_setregs('X1=-8')
    @itest_custom('ldr x0, [sp, x1, sxtx]')
    def test_ldr_reg_sxtx64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 8
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x5152535455565758)

    @itest_setregs('X1=-2')
    @itest_custom('ldr x0, [sp, x1, sxtx #3]')
    def test_ldr_reg_sxtx3_64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 16
        self._execute()
        self.assertEqual(self.rf.read('X0'), 0x5152535455565758)


    # LDUR.

    # 32-bit.

    # This is actually ldur since a positive offset must be a multiple of 4 for
    # the 32-bit variant of ldr (immediate).
    @itest_custom('ldr w1, [sp, #1]')
    def test_ldr_ldur32(self):
        self.cpu.push_int(0x4142434445464748)
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
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldur w1, [sp, #-256]')
    def test_ldur_min32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK += 256
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldur w1, [sp, #255]')
    def test_ldur_max32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK -= 255
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldur w1, [sp, #1]')
    def test_ldur32(self):
        self.cpu.push_int(0x4142434445464748)
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
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldur x1, [sp, #-256]')
    def test_ldur_min64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK += 256
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldur x1, [sp, #255]')
    def test_ldur_max64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK -= 255
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_custom('ldur x1, [sp, #4]')
    def test_ldur64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4546474851525354)
        self.assertEqual(self.rf.read('W1'), 0x51525354)
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


    # MADD.

    # 32-bit.

    @itest_setregs('W1=0xffffffff', 'W2=0xffffffff', 'W3=0xffffffff')
    @itest('madd w0, w1, w2, w3')
    def test_madd_max32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('W1=-1', 'W2=-1', 'W3=-1')
    @itest('madd w0, w1, w2, w3')
    def test_madd_neg32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('W1=1', 'W2=1', 'W3=0xffffffff')
    @itest('madd w0, w1, w2, w3')
    def test_madd_of1_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('W1=0xffffffff', 'W2=2', 'W3=0xffffffff')
    @itest('madd w0, w1, w2, w3')
    def test_madd_of2_32(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffd)
        self.assertEqual(self.rf.read('W0'), 0xfffffffd)

    @itest_setregs('W1=2', 'W2=3', 'W3=4')
    @itest('madd w0, w1, w2, w3')
    def test_madd32(self):
        self.assertEqual(self.rf.read('X0'), 10)
        self.assertEqual(self.rf.read('W0'), 10)

    # 64-bit.

    @itest_setregs(
        'X1=0xffffffffffffffff',
        'X2=0xffffffffffffffff',
        'X3=0xffffffffffffffff'
    )
    @itest('madd x0, x1, x2, x3')
    def test_madd_max64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('X1=-1', 'X2=-1', 'X3=-1')
    @itest('madd x0, x1, x2, x3')
    def test_madd_neg64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('X1=1', 'X2=1', 'X3=0xffffffffffffffff')
    @itest('madd x0, x1, x2, x3')
    def test_madd_of1_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs(
        'X1=0xffffffffffffffff',
        'X2=2',
        'X3=0xffffffffffffffff'
    )
    @itest('madd x0, x1, x2, x3')
    def test_madd_of2_64(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffffffffffd)
        self.assertEqual(self.rf.read('W0'), 0xfffffffd)

    @itest_setregs('X1=2', 'X2=3', 'X3=4')
    @itest('madd x0, x1, x2, x3')
    def test_madd64(self):
        self.assertEqual(self.rf.read('X0'), 10)
        self.assertEqual(self.rf.read('W0'), 10)


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
        self._execute()
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
        self._execute()
        self.assertEqual(self.rf.read('X0'), MAGIC_32)
        self.assertEqual(self.rf.read('W0'), MAGIC_32)


    # MOV (inverted wide immediate).

    # 32-bit.

    @itest('mov w0, #0xffffffff')
    def test_mov_inv_wide_imm32(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    @itest('mov w0, #-1')
    def test_mov_inv_wide_imm_neg32(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    # 64-bit.

    @itest('mov x0, #0xffffffffffffffff')
    def test_mov_inv_wide_imm64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    @itest('mov x0, #-1')
    def test_mov_inv_wide_imm_neg64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)


    # MOV (wide immediate).

    # 32-bit.

    @itest('mov w0, #0')
    def test_mov_wide_imm_min32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest('mov w0, #0xffff0000')
    def test_mov_wide_imm_max32(self):
        self.assertEqual(self.rf.read('X0'), 0xffff0000)
        self.assertEqual(self.rf.read('W0'), 0xffff0000)

    @itest('mov w0, #1')
    def test_mov_wide_imm32(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)

    # 64-bit.

    @itest('mov x0, #0')
    def test_mov_wide_imm_min64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest('mov x0, #0xffff000000000000')
    def test_mov_wide_imm_max64(self):
        self.assertEqual(self.rf.read('X0'), 0xffff000000000000)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest('mov x0, #1')
    def test_mov_wide_imm64(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)


    # MOV (bitmask immediate).

    @itest('mov w0, #0x7ffffffe')
    def test_mov_bmask_imm32(self):
        self.assertEqual(self.rf.read('X0'), 0x7ffffffe)
        self.assertEqual(self.rf.read('W0'), 0x7ffffffe)

    @itest('mov x0, #0x7ffffffffffffffe')
    def test_mov_bmask_imm64(self):
        self.assertEqual(self.rf.read('X0'), 0x7ffffffffffffffe)
        self.assertEqual(self.rf.read('W0'), 0xfffffffe)


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


    # MOV misc.

    @itest_multiple(["movn x0, #0", "mov w0, #1"])
    def test_mov_same_reg32(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)


    # MOVK.

    # 32-bit.

    @itest_setregs('W0=0x41424344')
    @itest('movk w0, #0')
    def test_movk_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41420000)
        self.assertEqual(self.rf.read('W0'), 0x41420000)

    @itest_setregs('W0=0x41424344')
    @itest('movk w0, #0xffff')
    def test_movk_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x4142ffff)
        self.assertEqual(self.rf.read('W0'), 0x4142ffff)

    @itest_setregs('W0=0x41424344')
    @itest('movk w0, #0x1001')
    def test_movk32(self):
        self.assertEqual(self.rf.read('X0'), 0x41421001)
        self.assertEqual(self.rf.read('W0'), 0x41421001)

    @itest_setregs('W0=0x41424344')
    @itest('movk w0, #0, lsl #0')
    def test_movk_sft0_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41420000)
        self.assertEqual(self.rf.read('W0'), 0x41420000)

    @itest_setregs('W0=0x41424344')
    @itest('movk w0, #0xffff, lsl #0')
    def test_movk_sft0_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x4142ffff)
        self.assertEqual(self.rf.read('W0'), 0x4142ffff)

    @itest_setregs('W0=0x41424344')
    @itest('movk w0, #0x1001, lsl #0')
    def test_movk_sft0_32(self):
        self.assertEqual(self.rf.read('X0'), 0x41421001)
        self.assertEqual(self.rf.read('W0'), 0x41421001)

    @itest_setregs('W0=0x41424344')
    @itest('movk w0, #0, lsl #16')
    def test_movk_sft16_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x4344)
        self.assertEqual(self.rf.read('W0'), 0x4344)

    @itest_setregs('W0=0x41424344')
    @itest('movk w0, #0xffff, lsl #16')
    def test_movk_sft16_max32(self):
        self.assertEqual(self.rf.read('X0'), 0xffff4344)
        self.assertEqual(self.rf.read('W0'), 0xffff4344)

    @itest_setregs('W0=0x41424344')
    @itest('movk w0, #0x1001, lsl #16')
    def test_movk_sft16_32(self):
        self.assertEqual(self.rf.read('X0'), 0x10014344)
        self.assertEqual(self.rf.read('W0'), 0x10014344)

    # 64-bit.

    @itest_setregs('X0=0x4142434445464748')
    @itest('movk x0, #0')
    def test_movk_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445460000)
        self.assertEqual(self.rf.read('W0'), 0x45460000)

    @itest_setregs('X0=0x4142434445464748')
    @itest('movk x0, #0xffff')
    def test_movk_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x414243444546ffff)
        self.assertEqual(self.rf.read('W0'), 0x4546ffff)

    @itest_setregs('X0=0x4142434445464748')
    @itest('movk x0, #0x1001')
    def test_movk64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445461001)
        self.assertEqual(self.rf.read('W0'), 0x45461001)

    @itest_setregs('X0=0x4142434445464748')
    @itest('movk x0, #0, lsl #0')
    def test_movk_sft0_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445460000)
        self.assertEqual(self.rf.read('W0'), 0x45460000)

    @itest_setregs('X0=0x4142434445464748')
    @itest('movk x0, #0xffff, lsl #0')
    def test_movk_sft0_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x414243444546ffff)
        self.assertEqual(self.rf.read('W0'), 0x4546ffff)

    @itest_setregs('X0=0x4142434445464748')
    @itest('movk x0, #0x1001, lsl #0')
    def test_movk_sft0_64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445461001)
        self.assertEqual(self.rf.read('W0'), 0x45461001)

    @itest_setregs('X0=0x4142434445464748')
    @itest('movk x0, #0, lsl #16')
    def test_movk_sft16_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434400004748)
        self.assertEqual(self.rf.read('W0'), 0x4748)

    @itest_setregs('X0=0x4142434445464748')
    @itest('movk x0, #0xffff, lsl #16')
    def test_movk_sft16_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344ffff4748)
        self.assertEqual(self.rf.read('W0'), 0xffff4748)

    @itest_setregs('X0=0x4142434445464748')
    @itest('movk x0, #0x1001, lsl #16')
    def test_movk_sft16_64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434410014748)
        self.assertEqual(self.rf.read('W0'), 0x10014748)

    @itest_setregs('X0=0x4142434445464748')
    @itest('movk x0, #0, lsl #32')
    def test_movk_sft32_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142000045464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X0=0x4142434445464748')
    @itest('movk x0, #0xffff, lsl #32')
    def test_movk_sft32_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142ffff45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X0=0x4142434445464748')
    @itest('movk x0, #0x1001, lsl #32')
    def test_movk_sft32_64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142100145464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X0=0x4142434445464748')
    @itest('movk x0, #0, lsl #48')
    def test_movk_sft48_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X0=0x4142434445464748')
    @itest('movk x0, #0xffff, lsl #48')
    def test_movk_sft48_max64(self):
        self.assertEqual(self.rf.read('X0'), 0xffff434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X0=0x4142434445464748')
    @itest('movk x0, #0x1001, lsl #48')
    def test_movk_sft48_64(self):
        self.assertEqual(self.rf.read('X0'), 0x1001434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)


    # MOVN.

    # 32-bit.

    @itest("movn w0, #0")
    def test_movn32(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    @itest("movn w0, #65535")
    def test_movn_max32(self):
        self.assertEqual(self.rf.read('X0'), 0xffff0000)
        self.assertEqual(self.rf.read('W0'), 0xffff0000)

    @itest("movn w0, #65535, lsl #16")
    def test_movn_sft16_32(self):
        self.assertEqual(self.rf.read('X0'), 0xffff)
        self.assertEqual(self.rf.read('W0'), 0xffff)

    # 64-bit.

    @itest("movn x0, #0")
    def test_movn64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    @itest("movn x0, #65535")
    def test_movn_max64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffffffff0000)
        self.assertEqual(self.rf.read('W0'), 0xffff0000)

    @itest("movn x0, #65535, lsl #16")
    def test_movn_sft16_64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffff0000ffff)
        self.assertEqual(self.rf.read('W0'), 0xffff)

    @itest("movn x0, #65535, lsl #32")
    def test_movn_sft32_64(self):
        self.assertEqual(self.rf.read('X0'), 0xffff0000ffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    @itest("movn x0, #65535, lsl #48")
    def test_movn_sft48_64(self):
        self.assertEqual(self.rf.read('X0'), 0x0000ffffffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)


    # MOVZ.

    # 32-bit.

    @itest("movz w0, #0")
    def test_movz32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest("movz w0, #65535")
    def test_movz_max32(self):
        self.assertEqual(self.rf.read('X0'), 0xffff)
        self.assertEqual(self.rf.read('W0'), 0xffff)

    @itest("movz w0, #65535, lsl #16")
    def test_movz_sft16_32(self):
        self.assertEqual(self.rf.read('X0'), 0xffff0000)
        self.assertEqual(self.rf.read('W0'), 0xffff0000)

    # 64-bit.

    @itest("movz x0, #0")
    def test_movz64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest("movz x0, #65535")
    def test_movz_max64(self):
        self.assertEqual(self.rf.read('X0'), 0xffff)
        self.assertEqual(self.rf.read('W0'), 0xffff)

    @itest("movz x0, #65535, lsl #16")
    def test_movz_sft16_64(self):
        self.assertEqual(self.rf.read('X0'), 0xffff0000)
        self.assertEqual(self.rf.read('W0'), 0xffff0000)

    @itest("movz x0, #65535, lsl #32")
    def test_movz_sft32_64(self):
        self.assertEqual(self.rf.read('X0'), 0xffff00000000)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest("movz x0, #65535, lsl #48")
    def test_movz_sft48_64(self):
        self.assertEqual(self.rf.read('X0'), 0xffff000000000000)
        self.assertEqual(self.rf.read('W0'), 0)


    # MSUB.

    # 32-bit.

    @itest_setregs('W1=0xffffffff', 'W2=0xffffffff', 'W3=0xffffffff')
    @itest('msub w0, w1, w2, w3')
    def test_msub_max32(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffe)
        self.assertEqual(self.rf.read('W0'), 0xfffffffe)

    @itest_setregs('W1=-1', 'W2=-1', 'W3=-1')
    @itest('msub w0, w1, w2, w3')
    def test_msub_neg32(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffe)
        self.assertEqual(self.rf.read('W0'), 0xfffffffe)

    @itest_setregs('W1=0xffffffff', 'W2=2', 'W3=1')
    @itest('msub w0, w1, w2, w3')
    def test_msub_of32(self):
        self.assertEqual(self.rf.read('X0'), 3)
        self.assertEqual(self.rf.read('W0'), 3)

    @itest_setregs('W1=3', 'W2=4', 'W3=5')
    @itest('msub w0, w1, w2, w3')
    def test_msub32(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffff9)
        self.assertEqual(self.rf.read('W0'), 0xfffffff9)

    # 64-bit.

    @itest_setregs(
        'X1=0xffffffffffffffff',
        'X2=0xffffffffffffffff',
        'X3=0xffffffffffffffff'
    )
    @itest('msub x0, x1, x2, x3')
    def test_msub_max64(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffffffffffe)
        self.assertEqual(self.rf.read('W0'), 0xfffffffe)

    @itest_setregs('X1=-1', 'X2=-1', 'X3=-1')
    @itest('msub x0, x1, x2, x3')
    def test_msub_neg64(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffffffffffe)
        self.assertEqual(self.rf.read('W0'), 0xfffffffe)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=2', 'X3=1')
    @itest('msub x0, x1, x2, x3')
    def test_msub_of64(self):
        self.assertEqual(self.rf.read('X0'), 3)
        self.assertEqual(self.rf.read('W0'), 3)

    @itest_setregs('X1=3', 'X2=4', 'X3=5')
    @itest('msub x0, x1, x2, x3')
    def test_msub64(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffffffffff9)
        self.assertEqual(self.rf.read('W0'), 0xfffffff9)


    # MUL.

    # 32-bit.

    @itest_setregs('W1=0xffffffff', 'W2=0xffffffff')
    @itest('mul w0, w1, w2')
    def test_mul_max32(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)

    @itest_setregs('W1=-1', 'W2=-1')
    @itest('mul w0, w1, w2')
    def test_mul_neg32(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)

    @itest_setregs('W1=0x80000000', 'W2=2')
    @itest('mul w0, w1, w2')
    def test_mul_of32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('W1=2', 'W2=3')
    @itest('mul w0, w1, w2')
    def test_mul32(self):
        self.assertEqual(self.rf.read('X0'), 6)
        self.assertEqual(self.rf.read('W0'), 6)

    @itest_setregs('W1=2', 'W2=-3')
    @itest('mul w0, w1, w2')
    def test_mul_pos_neg32(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffa)
        self.assertEqual(self.rf.read('W0'), 0xfffffffa)

    # 64-bit.

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0xffffffffffffffff')
    @itest('mul x0, x1, x2')
    def test_mul_max64(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)

    @itest_setregs('X1=-1', 'X2=-1')
    @itest('mul x0, x1, x2')
    def test_mul_neg64(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)

    @itest_setregs('X1=0x8000000000000000', 'X2=2')
    @itest('mul x0, x1, x2')
    def test_mul_of64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('X1=2', 'X2=3')
    @itest('mul x0, x1, x2')
    def test_mul64(self):
        self.assertEqual(self.rf.read('X0'), 6)
        self.assertEqual(self.rf.read('W0'), 6)

    @itest_setregs('X1=2', 'X2=-3')
    @itest('mul x0, x1, x2')
    def test_mul_pos_neg64(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffffffffffa)
        self.assertEqual(self.rf.read('W0'), 0xfffffffa)


    # NOP.

    @itest_custom('nop')
    def test_nop(self):
        pc = self.cpu.PC
        self._execute(check_pc=False)  # check explicitly
        self.assertEqual(self.rf.read('PC'), pc + 4)


    # ORR (immediate).

    # 32-bit.

    @itest_setregs('W1=0x41420000')
    @itest('orr w0, w1, #0xffff')
    def test_orr_imm32(self):
        self.assertEqual(self.rf.read('X0'), 0x4142ffff)
        self.assertEqual(self.rf.read('W0'), 0x4142ffff)

    @itest_setregs('W1=0x00004344')
    @itest('orr w0, w1, #0xffff0000')
    def test_orr_imm2_32(self):
        self.assertEqual(self.rf.read('X0'), 0xffff4344)
        self.assertEqual(self.rf.read('W0'), 0xffff4344)

    @itest_setregs('W1=0x41424344')
    @itest('orr w0, w1, #1')
    def test_orr_imm3_32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424345)
        self.assertEqual(self.rf.read('W0'), 0x41424345)

    # 64-bit.

    @itest_setregs('X1=0x0000414200004344')
    @itest('orr x0, x1, #0xffff0000ffff0000')
    def test_orr_imm64(self):
        self.assertEqual(self.rf.read('X0'), 0xffff4142ffff4344)
        self.assertEqual(self.rf.read('W0'), 0xffff4344)

    @itest_setregs('X1=0x4142000043440000')
    @itest('orr x0, x1, #0x0000ffff0000ffff')
    def test_orr_imm2_64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142ffff4344ffff)
        self.assertEqual(self.rf.read('W0'), 0x4344ffff)

    @itest_setregs('X1=0x4142434445464748')
    @itest('orr x0, x1, #1')
    def test_orr_imm3_64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464749)
        self.assertEqual(self.rf.read('W0'), 0x45464749)


    # ORR (shifted register).

    # 32-bit.

    @itest_setregs('W1=0x41420000', 'W2=0x4344')
    @itest('orr w0, w1, w2')
    def test_orr_sft_reg32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    @itest_setregs('W1=0x41420000', 'W2=0x4344')
    @itest('orr w0, w1, w2, lsl #0')
    def test_orr_sft_reg_lsl_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    @itest_setregs('W1=0x4142', 'W2=1')
    @itest('orr w0, w1, w2, lsl #31')
    def test_orr_sft_reg_lsl_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x80004142)
        self.assertEqual(self.rf.read('W0'), 0x80004142)

    @itest_setregs('W1=0x41420000', 'W2=0x4344')
    @itest('orr w0, w1, w2, lsl #1')
    def test_orr_sft_reg_lsl32(self):
        self.assertEqual(self.rf.read('X0'), 0x41428688)
        self.assertEqual(self.rf.read('W0'), 0x41428688)

    @itest_setregs('W1=0x41420000', 'W2=0x4344')
    @itest('orr w0, w1, w2, lsr #0')
    def test_orr_sft_reg_lsr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    @itest_setregs('W1=0x41420000', 'W2=0x80000000')
    @itest('orr w0, w1, w2, lsr #31')
    def test_orr_sft_reg_lsr_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x41420001)
        self.assertEqual(self.rf.read('W0'), 0x41420001)

    @itest_setregs('W1=0x4142', 'W2=0x80000000')
    @itest('orr w0, w1, w2, lsr #1')
    def test_orr_sft_reg_lsr32(self):
        self.assertEqual(self.rf.read('X0'), 0x40004142)
        self.assertEqual(self.rf.read('W0'), 0x40004142)

    @itest_setregs('W1=0x41420000', 'W2=0x4344')
    @itest('orr w0, w1, w2, asr #0')
    def test_orr_sft_reg_asr_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    @itest_setregs('W1=0x41420000', 'W2=0x80000000')
    @itest('orr w0, w1, w2, asr #31')
    def test_orr_sft_reg_asr_max32(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    @itest_setregs('W1=0x4142', 'W2=0x80000000')
    @itest('orr w0, w1, w2, asr #1')
    def test_orr_sft_reg_asr32(self):
        self.assertEqual(self.rf.read('X0'), 0xc0004142)
        self.assertEqual(self.rf.read('W0'), 0xc0004142)

    @itest_setregs('W1=0x41420000', 'W2=0x4344')
    @itest('orr w0, w1, w2, ror #0')
    def test_orr_sft_reg_ror_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    @itest_setregs('W1=0x4140', 'W2=0x80000001')
    @itest('orr w0, w1, w2, ror #31')
    def test_orr_sft_reg_ror_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x00004143)
        self.assertEqual(self.rf.read('W0'), 0x00004143)

    @itest_setregs('W1=0x4142', 'W2=1')
    @itest('orr w0, w1, w2, ror #1')
    def test_orr_sft_reg_ror32(self):
        self.assertEqual(self.rf.read('X0'), 0x80004142)
        self.assertEqual(self.rf.read('W0'), 0x80004142)

    # 64-bit.

    @itest_setregs('X1=0x4142434400000000', 'X2=0x45464748')
    @itest('orr x0, x1, x2')
    def test_orr_sft_reg64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0x4142434400000000', 'X2=0x45464748')
    @itest('orr x0, x1, x2, lsl #0')
    def test_orr_sft_reg_lsl_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0x41424344', 'X2=1')
    @itest('orr x0, x1, x2, lsl #63')
    def test_orr_sft_reg_lsl_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x8000000041424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    @itest_setregs('X1=0x4142434400000000', 'X2=0x45464748')
    @itest('orr x0, x1, x2, lsl #1')
    def test_orr_sft_reg_lsl64(self):
        self.assertEqual(self.rf.read('X0'), 0x414243448a8c8e90)
        self.assertEqual(self.rf.read('W0'), 0x8a8c8e90)

    @itest_setregs('X1=0x4142434400000000', 'X2=0x45464748')
    @itest('orr x0, x1, x2, lsr #0')
    def test_orr_sft_reg_lsr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0x4142434400000000', 'X2=0x8000000000000000')
    @itest('orr x0, x1, x2, lsr #63')
    def test_orr_sft_reg_lsr_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434400000001)
        self.assertEqual(self.rf.read('W0'), 1)

    @itest_setregs('X1=0x41424344', 'X2=0x8000000000000000')
    @itest('orr x0, x1, x2, lsr #1')
    def test_orr_sft_reg_lsr64(self):
        self.assertEqual(self.rf.read('X0'), 0x4000000041424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    @itest_setregs('X1=0x4142434400000000', 'X2=0x45464748')
    @itest('orr x0, x1, x2, asr #0')
    def test_orr_sft_reg_asr_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0x4142434400000000', 'X2=0x8000000000000000')
    @itest('orr x0, x1, x2, asr #63')
    def test_orr_sft_reg_asr_max64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    @itest_setregs('X1=0x41424344', 'X2=0x8000000000000000')
    @itest('orr x0, x1, x2, asr #1')
    def test_orr_sft_reg_asr64(self):
        self.assertEqual(self.rf.read('X0'), 0xc000000041424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    @itest_setregs('X1=0x4142434400000000', 'X2=0x45464748')
    @itest('orr x0, x1, x2, ror #0')
    def test_orr_sft_reg_ror_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X1=0x4142434445464740', 'X2=0x8000000000000001')
    @itest('orr x0, x1, x2, ror #63')
    def test_orr_sft_reg_ror_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464743)
        self.assertEqual(self.rf.read('W0'), 0x45464743)

    @itest_setregs('X1=0x41424344', 'X2=1')
    @itest('orr x0, x1, x2, ror #1')
    def test_orr_sft_reg_ror64(self):
        self.assertEqual(self.rf.read('X0'), 0x8000000041424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)


    # RBIT.

    # 32-bit.

    @itest_setregs('W1=0')
    @itest('rbit w0, w1')
    def test_rbit_min32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('W1=0xffffffff')
    @itest('rbit w0, w1')
    def test_rbit_max32(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    @itest_setregs('W1=1')
    @itest('rbit w0, w1')
    def test_rbit_one32(self):
        self.assertEqual(self.rf.read('X0'), 0x80000000)
        self.assertEqual(self.rf.read('W0'), 0x80000000)

    @itest_setregs('W1=0x41424344')
    @itest('rbit w0, w1')
    def test_rbit32(self):
        self.assertEqual(self.rf.read('X0'), 0x22c24282)
        self.assertEqual(self.rf.read('W0'), 0x22c24282)

    # 64-bit.

    @itest_setregs('X1=0')
    @itest('rbit x0, x1')
    def test_rbit_min64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('X1=0xffffffffffffffff')
    @itest('rbit x0, x1')
    def test_rbit_max64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    @itest_setregs('X1=1')
    @itest('rbit x0, x1')
    def test_rbit_one64(self):
        self.assertEqual(self.rf.read('X0'), 0x8000000000000000)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('X1=0x4142434445464748')
    @itest('rbit x0, x1')
    def test_rbit64(self):
        self.assertEqual(self.rf.read('X0'), 0x12e262a222c24282)
        self.assertEqual(self.rf.read('W0'), 0x22c24282)


    # RET.

    @itest_custom('ret')
    def test_ret(self):
        pc = self.cpu.PC
        self.cpu.X30 = pc + 16
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 16)

    @itest_custom('ret X0')
    def test_ret_reg(self):
        pc = self.cpu.PC
        self.cpu.X0 = pc + 32
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 32)


    # REV.

    # 32-bit.

    @itest_setregs('W1=0')
    @itest('rev w0, w1')
    def test_rev_min32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('W1=0xffffffff')
    @itest('rev w0, w1')
    def test_rev_max32(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    @itest_setregs('W1=0x41424344')
    @itest('rev w0, w1')
    def test_rev32(self):
        self.assertEqual(self.rf.read('X0'), 0x44434241)
        self.assertEqual(self.rf.read('W0'), 0x44434241)

    # 64-bit.

    @itest_setregs('X1=0')
    @itest('rev x0, x1')
    def test_rev_min64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('X1=0xffffffffffffffff')
    @itest('rev x0, x1')
    def test_rev_max64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    @itest_setregs('X1=0x4142434445464748')
    @itest('rev x0, x1')
    def test_rev64(self):
        self.assertEqual(self.rf.read('X0'), 0x4847464544434241)
        self.assertEqual(self.rf.read('W0'), 0x44434241)


    # SBFIZ.

    # 32-bit.

    # Copy 1 bit from the least significant bits of the source register to bit
    # position 0 of the destination register.
    @itest_setregs('W1=0x44434241')
    @itest('sbfiz w0, w1, #0, #1')
    def test_sbfiz_min_min32(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    # Copy 32 bits from the least significant bits of the source register to bit
    # position 0 of the destination register.
    @itest_setregs('W1=0x41424344')
    @itest('sbfiz w0, w1, #0, #32')
    def test_sbfiz_min_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    # Copy 1 bit from the least significant bits of the source register to bit
    # position 31 of the destination register.
    @itest_setregs('W1=0x44434241')
    @itest('sbfiz w0, w1, #31, #1')
    def test_sbfiz_max_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x80000000)
        self.assertEqual(self.rf.read('W0'), 0x80000000)

    # Copy 15 bits from the least significant bits of the source register to bit
    # position 17 of the destination register.
    @itest_setregs('W1=0x41427fff')
    @itest('sbfiz w0, w1, #17, #15')
    def test_sbfiz32(self):
        self.assertEqual(self.rf.read('X0'), 0xfffe0000)
        self.assertEqual(self.rf.read('W0'), 0xfffe0000)

    # 64-bit.

    # Copy 1 bit from the least significant bits of the source register to bit
    # position 0 of the destination register.
    @itest_setregs('X1=0x4847464544434241')
    @itest('sbfiz x0, x1, #0, #1')
    def test_sbfiz_min_min64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    # Copy 64 bits from the least significant bits of the source register to bit
    # position 0 of the destination register.
    @itest_setregs('X1=0x4142434445464748')
    @itest('sbfiz x0, x1, #0, #64')
    def test_sbfiz_min_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    # Copy 1 bit from the least significant bits of the source register to bit
    # position 63 of the destination register.
    @itest_setregs('X1=0x4847464544434241')
    @itest('sbfiz x0, x1, #63, #1')
    def test_sbfiz_max_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x8000000000000000)
        self.assertEqual(self.rf.read('W0'), 0)

    # Copy 31 bit from the least significant bits of the source register to bit
    # position 33 of the destination register.
    @itest_setregs('X1=0x414243447fffffff')
    @itest('sbfiz x0, x1, #33, #31')
    def test_sbfiz64(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffe00000000)
        self.assertEqual(self.rf.read('W0'), 0)


    # SBFM.

    # 32-bit.

    # This is actually sbfx.
    # Copy 5 - 3 + 1 bits from bit position 3 of the source register to the
    # least significant bits of the destination register.  Set bits above
    # the bitfield to the most significant bit of the bitfield and to zero
    # below the bitfield.
    @itest_setregs('W0=0xffffffff', 'W1=0x41424328')
    @itest('sbfm w0, w1, #3, #5')
    def test_sbfm_ge32(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffd)
        self.assertEqual(self.rf.read('W0'), 0xfffffffd)

    # This is actually sbfiz.
    # Copy 3 + 1 bits from the least significant bits of the source register to
    # bit position 32 - 5 of the destination register.  Set bits above
    # the bitfield to the most significant bit of the bitfield and to zero
    # below the bitfield.
    @itest_setregs('W0=0xffffffff', 'W1=0x41424349')
    @itest('sbfm w0, w1, #5, #3')
    def test_sbfm_lt32(self):
        self.assertEqual(self.rf.read('X0'), 0xc8000000)
        self.assertEqual(self.rf.read('W0'), 0xc8000000)

    # This is actually asr.
    # Copy 31 - 0 + 1 bits from bit position 0 of the source register to the
    # least significant bits of the destination register.  Set bits above
    # the bitfield to the most significant bit of the bitfield and to zero
    # below the bitfield.
    @itest_setregs('W0=0xffffffff', 'W1=0x41424344')
    @itest('sbfm w0, w1, #0, #31')
    def test_sbfm_ge_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    # This is actually sbfiz.
    # Copy 0 + 1 bits from the least significant bits of the source register to
    # bit position 32 - 31 of the destination register.  Set bits above
    # the bitfield to the most significant bit of the bitfield and to zero
    # below the bitfield.
    @itest_setregs('W0=0xffffffff','W1=0x44434241')
    @itest('sbfm w0, w1, #31, #0')
    def test_sbfm_lt_max32(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffe)
        self.assertEqual(self.rf.read('W0'), 0xfffffffe)

    # This is actually sbfx.
    # Copy 0 - 0 + 1 bits from bit position 0 of the source register to the
    # least significant bits of the destination register.  Set bits above
    # the bitfield to the most significant bit of the bitfield and to zero
    # below the bitfield.
    @itest_setregs('W0=0xffffffff', 'W1=0x44434241')
    @itest('sbfm w0, w1, #0, #0')
    def test_sbfm_ge_min32(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    # This is actually sbfiz.
    # Copy 0 + 1 bits from the least significant bits of the source register to
    # bit position 32 - 1 of the destination register.  Set bits above
    # the bitfield to the most significant bit of the bitfield and to zero
    # below the bitfield.
    @itest_setregs('W0=0xffffffff', 'W1=0x44434241')
    @itest('sbfm w0, w1, #1, #0')
    def test_sbfm_lt_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x80000000)
        self.assertEqual(self.rf.read('W0'), 0x80000000)

    # This is actually sxtb.
    # Copy 7 - 0 + 1 bits from bit position 0 of the source register to the
    # least significant bits of the destination register.  Set bits above
    # the bitfield to the most significant bit of the bitfield and to zero
    # below the bitfield.
    @itest_setregs('W0=0xffffffff', 'W1=0x41424344')
    @itest('sbfm w0, w1, #0, #7')
    def test_sbfm_sxtb_zero32(self):
        self.assertEqual(self.rf.read('X0'), 0x44)
        self.assertEqual(self.rf.read('W0'), 0x44)

    @itest_setregs('W0=0xffffffff', 'W1=0x41424384')
    @itest('sbfm w0, w1, #0, #7')
    def test_sbfm_sxtb_one32(self):
        self.assertEqual(self.rf.read('X0'), 0xffffff84)
        self.assertEqual(self.rf.read('W0'), 0xffffff84)

    # This is actually sxth.
    # Copy 15 - 0 + 1 bits from bit position 0 of the source register to the
    # least significant bits of the destination register.  Set bits above
    # the bitfield to the most significant bit of the bitfield and to zero
    # below the bitfield.
    @itest_setregs('W0=0xffffffff', 'W1=0x41424344')
    @itest('sbfm w0, w1, #0, #15')
    def test_sbfm_sxth_zero32(self):
        self.assertEqual(self.rf.read('X0'), 0x4344)
        self.assertEqual(self.rf.read('W0'), 0x4344)

    @itest_setregs('W0=0xffffffff', 'W1=0x41428344')
    @itest('sbfm w0, w1, #0, #15')
    def test_sbfm_sxth_one32(self):
        self.assertEqual(self.rf.read('X0'), 0xffff8344)
        self.assertEqual(self.rf.read('W0'), 0xffff8344)

    # 64-bit.

    # This is actually sbfx.
    # Copy 5 - 3 + 1 bits from bit position 3 of the source register to the
    # least significant bits of the destination register.  Set bits above
    # the bitfield to the most significant bit of the bitfield and to zero
    # below the bitfield.
    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x4142434445464728')
    @itest('sbfm x0, x1, #3, #5')
    def test_sbfm_ge64(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffffffffffd)
        self.assertEqual(self.rf.read('W0'), 0xfffffffd)

    # This is actually sbfiz.
    # Copy 3 + 1 bits from the least significant bits of the source register to
    # bit position 64 - 5 of the destination register.  Set bits above
    # the bitfield to the most significant bit of the bitfield and to zero
    # below the bitfield.
    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x4142434445464749')
    @itest('sbfm x0, x1, #5, #3')
    def test_sbfm_lt64(self):
        self.assertEqual(self.rf.read('X0'), 0xc800000000000000)
        self.assertEqual(self.rf.read('W0'), 0)

    # This is actually asr.
    # Copy 63 - 0 + 1 bits from bit position 0 of the source register to the
    # least significant bits of the destination register.  Set bits above
    # the bitfield to the most significant bit of the bitfield and to zero
    # below the bitfield.
    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x4142434445464748')
    @itest('sbfm x0, x1, #0, #63')
    def test_sbfm_ge_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    # This is actually sbfiz.
    # Copy 0 + 1 bits from the least significant bits of the source register to
    # bit position 64 - 63 of the destination register.  Set bits above
    # the bitfield to the most significant bit of the bitfield and to zero
    # below the bitfield.
    @itest_setregs('X0=0xffffffffffffffff','X1=0x4847464544434241')
    @itest('sbfm x0, x1, #63, #0')
    def test_sbfm_lt_max64(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffffffffffe)
        self.assertEqual(self.rf.read('W0'), 0xfffffffe)

    # This is actually sbfx.
    # Copy 0 - 0 + 1 bits from bit position 0 of the source register to the
    # least significant bits of the destination register.  Set bits above
    # the bitfield to the most significant bit of the bitfield and to zero
    # below the bitfield.
    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x4847464544434241')
    @itest('sbfm x0, x1, #0, #0')
    def test_sbfm_ge_min64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    # This is actually sbfiz.
    # Copy 0 + 1 bits from the least significant bits of the source register to
    # bit position 64 - 1 of the destination register.  Set bits above
    # the bitfield to the most significant bit of the bitfield and to zero
    # below the bitfield.
    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x4847464544434241')
    @itest('sbfm x0, x1, #1, #0')
    def test_sbfm_lt_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x8000000000000000)
        self.assertEqual(self.rf.read('W0'), 0)

    # This is actually sxtb.
    # Copy 7 - 0 + 1 bits from bit position 0 of the source register to the
    # least significant bits of the destination register.  Set bits above
    # the bitfield to the most significant bit of the bitfield and to zero
    # below the bitfield.
    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x4142434445464748')
    @itest('sbfm x0, x1, #0, #7')
    def test_sbfm_sxtb_zero64(self):
        self.assertEqual(self.rf.read('X0'), 0x48)
        self.assertEqual(self.rf.read('W0'), 0x48)

    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x4142434445464788')
    @itest('sbfm x0, x1, #0, #7')
    def test_sbfm_sxtb_one64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffffffffff88)
        self.assertEqual(self.rf.read('W0'), 0xffffff88)

    # This is actually sxth.
    # Copy 15 - 0 + 1 bits from bit position 0 of the source register to the
    # least significant bits of the destination register.  Set bits above
    # the bitfield to the most significant bit of the bitfield and to zero
    # below the bitfield.
    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x4142434445464748')
    @itest('sbfm x0, x1, #0, #15')
    def test_sbfm_sxth_zero64(self):
        self.assertEqual(self.rf.read('X0'), 0x4748)
        self.assertEqual(self.rf.read('W0'), 0x4748)

    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x4142434445468748')
    @itest('sbfm x0, x1, #0, #15')
    def test_sbfm_sxth_one64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffffffff8748)
        self.assertEqual(self.rf.read('W0'), 0xffff8748)

    # This is actually sxtw.
    # Copy 31 - 0 + 1 bits from bit position 0 of the source register to the
    # least significant bits of the destination register.  Set bits above
    # the bitfield to the most significant bit of the bitfield and to zero
    # below the bitfield.
    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x4142434445464748')
    @itest('sbfm x0, x1, #0, #31')
    def test_sbfm_sxtw_zero(self):
        self.assertEqual(self.rf.read('X0'), 0x45464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x4142434485464748')
    @itest('sbfm x0, x1, #0, #31')
    def test_sbfm_sxtw_one(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffff85464748)
        self.assertEqual(self.rf.read('W0'), 0x85464748)


    # SBFX.

    # 32-bit.

    # Copy 1 bit from bit position 0 in the source register to the least
    # significant bits of the destination register.
    @itest_setregs('W1=0x44434241')
    @itest('sbfx w0, w1, #0, #1')
    def test_sbfx_min_min32(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    # Copy 32 bits from bit position 0 in the source register to the least
    # significant bits of the destination register.
    @itest_setregs('W1=0x41424344')
    @itest('sbfx w0, w1, #0, #32')
    def test_sbfx_min_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    # Copy 1 bit from bit position 31 in the source register to the least
    # significant bits of the destination register.
    @itest_setregs('W1=0x81424344')
    @itest('sbfx w0, w1, #31, #1')
    def test_sbfx_max_min32(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    # Copy 16 bits from bit position 16 in the source register to the least
    # significant bits of the destination register.
    @itest_setregs('W1=0xffff4344')
    @itest('sbfx w0, w1, #16, #16')
    def test_sbfx32(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    # 64-bit.

    # Copy 1 bit from bit position 0 in the source register to the least
    # significant bits of the destination register.
    @itest_setregs('X1=0x4847464544434241')
    @itest('sbfx x0, x1, #0, #1')
    def test_sbfx_min_min64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    # Copy 64 bits from bit position 0 in the source register to the least
    # significant bits of the destination register.
    @itest_setregs('X1=0x4142434445464748')
    @itest('sbfx x0, x1, #0, #64')
    def test_sbfx_min_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    # Copy 1 bit from bit position 63 in the source register to the least
    # significant bits of the destination register.
    @itest_setregs('X1=0x8142434445464748')
    @itest('sbfx x0, x1, #63, #1')
    def test_sbfx_max_min64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    # Copy 32 bits from bit position 32 in the source register to the least
    # significant bits of the destination register.
    @itest_setregs('X1=0xffffffff45464748')
    @itest('sbfx x0, x1, #32, #32')
    def test_sbfx64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffffffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)


    # STR (immediate).

    # str w1, [x27]          base register (opt. offset omitted):  [x27]     = w1
    # str w2, [x28, #8]      base plus offset:                     [x28 + 8] = w2
    # str w3, [x29], #8      post-indexed:                         [x29]     = w3, x29 += 8
    # str w4, [x30, #8]!     pre-indexed:                          [x30 + 8] = w4, x30 += 8

    # 32-bit.

    @itest_setregs('W1=0x41424344')
    @itest_custom('str w1, [sp]')
    def test_str_imm_base32(self):
        self.cpu.push_int(0x5152535455565758)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.cpu.read_int(stack), 0x5152535441424344)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_setregs('W1=0x41424344')
    @itest_custom('str w1, [sp, #8]')
    def test_str_imm_base_offset32(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.push_int(0x6162636465666768)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.cpu.read_int(stack + 8), 0x5152535441424344)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_setregs('W1=0x41424344')
    @itest_custom('str w1, [sp, #16380]')
    def test_str_imm_base_offset_max32(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK -= 16380
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.cpu.read_int(stack + 16380), 0x5152535441424344)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_setregs('W1=0x41424344')
    @itest_custom('str w1, [sp], #8')
    def test_str_imm_post_indexed32(self):
        self.cpu.push_int(0x5152535455565758)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.cpu.read_int(stack), 0x5152535441424344)
        self.assertEqual(self.rf.read('SP'), stack + 8)  # writeback

    @itest_setregs('W1=0x41424344')
    @itest_custom('str w1, [sp], #-256')
    def test_str_imm_post_indexed_neg32(self):
        self.cpu.push_int(0x5152535455565758)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.cpu.read_int(stack), 0x5152535441424344)
        self.assertEqual(self.rf.read('SP'), stack - 256)  # writeback

    @itest_setregs('W1=0x41424344')
    @itest_custom('str w1, [sp, #8]!')
    def test_str_imm_pre_indexed32(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.push_int(0x6162636465666768)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.cpu.read_int(stack + 8), 0x5152535441424344)
        self.assertEqual(self.rf.read('SP'), stack + 8)  # writeback

    @itest_setregs('W1=0x41424344')
    @itest_custom('str w1, [sp, #-256]!')
    def test_str_imm_pre_indexed_neg32(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 256
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.cpu.read_int(stack - 256), 0x5152535441424344)
        self.assertEqual(self.rf.read('SP'), stack - 256)  # writeback

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748')
    @itest_custom('str x1, [sp]')
    def test_str_imm_base64(self):
        self.cpu.push_int(0x5152535455565758)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.cpu.read_int(stack), 0x4142434445464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_setregs('X1=0x4142434445464748')
    @itest_custom('str x1, [sp, #8]')
    def test_str_imm_base_offset64(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.push_int(0x6162636465666768)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.cpu.read_int(stack + 8), 0x4142434445464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_setregs('X1=0x4142434445464748')
    @itest_custom('str x1, [sp, #32760]')
    def test_str_imm_base_offset_max64(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK -= 32760
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.cpu.read_int(stack + 32760), 0x4142434445464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_setregs('X1=0x4142434445464748')
    @itest_custom('str x1, [sp], #8')
    def test_str_imm_post_indexed64(self):
        self.cpu.push_int(0x5152535455565758)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.cpu.read_int(stack), 0x4142434445464748)
        self.assertEqual(self.rf.read('SP'), stack + 8)  # writeback

    @itest_setregs('X1=0x4142434445464748')
    @itest_custom('str x1, [sp], #-256')
    def test_str_imm_post_indexed_neg64(self):
        self.cpu.push_int(0x5152535455565758)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.cpu.read_int(stack), 0x4142434445464748)
        self.assertEqual(self.rf.read('SP'), stack - 256)  # writeback

    @itest_setregs('X1=0x4142434445464748')
    @itest_custom('str x1, [sp, #8]!')
    def test_str_imm_pre_indexed64(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.push_int(0x6162636465666768)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.cpu.read_int(stack + 8), 0x4142434445464748)
        self.assertEqual(self.rf.read('SP'), stack + 8)  # writeback

    @itest_setregs('X1=0x4142434445464748')
    @itest_custom('str x1, [sp, #-256]!')
    def test_str_imm_pre_indexed_neg64(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 256
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.cpu.read_int(stack - 256), 0x4142434445464748)
        self.assertEqual(self.rf.read('SP'), stack - 256)  # writeback


    # STR (register).

    # 32-bit.

    @itest_setregs('W0=0x41424344', 'W1=-8')
    @itest_custom('str w0, [sp, w1, uxtw]')
    def test_str_reg_uxtw32(self):
        self.cpu.push_int(0x5152535455565758)
        # Account for -8 (0xfffffff8) being treated like a large positive value
        # after zero extension to 64 bits.
        stack = self.cpu.STACK
        self.cpu.STACK -= 0xfffffff8
        self._execute()
        self.assertEqual(self.cpu.read_int(stack), 0x5152535441424344)

    @itest_setregs('W0=0x41424344', 'W1=-8')
    @itest_custom('str w0, [sp, w1, uxtw #2]')
    def test_str_reg_uxtw2_32(self):
        self.cpu.push_int(0x5152535455565758)
        # Account for -8 (0xfffffff8) being treated like a large positive value
        # after zero extension to 64 bits.
        stack = self.cpu.STACK
        self.cpu.STACK -= LSL(0xfffffff8, 2, 64)
        self._execute()
        self.assertEqual(self.cpu.read_int(stack), 0x5152535441424344)

    @itest_setregs('W0=0x41424344', 'X1=8')
    @itest_custom('str w0, [sp, x1]')
    def test_str_reg32(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.push_int(0x6162636465666768)
        self._execute()
        self.assertEqual(self.cpu.read_int(self.cpu.STACK + 8), 0x5152535441424344)

    @itest_setregs('W0=0x41424344', 'X1=2')
    @itest_custom('str w0, [sp, x1, lsl #2]')
    def test_str_reg_lsl32(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.push_int(0x6162636465666768)
        self._execute()
        self.assertEqual(self.cpu.read_int(self.cpu.STACK + 8), 0x5152535441424344)

    @itest_setregs('W0=0x41424344', 'W1=-8')
    @itest_custom('str w0, [sp, w1, sxtw]')
    def test_str_reg_sxtw32(self):
        self.cpu.push_int(0x5152535455565758)
        stack = self.cpu.STACK
        self.cpu.STACK += 8
        self._execute()
        self.assertEqual(self.cpu.read_int(stack), 0x5152535441424344)

    @itest_setregs('W0=0x41424344', 'W1=-8')
    @itest_custom('str w0, [sp, w1, sxtw #2]')
    def test_str_reg_sxtw2_32(self):
        self.cpu.push_int(0x5152535455565758)
        stack = self.cpu.STACK
        self.cpu.STACK += LSL(8, 2, 32)
        self._execute()
        self.assertEqual(self.cpu.read_int(stack), 0x5152535441424344)

    @itest_setregs('W0=0x41424344', 'X1=-8')
    @itest_custom('str w0, [sp, x1, sxtx]')
    def test_str_reg_sxtx32(self):
        self.cpu.push_int(0x5152535455565758)
        stack = self.cpu.STACK
        self.cpu.STACK += 8
        self._execute()
        self.assertEqual(self.cpu.read_int(stack), 0x5152535441424344)

    @itest_setregs('W0=0x41424344', 'X1=-2')
    @itest_custom('str w0, [sp, x1, sxtx #2]')
    def test_str_reg_sxtx2_32(self):
        self.cpu.push_int(0x5152535455565758)
        stack = self.cpu.STACK
        self.cpu.STACK += 8
        self._execute()
        self.assertEqual(self.cpu.read_int(stack), 0x5152535441424344)

    # 64-bit.

    @itest_setregs('X0=0x4142434445464748', 'W1=-8')
    @itest_custom('str x0, [sp, w1, uxtw]')
    def test_str_reg_uxtw64(self):
        self.cpu.push_int(0x5152535455565758)
        # Account for -8 (0xfffffff8) being treated like a large positive value
        # after zero extension to 64 bits.
        stack = self.cpu.STACK
        self.cpu.STACK -= 0xfffffff8
        self._execute()
        self.assertEqual(self.cpu.read_int(stack), 0x4142434445464748)

    @itest_setregs('X0=0x4142434445464748', 'W1=-8')
    @itest_custom('str x0, [sp, w1, uxtw #3]')
    def test_str_reg_uxtw3_64(self):
        self.cpu.push_int(0x5152535455565758)
        # Account for -8 (0xfffffff8) being treated like a large positive value
        # after zero extension to 64 bits.
        stack = self.cpu.STACK
        self.cpu.STACK -= LSL(0xfffffff8, 3, 64)
        self._execute()
        self.assertEqual(self.cpu.read_int(stack), 0x4142434445464748)

    @itest_setregs('X0=0x4142434445464748', 'X1=8')
    @itest_custom('str x0, [sp, x1]')
    def test_str_reg64(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.push_int(0x6162636465666768)
        self._execute()
        self.assertEqual(self.cpu.read_int(self.cpu.STACK + 8), 0x4142434445464748)

    @itest_setregs('X0=0x4142434445464748', 'X1=2')
    @itest_custom('str x0, [sp, x1, lsl #3]')
    def test_str_reg_lsl64(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.push_int(0x6162636465666768)
        self.cpu.push_int(0x7172737475767778)
        self._execute()
        self.assertEqual(self.cpu.read_int(self.cpu.STACK + 16), 0x4142434445464748)

    @itest_setregs('X0=0x4142434445464748', 'W1=-8')
    @itest_custom('str x0, [sp, w1, sxtw]')
    def test_str_reg_sxtw64(self):
        self.cpu.push_int(0x5152535455565758)
        stack = self.cpu.STACK
        self.cpu.STACK += 8
        self._execute()
        self.assertEqual(self.cpu.read_int(stack), 0x4142434445464748)

    @itest_setregs('X0=0x4142434445464748', 'W1=-8')
    @itest_custom('str x0, [sp, w1, sxtw #3]')
    def test_str_reg_sxtw3_64(self):
        self.cpu.push_int(0x5152535455565758)
        stack = self.cpu.STACK
        self.cpu.STACK += LSL(8, 3, 32)
        self._execute()
        self.assertEqual(self.cpu.read_int(stack), 0x4142434445464748)

    @itest_setregs('X0=0x4142434445464748', 'X1=-8')
    @itest_custom('str x0, [sp, x1, sxtx]')
    def test_str_reg_sxtx64(self):
        self.cpu.push_int(0x5152535455565758)
        stack = self.cpu.STACK
        self.cpu.STACK += 8
        self._execute()
        self.assertEqual(self.cpu.read_int(stack), 0x4142434445464748)

    @itest_setregs('X0=0x4142434445464748', 'X1=-2')
    @itest_custom('str x0, [sp, x1, sxtx #3]')
    def test_str_reg_sxtx3_64(self):
        self.cpu.push_int(0x5152535455565758)
        stack = self.cpu.STACK
        self.cpu.STACK += 16
        self._execute()
        self.assertEqual(self.cpu.read_int(stack), 0x4142434445464748)


    # STUR.

    # 32-bit.

    @itest_setregs('W1=0x41424344')
    @itest_custom('stur w1, [sp, #-256]')
    def test_stur_min32(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 256
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.cpu.read_int(stack - 256), 0x5152535441424344)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_setregs('W1=0x41424344')
    @itest_custom('stur w1, [sp, #255]')
    def test_stur_max32(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK -= 255
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.cpu.read_int(stack + 255), 0x5152535441424344)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_setregs('W1=0x41424344')
    @itest_custom('stur w1, [sp, #1]')
    def test_stur_one32(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.push_int(0x6162636465666768)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.cpu.read_int(stack + 1), 0x5861626341424344)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_setregs('W1=0x41424344')
    @itest_custom('stur w1, [sp]')
    def test_stur32(self):
        self.cpu.push_int(0x5152535455565758)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.cpu.read_int(stack), 0x5152535441424344)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    # 64-bit.

    @itest_setregs('X1=0x4142434445464748')
    @itest_custom('stur x1, [sp, #-256]')
    def test_stur_min64(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK += 256
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.cpu.read_int(stack - 256), 0x4142434445464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_setregs('X1=0x4142434445464748')
    @itest_custom('stur x1, [sp, #255]')
    def test_stur_max64(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.STACK -= 255
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.cpu.read_int(stack + 255), 0x4142434445464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_setregs('X1=0x4142434445464748')
    @itest_custom('stur x1, [sp, #1]')
    def test_stur_one64(self):
        self.cpu.push_int(0x5152535455565758)
        self.cpu.push_int(0x6162636465666768)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.cpu.read_int(stack + 1), 0x4142434445464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    @itest_setregs('X1=0x4142434445464748')
    @itest_custom('stur x1, [sp]')
    def test_stur64(self):
        self.cpu.push_int(0x5152535455565758)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.cpu.read_int(stack), 0x4142434445464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback


    # SVC.

    def test_svc0(self):
        with self.assertRaises(Interruption):
            self._setupCpu("svc #0")
            self._execute()

    def test_svc1(self):
        # XXX: Maybe change the behavior to be consistent with Unicorn?
        if self.__class__.__name__ == 'Aarch64CpuInstructions':
            e = InstructionNotImplementedError
        elif self.__class__.__name__ == 'Aarch64UnicornInstructions':
            e = Interruption
        else:
            self.fail()

        with self.assertRaises(e):
            self._setupCpu("svc #1")
            self._execute()


    # TBNZ.

    # 32-bit.

    # Execute sequentially.
    @itest_custom(['tbnz w0, 0, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_tbnz_min_zero32(self):
        self.cpu.W0 = 0
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 4)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 42)
        self.assertEqual(self.rf.read('X2'), 0)

    # Jump over the second instruction.
    @itest_custom(['tbnz w0, 0, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_tbnz_min_one32(self):
        self.cpu.W0 = 1
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 8)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0)
        self.assertEqual(self.rf.read('X2'), 43)

    # Execute sequentially.
    @itest_custom(['tbnz w0, 31, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_tbnz_max_zero32(self):
        self.cpu.W0 = 0
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 4)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 42)
        self.assertEqual(self.rf.read('X2'), 0)

    # Jump over the second instruction.
    @itest_custom(['tbnz w0, 31, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_tbnz_max_one32(self):
        self.cpu.W0 = 0x80000000
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 8)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0)
        self.assertEqual(self.rf.read('X2'), 43)

    # Execute sequentially.
    @itest_custom(['tbnz w0, 3, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_tbnz_zero32(self):
        self.cpu.W0 = 0
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 4)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 42)
        self.assertEqual(self.rf.read('X2'), 0)

    # Jump over the second instruction.
    @itest_custom(['tbnz w0, 3, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_tbnz_one32(self):
        self.cpu.W0 = 8
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 8)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0)
        self.assertEqual(self.rf.read('X2'), 43)

    # 64-bit.

    # Execute sequentially.
    @itest_custom(['tbnz x0, 0, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_tbnz_min_zero64(self):
        self.cpu.X0 = 0
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 4)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 42)
        self.assertEqual(self.rf.read('X2'), 0)

    # Jump over the second instruction.
    @itest_custom(['tbnz x0, 0, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_tbnz_min_one64(self):
        self.cpu.X0 = 1
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 8)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0)
        self.assertEqual(self.rf.read('X2'), 43)

    # Execute sequentially.
    @itest_custom(['tbnz x0, 63, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_tbnz_max_zero64(self):
        self.cpu.X0 = 0
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 4)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 42)
        self.assertEqual(self.rf.read('X2'), 0)

    # Jump over the second instruction.
    @itest_custom(['tbnz x0, 63, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_tbnz_max_one64(self):
        self.cpu.X0 = 0x8000000000000000
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 8)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0)
        self.assertEqual(self.rf.read('X2'), 43)

    # Execute sequentially.
    @itest_custom(['tbnz x0, 3, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_tbnz_zero64(self):
        self.cpu.X0 = 0
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 4)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 42)
        self.assertEqual(self.rf.read('X2'), 0)

    # Jump over the second instruction.
    @itest_custom(['tbnz x0, 3, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_tbnz_one64(self):
        self.cpu.X0 = 8
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 8)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0)
        self.assertEqual(self.rf.read('X2'), 43)


    # TBZ.

    # 32-bit.

    # Jump over the second instruction.
    @itest_custom(['tbz w0, 0, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_tbz_min_zero32(self):
        self.cpu.W0 = 0
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 8)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0)
        self.assertEqual(self.rf.read('X2'), 43)

    # Execute sequentially.
    @itest_custom(['tbz w0, 0, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_tbz_min_one32(self):
        self.cpu.W0 = 1
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 4)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 42)
        self.assertEqual(self.rf.read('X2'), 0)

    # Jump over the second instruction.
    @itest_custom(['tbz w0, 31, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_tbz_max_zero32(self):
        self.cpu.W0 = 0
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 8)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0)
        self.assertEqual(self.rf.read('X2'), 43)

    # Execute sequentially.
    @itest_custom(['tbz w0, 31, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_tbz_max_one32(self):
        self.cpu.W0 = 0x80000000
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 4)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 42)
        self.assertEqual(self.rf.read('X2'), 0)

    # Jump over the second instruction.
    @itest_custom(['tbz w0, 3, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_tbz_zero32(self):
        self.cpu.W0 = 0
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 8)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0)
        self.assertEqual(self.rf.read('X2'), 43)

    # Execute sequentially.
    @itest_custom(['tbz w0, 3, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_tbz_one32(self):
        self.cpu.W0 = 8
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 4)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 42)
        self.assertEqual(self.rf.read('X2'), 0)

    # 64-bit.

    # Jump over the second instruction.
    @itest_custom(['tbz x0, 0, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_tbz_min_zero64(self):
        self.cpu.X0 = 0
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 8)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0)
        self.assertEqual(self.rf.read('X2'), 43)

    # Execute sequentially.
    @itest_custom(['tbz x0, 0, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_tbz_min_one64(self):
        self.cpu.X0 = 1
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 4)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 42)
        self.assertEqual(self.rf.read('X2'), 0)

    # Jump over the second instruction.
    @itest_custom(['tbz x0, 63, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_tbz_max_zero64(self):
        self.cpu.X0 = 0
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 8)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0)
        self.assertEqual(self.rf.read('X2'), 43)

    # Execute sequentially.
    @itest_custom(['tbz x0, 63, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_tbz_max_one64(self):
        self.cpu.X0 = 0x8000000000000000
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 4)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 42)
        self.assertEqual(self.rf.read('X2'), 0)

    # Jump over the second instruction.
    @itest_custom(['tbz x0, 3, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_tbz_zero64(self):
        self.cpu.X0 = 0
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 8)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0)
        self.assertEqual(self.rf.read('X2'), 43)

    # Execute sequentially.
    @itest_custom(['tbz x0, 3, .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_tbz_one64(self):
        self.cpu.X0 = 8
        pc = self.cpu.PC
        self._execute(check_pc=False)
        self.assertEqual(self.rf.read('PC'), pc + 4)
        self.assertEqual(self.rf.read('LR'), 0)
        self.assertEqual(self.rf.read('X30'), 0)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 42)
        self.assertEqual(self.rf.read('X2'), 0)


    # TST (immediate).

    # 32-bit.

    @itest_setregs('W1=0x41424344')
    @itest('tst w1, #0xffff')
    def test_tst_imm32(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x81424344')
    @itest('tst w1, #0xffff0000')
    def test_tst_imm2_32(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x44434241')
    @itest('tst w1, #1')
    def test_tst_imm3_32(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0')
    @itest('tst w1, #1')
    def test_tst_imm4_32(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x40000000)

    # 64-bit.

    @itest_setregs('X1=0x8142434445464748')
    @itest('tst x1, #0xffff0000ffff0000')
    def test_tst_imm64(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0x4142434445464748')
    @itest('tst x1, #0x0000ffff0000ffff')
    def test_tst_imm2_64(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x4847464544434241')
    @itest('tst x1, #1')
    def test_tst_imm3_64(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0')
    @itest('tst x1, #1')
    def test_tst_imm4_64(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x40000000)


    # TST (shifted register).

    # 32-bit.

    @itest_setregs('W1=0x4142ffff', 'W2=0xffff4344')
    @itest('tst w1, w2')
    def test_tst_sft_reg32(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0xffffffff', 'W2=0')
    @itest('tst w1, w2')
    def test_tst_sft_reg_zero32(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x40000000)

    @itest_setregs('W1=0x4142ffff', 'W2=0xffff4344')
    @itest('tst w1, w2, lsl #0')
    def test_tst_sft_reg_lsl_min32(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0xffffffff', 'W2=0x80000001')
    @itest('tst w1, w2, lsl #31')
    def test_tst_sft_reg_lsl_max32(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0xffffffff', 'W2=0x81424344')
    @itest('tst w1, w2, lsl #4')
    def test_tst_sft_reg_lsl32(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x4142ffff', 'W2=0xffff4344')
    @itest('tst w1, w2, lsr #0')
    def test_tst_sft_reg_lsr_min32(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0xffffffff', 'W2=0x80000001')
    @itest('tst w1, w2, lsr #31')
    def test_tst_sft_reg_lsr_max32(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0xffffffff', 'W2=0x81424344')
    @itest('tst w1, w2, lsr #4')
    def test_tst_sft_reg_lsr32(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0x4142ffff', 'W2=0xffff4344')
    @itest('tst w1, w2, asr #0')
    def test_tst_sft_reg_asr_min32(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0xffffffff', 'W2=0x80000001')
    @itest('tst w1, w2, asr #31')
    def test_tst_sft_reg_asr_max32(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0xffffffff', 'W2=0x81424344')
    @itest('tst w1, w2, asr #4')
    def test_tst_sft_reg_asr32(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('W1=0x4142ffff', 'W2=0xffff4344')
    @itest('tst w1, w2, ror #0')
    def test_tst_sft_reg_ror_min32(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0xffffffff', 'W2=0x80000001')
    @itest('tst w1, w2, ror #31')
    def test_tst_sft_reg_ror_max32(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('W1=0xffffffff', 'W2=0x81424344')
    @itest('tst w1, w2, ror #4')
    def test_tst_sft_reg_ror32(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    # 64-bit.

    @itest_setregs('X1=0x41424344ffffffff', 'X2=0xffffffff45464748')
    @itest('tst x1, x2')
    def test_tst_sft_reg64(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0')
    @itest('tst x1, x2')
    def test_tst_sft_reg_zero64(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x40000000)

    @itest_setregs('X1=0x41424344ffffffff', 'X2=0xffffffff45464748')
    @itest('tst x1, x2, lsl #0')
    def test_tst_sft_reg_lsl_min64(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8000000000000001')
    @itest('tst x1, x2, lsl #63')
    def test_tst_sft_reg_lsl_max64(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8142434445464748')
    @itest('tst x1, x2, lsl #4')
    def test_tst_sft_reg_lsl64(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x41424344ffffffff', 'X2=0xffffffff45464748')
    @itest('tst x1, x2, lsr #0')
    def test_tst_sft_reg_lsr_min64(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8000000000000001')
    @itest('tst x1, x2, lsr #63')
    def test_tst_sft_reg_lsr_max64(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8142434445464748')
    @itest('tst x1, x2, lsr #4')
    def test_tst_sft_reg_lsr64(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0x41424344ffffffff', 'X2=0xffffffff45464748')
    @itest('tst x1, x2, asr #0')
    def test_tst_sft_reg_asr_min64(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8000000000000001')
    @itest('tst x1, x2, asr #63')
    def test_tst_sft_reg_asr_max64(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8142434445464748')
    @itest('tst x1, x2, asr #4')
    def test_tst_sft_reg_asr64(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)

    @itest_setregs('X1=0x41424344ffffffff', 'X2=0xffffffff45464748')
    @itest('tst x1, x2, ror #0')
    def test_tst_sft_reg_ror_min64(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8000000000000001')
    @itest('tst x1, x2, ror #63')
    def test_tst_sft_reg_ror_max64(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0x8142434445464748')
    @itest('tst x1, x2, ror #4')
    def test_tst_sft_reg_ror64(self):
        self.assertEqual(self.rf.read('XZR'), 0)
        self.assertEqual(self.rf.read('WZR'), 0)
        self.assertEqual(self.rf.read('NZCV'), 0x80000000)


    # UBFIZ.

    # 32-bit.

    # Copy 1 bit from the least significant bits of the source register to bit
    # position 0 of the destination register.
    @itest_setregs('W1=0x44434241')
    @itest('ubfiz w0, w1, #0, #1')
    def test_ubfiz_min_min32(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)

    # Copy 32 bits from the least significant bits of the source register to bit
    # position 0 of the destination register.
    @itest_setregs('W1=0x41424344')
    @itest('ubfiz w0, w1, #0, #32')
    def test_ubfiz_min_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    # Copy 1 bit from the least significant bits of the source register to bit
    # position 31 of the destination register.
    @itest_setregs('W1=0x44434241')
    @itest('ubfiz w0, w1, #31, #1')
    def test_ubfiz_max_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x80000000)
        self.assertEqual(self.rf.read('W0'), 0x80000000)

    # Copy 15 bits from the least significant bits of the source register to bit
    # position 17 of the destination register.
    @itest_setregs('W1=0x41427fff')
    @itest('ubfiz w0, w1, #17, #15')
    def test_ubfiz32(self):
        self.assertEqual(self.rf.read('X0'), 0xfffe0000)
        self.assertEqual(self.rf.read('W0'), 0xfffe0000)

    # 64-bit.

    # Copy 1 bit from the least significant bits of the source register to bit
    # position 0 of the destination register.
    @itest_setregs('X1=0x4847464544434241')
    @itest('ubfiz x0, x1, #0, #1')
    def test_ubfiz_min_min64(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)

    # Copy 64 bits from the least significant bits of the source register to bit
    # position 0 of the destination register.
    @itest_setregs('X1=0x4142434445464748')
    @itest('ubfiz x0, x1, #0, #64')
    def test_ubfiz_min_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    # Copy 1 bit from the least significant bits of the source register to bit
    # position 63 of the destination register.
    @itest_setregs('X1=0x4847464544434241')
    @itest('ubfiz x0, x1, #63, #1')
    def test_ubfiz_max_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x8000000000000000)
        self.assertEqual(self.rf.read('W0'), 0)

    # Copy 31 bit from the least significant bits of the source register to bit
    # position 33 of the destination register.
    @itest_setregs('X1=0x414243447fffffff')
    @itest('ubfiz x0, x1, #33, #31')
    def test_ubfiz64(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffe00000000)
        self.assertEqual(self.rf.read('W0'), 0)


    # UBFM.

    # 32-bit.

    # This is actually ubfx.
    # Copy 5 - 3 + 1 bits from bit position 3 of the source register to the
    # least significant bits of the destination register.  Set bits below and
    # above the bitfield to zero.
    @itest_setregs('W0=0xffffffff', 'W1=0x41424328')
    @itest('ubfm w0, w1, #3, #5')
    def test_ubfm_ge32(self):
        self.assertEqual(self.rf.read('X0'), 5)
        self.assertEqual(self.rf.read('W0'), 5)

    # This is actually ubfiz.
    # Copy 3 + 1 bits from the least significant bits of the source register to
    # bit position 32 - 5 of the destination register.  Set bits below and
    # above the bitfield to zero.
    @itest_setregs('W0=0xffffffff', 'W1=0x41424349')
    @itest('ubfm w0, w1, #5, #3')
    def test_ubfm_lt32(self):
        self.assertEqual(self.rf.read('X0'), 0x48000000)
        self.assertEqual(self.rf.read('W0'), 0x48000000)

    # This is actually lsr.
    # Copy 31 - 0 + 1 bits from bit position 0 of the source register to the
    # least significant bits of the destination register.  Set bits below and
    # above the bitfield to zero.
    @itest_setregs('W0=0xffffffff', 'W1=0x41424344')
    @itest('ubfm w0, w1, #0, #31')
    def test_ubfm_ge_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    # This is actually ubfiz.
    # Copy 0 + 1 bits from the least significant bits of the source register to
    # bit position 32 - 31 of the destination register.  Set bits below and
    # above the bitfield to zero.
    @itest_setregs('W0=0xffffffff','W1=0x44434241')
    @itest('ubfm w0, w1, #31, #0')
    def test_ubfm_lt_max32(self):
        self.assertEqual(self.rf.read('X0'), 2)
        self.assertEqual(self.rf.read('W0'), 2)

    # This is actually ubfx.
    # Copy 0 - 0 + 1 bits from bit position 0 of the source register to the
    # least significant bits of the destination register.  Set bits below and
    # above the bitfield to zero.
    @itest_setregs('W0=0xffffffff', 'W1=0x44434241')
    @itest('ubfm w0, w1, #0, #0')
    def test_ubfm_ge_min32(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)

    # This is actually lsl.
    # Copy 0 + 1 bits from the least significant bits of the source register to
    # bit position 32 - 1 of the destination register.  Set bits below and
    # above the bitfield to zero.
    @itest_setregs('W0=0xffffffff', 'W1=0x44434241')
    @itest('ubfm w0, w1, #1, #0')
    def test_ubfm_lt_min32(self):
        self.assertEqual(self.rf.read('X0'), 0x80000000)
        self.assertEqual(self.rf.read('W0'), 0x80000000)

    # This is actually uxtb.
    # Copy 7 - 0 + 1 bits from bit position 0 of the source register to the
    # least significant bits of the destination register.  Set bits below and
    # above the bitfield to zero.
    @itest_setregs('W0=0xffffffff', 'W1=0x41424344')
    @itest('ubfm w0, w1, #0, #7')
    def test_ubfm_uxtb(self):
        self.assertEqual(self.rf.read('X0'), 0x44)
        self.assertEqual(self.rf.read('W0'), 0x44)

    # This is actually uxth.
    # Copy 15 - 0 + 1 bits from bit position 0 of the source register to the
    # least significant bits of the destination register.  Set bits below and
    # above the bitfield to zero.
    @itest_setregs('W0=0xffffffff', 'W1=0x41424344')
    @itest('ubfm w0, w1, #0, #15')
    def test_ubfm_uxth(self):
        self.assertEqual(self.rf.read('X0'), 0x4344)
        self.assertEqual(self.rf.read('W0'), 0x4344)

    # 64-bit.

    # This is actually ubfx.
    # Copy 5 - 3 + 1 bits from bit position 3 of the source register to the
    # least significant bits of the destination register.  Set bits below and
    # above the bitfield to zero.
    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x4142434445464728')
    @itest('ubfm x0, x1, #3, #5')
    def test_ubfm_ge64(self):
        self.assertEqual(self.rf.read('X0'), 5)
        self.assertEqual(self.rf.read('W0'), 5)

    # This is actually ubfiz.
    # Copy 3 + 1 bits from the least significant bits of the source register to
    # bit position 64 - 5 of the destination register.  Set bits below and
    # above the bitfield to zero.
    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x4142434445464749')
    @itest('ubfm x0, x1, #5, #3')
    def test_ubfm_lt64(self):
        self.assertEqual(self.rf.read('X0'), 0x4800000000000000)
        self.assertEqual(self.rf.read('W0'), 0)

    # This is actually lsr.
    # Copy 63 - 0 + 1 bits from bit position 0 of the source register to the
    # least significant bits of the destination register.  Set bits below and
    # above the bitfield to zero.
    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x4142434445464748')
    @itest('ubfm x0, x1, #0, #63')
    def test_ubfm_ge_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    # This is actually ubfiz.
    # Copy 0 + 1 bits from the least significant bits of the source register to
    # bit position 64 - 63 of the destination register.  Set bits below and
    # above the bitfield to zero.
    @itest_setregs('X0=0xffffffffffffffff','X1=0x4847464544434241')
    @itest('ubfm x0, x1, #63, #0')
    def test_ubfm_lt_max64(self):
        self.assertEqual(self.rf.read('X0'), 2)
        self.assertEqual(self.rf.read('W0'), 2)

    # This is actually ubfx.
    # Copy 0 - 0 + 1 bits from bit position 0 of the source register to the
    # least significant bits of the destination register.  Set bits below and
    # above the bitfield to zero.
    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x4847464544434241')
    @itest('ubfm x0, x1, #0, #0')
    def test_ubfm_ge_min64(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)

    # This is actually lsl.
    # Copy 0 + 1 bits from the least significant bits of the source register to
    # bit position 64 - 1 of the destination register.  Set bits below and
    # above the bitfield to zero.
    @itest_setregs('X0=0xffffffffffffffff', 'X1=0x4847464544434241')
    @itest('ubfm x0, x1, #1, #0')
    def test_ubfm_lt_min64(self):
        self.assertEqual(self.rf.read('X0'), 0x8000000000000000)
        self.assertEqual(self.rf.read('W0'), 0)


    # UBFX.

    # 32-bit.

    # Copy 1 bit from bit position 0 in the source register to the least
    # significant bits of the destination register.
    @itest_setregs('W1=0x44434241')
    @itest('ubfx w0, w1, #0, #1')
    def test_ubfx_min_min32(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)

    # Copy 32 bits from bit position 0 in the source register to the least
    # significant bits of the destination register.
    @itest_setregs('W1=0x41424344')
    @itest('ubfx w0, w1, #0, #32')
    def test_ubfx_min_max32(self):
        self.assertEqual(self.rf.read('X0'), 0x41424344)
        self.assertEqual(self.rf.read('W0'), 0x41424344)

    # Copy 1 bit from bit position 31 in the source register to the least
    # significant bits of the destination register.
    @itest_setregs('W1=0x81424344')
    @itest('ubfx w0, w1, #31, #1')
    def test_ubfx_max_min32(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)

    # Copy 16 bits from bit position 16 in the source register to the least
    # significant bits of the destination register.
    @itest_setregs('W1=0xffff4344')
    @itest('ubfx w0, w1, #16, #16')
    def test_ubfx32(self):
        self.assertEqual(self.rf.read('X0'), 0xffff)
        self.assertEqual(self.rf.read('W0'), 0xffff)

    # 64-bit.

    # Copy 1 bit from bit position 0 in the source register to the least
    # significant bits of the destination register.
    @itest_setregs('X1=0x4847464544434241')
    @itest('ubfx x0, x1, #0, #1')
    def test_ubfx_min_min64(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)

    # Copy 64 bits from bit position 0 in the source register to the least
    # significant bits of the destination register.
    @itest_setregs('X1=0x4142434445464748')
    @itest('ubfx x0, x1, #0, #64')
    def test_ubfx_min_max64(self):
        self.assertEqual(self.rf.read('X0'), 0x4142434445464748)
        self.assertEqual(self.rf.read('W0'), 0x45464748)

    # Copy 1 bit from bit position 63 in the source register to the least
    # significant bits of the destination register.
    @itest_setregs('X1=0x8142434445464748')
    @itest('ubfx x0, x1, #63, #1')
    def test_ubfx_max_min64(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)

    # Copy 32 bits from bit position 32 in the source register to the least
    # significant bits of the destination register.
    @itest_setregs('X1=0xffffffff45464748')
    @itest('ubfx x0, x1, #32, #32')
    def test_ubfx64(self):
        self.assertEqual(self.rf.read('X0'), 0xffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)


    # UDIV.

    # 32-bit.

    @itest_setregs('W1=0', 'W2=0')
    @itest('udiv w0, w1, w2')
    def test_udiv_min32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('W1=0xffffffff', 'W2=0xffffffff')
    @itest('udiv w0, w1, w2')
    def test_udiv_max32(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)

    @itest_setregs('W1=0xffffffff', 'W2=0')
    @itest('udiv w0, w1, w2')
    def test_udiv0_32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('W1=0xffffffff', 'W2=2')
    @itest('udiv w0, w1, w2')
    def test_udiv_neg32(self):
        self.assertEqual(self.rf.read('X0'), 0x7fffffff)
        self.assertEqual(self.rf.read('W0'), 0x7fffffff)

    @itest_setregs('W1=1', 'W2=2')
    @itest('udiv w0, w1, w2')
    def test_udiv_pos32(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    # 64-bit.

    @itest_setregs('X1=0', 'X2=0')
    @itest('udiv x0, x1, x2')
    def test_udiv_min64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0xffffffffffffffff')
    @itest('udiv x0, x1, x2')
    def test_udiv_max64(self):
        self.assertEqual(self.rf.read('X0'), 1)
        self.assertEqual(self.rf.read('W0'), 1)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0')
    @itest('udiv x0, x1, x2')
    def test_udiv0_64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=2')
    @itest('udiv x0, x1, x2')
    def test_udiv_neg64(self):
        self.assertEqual(self.rf.read('X0'), 0x7fffffffffffffff)
        self.assertEqual(self.rf.read('W0'), 0xffffffff)

    @itest_setregs('X1=1', 'X2=2')
    @itest('udiv x0, x1, x2')
    def test_udiv_pos64(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)


    # UMULH.

    @itest_setregs('X1=0', 'X2=0')
    @itest('umulh x0, x1, x2')
    def test_umulh_min(self):
        self.assertEqual(self.rf.read('X0'), 0)
        self.assertEqual(self.rf.read('W0'), 0)

    @itest_setregs('X1=0xffffffffffffffff', 'X2=0xffffffffffffffff')
    @itest('umulh x0, x1, x2')
    def test_umulh_max(self):
        self.assertEqual(self.rf.read('X0'), 0xfffffffffffffffe)
        self.assertEqual(self.rf.read('W0'), 0xfffffffe)

    @itest_setregs('X1=0x4142434445464748', 'X2=0x4142434445464748')
    @itest('umulh x0, x1, x2')
    def test_umulh(self):
        self.assertEqual(self.rf.read('X0'), 0x10a2b74f6c0e36e6)
        self.assertEqual(self.rf.read('W0'), 0x6c0e36e6)


    # UXTB.

    @itest_setregs('W1=0x41424381')
    @itest('uxtb w0, w1')
    def test_uxtb(self):
        self.assertEqual(self.rf.read('X0'), 0x81)
        self.assertEqual(self.rf.read('W0'), 0x81)


    # UXTH.

    @itest_setregs('W1=0x41428561')
    @itest('uxth w0, w1')
    def test_uxth(self):
        self.assertEqual(self.rf.read('X0'), 0x8561)
        self.assertEqual(self.rf.read('W0'), 0x8561)


class Aarch64CpuInstructions(unittest.TestCase, Aarch64Instructions):
    def setUp(self):
        # XXX: Adapted from the Armv7 test code.
        cs = ConstraintSet()
        self.cpu = Cpu(SMemory64(cs))
        self.mem = self.cpu.memory
        self.rf = self.cpu.regfile

    def _execute(self, check_pc=True):
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
        self.emu = UnicornEmulator(self.cpu)
        # Make sure that 'self._emu' is set.
        self.emu.reset()
        # XXX: Map the data region as well?
        # Map the stack.
        self.emu._create_emulated_mapping(self.emu._emu, self.cpu.STACK)

    def _execute(self, check_pc=True):
        # XXX: Based on the Armv7 test code.
        pc = self.cpu.PC
        self.cpu.decode_instruction(pc)
        self.emu.emulate(self.cpu.instruction)
        if check_pc:
            self.assertEqual(self.cpu.PC, pc + 4)
