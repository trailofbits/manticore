import unittest

from capstone import CS_MODE_ARM
from functools import wraps
from keystone import Ks, KS_ARCH_ARM64, KS_MODE_LITTLE_ENDIAN

from manticore.core.smtlib import *
from manticore.native.memory import SMemory64, Memory64
from manticore.native.cpu.aarch64 import Aarch64Cpu as Cpu
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


    # B.

    # Jump over the second instruction.  Specify 'count', so it doesn't attempt
    # to execute beyond valid code.
    @itest_multiple(['b .+8', 'mov x1, 42', 'mov x2, 43'], count=2)
    def test_b_pos(self):
        self.assertEqual(self.rf.read('X1'), 0)
        self.assertEqual(self.rf.read('X2'), 43)

    # Jump two instructions back.
    @itest_custom(['mov x1, 42', 'mov x2, 43', 'b .-8'], multiple_insts=True)
    def test_b_neg(self):
        self.cpu.PC += 8  # start at 'b'
        # Execute just two instructions, so it doesn't loop indefinitely.
        self._execute()
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


    # BL.

    # Jump over the second instruction.
    @itest_custom(['bl .+8', 'mov x1, 42', 'mov x2, 43'], multiple_insts=True)
    def test_bl_pos(self):
        pc = self.cpu.PC
        # Execute just two instructions, so it doesn't attempt to run beyond
        # valid code.
        self._execute()
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
        self._execute()
        self.assertEqual(self.rf.read('PC'), pc - 8)
        self.assertEqual(self.rf.read('LR'), pc + 4)
        self.assertEqual(self.rf.read('X30'), pc + 4)
        self._execute()
        self.assertEqual(self.rf.read('X1'), 42)
        self.assertEqual(self.rf.read('X2'), 0)


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
    def test_ldr_reg_sxtx_64(self):
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


    # XXX: Unimplemented.

    # This is actually ldur since a positive offset must be a multiple of 4 for
    # the 32-bit variant of ldr (immediate).
    @itest_custom('ldr w1, [sp, #1]')
    def test_ldur32(self):
        self.cpu.push_int(0x4142434445464748)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x44454647)
        self.assertEqual(self.rf.read('W1'), 0x44454647)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    # This is actually ldur since negative offsets are not allowed with ldr
    # (immediate).
    @itest_custom('ldr w1, [sp, #-256]')
    def test_ldur_neg32(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK += 256
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x45464748)
        self.assertEqual(self.rf.read('W1'), 0x45464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    # This is actually ldur since a positive offset must be a multiple of 8 for
    # the 64-bit variant of ldr (immediate).
    @itest_custom('ldr x1, [sp, #4]')
    def test_ldur64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.push_int(0x5152535455565758)
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4546474851525354)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

    # This is actually ldur since negative offsets are not allowed with ldr
    # (immediate).
    @itest_custom('ldr x1, [sp, #-256]')
    def test_ldur_neg64(self):
        self.cpu.push_int(0x4142434445464748)
        self.cpu.STACK += 256
        stack = self.cpu.STACK
        self._execute()
        self.assertEqual(self.rf.read('X1'), 0x4142434445464748)
        self.assertEqual(self.rf.read('SP'), stack)  # no writeback

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

    def _setupCpu(self, asm, mode=CS_MODE_ARM, multiple_insts=False):
        super()._setupCpu(asm, mode, multiple_insts)
        self.emu = UnicornEmulator(self.cpu)
        # Make sure that 'self._emu' is set.
        self.emu.reset()
        # XXX: Map the data region as well?
        # Map the stack.
        self.emu._create_emulated_mapping(self.emu._emu, self.cpu.STACK)

    def _execute(self):
        # XXX: Based on the Armv7 test code.
        self.cpu.decode_instruction(self.cpu.PC)
        self.emu.emulate(self.cpu.instruction)
