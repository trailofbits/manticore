import unittest

from capstone import CS_MODE_ARM
from functools import wraps
from keystone import Ks, KS_ARCH_ARM64, KS_MODE_LITTLE_ENDIAN
from nose.tools import nottest

from manticore.core.smtlib import ConstraintSet, solver
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
