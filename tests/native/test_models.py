import unittest
import os
import random
import tempfile
from glob import glob
import re

from manticore.core.smtlib import (
    ConstraintSet,
    Operators,
    Z3Solver,
    issymbolic,
    ArraySelect,
    BitVecITE,
)
from manticore.native.state import State
from manticore.platforms import linux
from manticore.native import Manticore
from manticore.native.models import (
    variadic,
    isvariadic,
    strcmp,
    strlen_exact,
    strlen_approx,
    strcpy,
    strncpy,
    must_be_NULL,
    cannot_be_NULL,
)


class ModelMiscTest(unittest.TestCase):
    def test_variadic_dec(self):
        @variadic
        def f():
            pass

        self.assertTrue(isvariadic(f))

    def test_no_variadic_dec(self):
        def f():
            pass

        self.assertFalse(isvariadic(f))


class ModelTest(unittest.TestCase):
    dirname = os.path.dirname(__file__)
    l = linux.SLinux(os.path.join(dirname, "binaries", "basic_linux_amd64"))
    state = State(ConstraintSet(), l)
    stack_top = state.cpu.RSP

    def _clear_constraints(self):
        self.state.context["migration_map"] = None
        self.state._constraints = ConstraintSet()

    def tearDown(self):
        self._clear_constraints()
        self.state.cpu.RSP = self.stack_top

    def _push_string(self, s):
        cpu = self.state.cpu
        cpu.RSP -= len(s)
        cpu.write_bytes(cpu.RSP, s)
        return cpu.RSP

    def _push_string_space(self, l):
        cpu = self.state.cpu
        cpu.RSP -= l
        return cpu.RSP

    def _pop_string_space(self, l):
        cpu = self.state.cpu
        cpu.RSP += l
        return cpu.RSP

    def assertItemsEqual(self, a, b):
        # Required for Python3 compatibility
        self.assertEqual(sorted(a), sorted(b))


class StrcmpTest(ModelTest):
    _multiprocess_can_split_ = True

    def _push2(self, s1, s2):
        s1ptr = self._push_string(s1)
        s2ptr = self._push_string(s2)
        return s1ptr, s2ptr

    def test_concrete_eq(self):
        s = "abc\0"
        strs = self._push2(s, s)
        ret = strcmp(self.state, *strs)
        self.assertEqual(ret, 0)

    def test_concrete_lt(self):
        def _concrete_lt(s1, s2):
            strs = self._push2(s1, s2)
            ret = strcmp(self.state, *strs)
            self.assertTrue(ret < 0)

        _concrete_lt("a\0", "b\0")
        _concrete_lt("a\0", "ab\0")

    def test_concrete_gt(self):
        def _concrete_gt(s1, s2):
            strs = self._push2(s1, s2)
            ret = strcmp(self.state, *strs)
            self.assertTrue(ret > 0)

        _concrete_gt("c\0", "b\0")
        _concrete_gt("bc\0", "b\0")

    def test_symbolic_actually_concrete(self):
        s1 = "ab\0"
        s2 = self.state.symbolicate_buffer("d+\0")
        strs = self._push2(s1, s2)

        ret = strcmp(self.state, *strs)
        self.assertTrue(self.state.must_be_true(ret < 0))

    def test_effective_null(self):
        s1 = self.state.symbolicate_buffer("a+")
        s2 = self.state.symbolicate_buffer("++")

        strs = self._push2(s1, s2)
        self.state.constrain(s1[1] == 0)
        self.state.constrain(s2[0] == ord("z"))

        ret = strcmp(self.state, *strs)
        self.assertTrue(self.state.must_be_true(ret < 0))

    def test_symbolic_concrete(self):
        s1 = "hi\0"
        s2 = self.state.symbolicate_buffer("+++\0")
        strs = self._push2(s1, s2)

        ret = strcmp(self.state, *strs)
        self.assertTrue(Z3Solver.instance().can_be_true(self.state.constraints, ret != 0))
        self.assertTrue(Z3Solver.instance().can_be_true(self.state.constraints, ret == 0))

        self.state.constrain(s2[0] == ord("a"))
        ret = strcmp(self.state, *strs)
        self.assertTrue(self.state.must_be_true(ret > 0))
        self._clear_constraints()

        self.state.constrain(s2[0] == ord("z"))
        ret = strcmp(self.state, *strs)
        self.assertTrue(self.state.must_be_true(ret < 0))
        self._clear_constraints()

        self.state.constrain(s2[0] == ord("h"))
        self.state.constrain(s2[1] == ord("i"))
        ret = strcmp(self.state, *strs)
        self.assertTrue(self.state.must_be_true(ret <= 0))

        self.state.constrain(s2[2] == ord("\0"))
        ret = strcmp(self.state, *strs)
        self.assertTrue(self.state.must_be_true(ret == 0))


class StrlenTest(ModelTest):
    def test_concrete(self):
        s = self._push_string("abc\0")
        ret = strlen_exact(self.state, s)
        self.assertEqual(ret, 3)
        ret = strlen_approx(self.state, s)
        self.assertEqual(ret, 3)

    def test_concrete_empty(self):
        s = self._push_string("\0")
        ret = strlen_exact(self.state, s)
        self.assertEqual(ret, 0)
        ret = strlen_approx(self.state, s)
        self.assertEqual(ret, 0)

    def test_symbolic_effective_null(self):
        sy = self.state.symbolicate_buffer("ab+")
        self.state.constrain(sy[2] == 0)
        s = self._push_string(sy)
        ret = strlen_exact(self.state, s)
        self.assertEqual(ret, 2)
        ret = strlen_approx(self.state, s)
        self.assertEqual(ret, 2)

    def test_symbolic_no_fork(self):
        sy = self.state.symbolicate_buffer("+++\0")
        s = self._push_string(sy)

        ret = strlen_approx(self.state, s)
        self.assertItemsEqual(
            range(4), Z3Solver.instance().get_all_values(self.state.constraints, ret)
        )

        self.state.constrain(sy[0] == 0)
        ret = strlen_exact(self.state, s)
        self.assertTrue(self.state.must_be_true(ret == 0))
        ret = strlen_approx(self.state, s)
        self.assertTrue(self.state.must_be_true(ret == 0))
        self._clear_constraints()

        self.state.constrain(sy[0] != 0)
        self.state.constrain(sy[1] == 0)
        ret = strlen_exact(self.state, s)
        self.assertTrue(self.state.must_be_true(ret == 1))
        ret = strlen_approx(self.state, s)
        self.assertTrue(self.state.must_be_true(ret == 1))
        self._clear_constraints()

        self.state.constrain(sy[0] != 0)
        self.state.constrain(sy[1] != 0)
        self.state.constrain(sy[2] == 0)
        ret = strlen_exact(self.state, s)
        self.assertTrue(self.state.must_be_true(ret == 2))
        ret = strlen_approx(self.state, s)
        self.assertTrue(self.state.must_be_true(ret == 2))
        self._clear_constraints()

        self.state.constrain(sy[0] != 0)
        self.state.constrain(sy[1] != 0)
        self.state.constrain(sy[2] != 0)
        ret = strlen_exact(self.state, s)
        self.assertTrue(self.state.must_be_true(ret == 3))
        ret = strlen_approx(self.state, s)
        self.assertTrue(self.state.must_be_true(ret == 3))

    def test_symbolic_fork(self):
        # This binary is compiled using gcc (Ubuntu 7.5.0-3ubuntu1~18.04) 7.5.0
        # with flags: -g -static -fno-builtin
        BIN_PATH = os.path.join(
            os.path.dirname(__file__), "binaries/str_model_tests", "sym_strlen_test"
        )
        tmp_dir = tempfile.TemporaryDirectory(prefix="mcore_test_sym_")
        m = Manticore(BIN_PATH, stdin_size=10, workspace_url=str(tmp_dir.name))

        addr_of_strlen = 0x04404D0

        @m.hook(addr_of_strlen)
        def strlen_model(state):
            state.invoke_model(strlen_exact)

        m.run()
        m.finalize()

        # Expected stdout outputs
        expected = {
            "Length of string is: 0",
            "Length of string is: 1",
            "Length of string is: 2",
            "Length of string is: 3",
            "Length of string is: 4",
            "Length of string is: 5",
        }

        # Make a list of the generated output states
        outputs = f"{str(m.workspace)}/test_*.stdout"
        stdouts = set()
        for out in glob(outputs):
            with open(out) as f:
                stdouts.add(f.read())

        # Assert that every expected stdout has a matching output
        self.assertEqual(expected, stdouts)

    def test_symbolic_mixed(self):
        sy = self.state.symbolicate_buffer("a+b+\0")
        s = self._push_string(sy)

        self.state.constrain(sy[1] == 0)
        ret = strlen_exact(self.state, s)
        self.assertTrue(self.state.must_be_true(ret == 1))
        ret = strlen_approx(self.state, s)
        self.assertTrue(self.state.must_be_true(ret == 1))
        self._clear_constraints()

        self.state.constrain(sy[1] != 0)
        self.state.constrain(sy[3] == 0)
        ret = strlen_exact(self.state, s)
        self.assertTrue(self.state.must_be_true(ret == 3))
        ret = strlen_approx(self.state, s)
        self.assertTrue(self.state.must_be_true(ret == 3))
        self._clear_constraints()

        self.state.constrain(sy[1] != 0)
        self.state.constrain(sy[3] != 0)
        ret = strlen_exact(self.state, s)
        self.assertTrue(self.state.must_be_true(ret == 4))
        ret = strlen_approx(self.state, s)
        self.assertTrue(self.state.must_be_true(ret == 4))


class StrcpyTest(ModelTest):
    def _assert_concrete(self, s, d):
        # Checks all characters are copied until the 1st that could be NULL
        cpu = self.state.cpu
        src = cpu.read_int(s, 8)
        dst = cpu.read_int(d, 8)
        offset = 0
        while cannot_be_NULL(self.state, src):
            self.assertEqual(src, dst)
            offset += 1
            src = cpu.read_int(s + offset, 8)
            dst = cpu.read_int(d + offset, 8)

        # Assert final NULL byte
        self.assertTrue(must_be_NULL(self.state, src))
        self.assertEqual(0, dst)

    def _test_strcpy(self, string, dst_len=None):
        """
        This method creates memory for a given src (with no possible NULL bytes but and a
        final NULL byte) and dst string pointers, asserts that everything is copied from src
        to dst until the NULL byte, and asserts the memory address returned by strcpy is
        equal to the given dst address.
        """
        # Create src and dst strings
        if dst_len is None:
            dst_len = len(string)
        cpu = self.state.cpu
        s = self._push_string(string)
        d = self._push_string_space(dst_len)
        dst_vals = [None] * dst_len
        for i in range(dst_len):
            # Set each dst byte to a random char to simplify equal comparisons
            c = random.randrange(1, 255)
            cpu.write_int(d + i, c, 8)
            dst_vals[i] = c

        ret = strcpy(self.state, d, s)

        # addresses should match
        self.assertEqual(ret, d)
        # assert everything is copied up to the 1st possible 0 is copied
        self._assert_concrete(s, d)

        # Delete stack space created
        self._pop_string_space(dst_len + len(string))

    def test_concrete(self):
        self._test_strcpy("abc\0")
        self._test_strcpy("a\0", dst_len=10)
        self._test_strcpy("abcdefghijklm\0")
        self._test_strcpy("a\0", dst_len=5)

    def test_concrete_empty(self):
        self._test_strcpy("\0")
        self._test_strcpy("\0", dst_len=10)

    def test_symbolic(self):
        # This binary is compiled using gcc (Ubuntu 7.5.0-3ubuntu1~18.04) 7.5.0
        # with flags: -g -static -fno-builtin
        BIN_PATH = os.path.join(
            os.path.dirname(__file__), "binaries/str_model_tests", "sym_strcpy_test"
        )
        tmp_dir = tempfile.TemporaryDirectory(prefix="mcore_test_sym_")
        m = Manticore(BIN_PATH, stdin_size=10, workspace_url=str(tmp_dir.name))

        addr_of_strcpy = 0x400418

        @m.hook(addr_of_strcpy)
        def strcpy_model(state):
            state.invoke_model(strcpy)

        m.run()
        m.finalize()

        # Approximate regexes for expected testcase output
        # Example Match above each regex
        # Manticore varies the hex output slightly per run
        expected = [
            # STDIN: b'\x00AAAAAAAAA'
            r"STDIN: b\'\\x00A.{8,32}\'",
            # STDIN: b'\xffA\x00\xff\xff\xff\xff\xff\xff\xff'
            r"STDIN: b\'(\\x((?!(00))[0-9a-f]{2}))A\\x00(\\x([0-9a-f]{2})){7}\'",
            # STDIN: b'\xffA\xff\x00\xff\xff\xff\xff\xff\xff'
            r"STDIN: b\'(\\x((?!(00))[0-9a-f]{2}))A(\\x((?!(00))[0-9a-f]{2}))\\x00(\\x([0-9a-f]{2})){6}\'",
            # STDIN: b'\xffA\xff\xff\x00\xff\xff\xff\xff\xff'
            r"STDIN: b\'(\\x((?!(00))[0-9a-f]{2}))A(\\x((?!(00))[0-9a-f]{2})){2}\\x00(\\x([0-9a-f]{2})){5}\'",
            # STDIN: b'\x00\xbe\xbe\xbe\xbe\xbe\xbe\xbe\xbe\xbe'
            r"STDIN: b\'\\x00(\\x([0-9a-f]{2})){9}\'",
            # STDIN: b'\xff\x00\xff\xff\xff\xff\xff\xff\xff\xff'
            r"STDIN: b\'(\\x((?!(00))([0-9a-f]{2}))){1}\\x00(\\x([0-9a-f]{2})){8}\'",
            # STDIN: b'\xff\xff\x00\xff\xff\xff\xff\xff\xff\xff'
            r"STDIN: b\'(\\x((?!(00))([0-9a-f]{2}))){2}\\x00(\\x([0-9a-f]{2})){7}\'",
            # STDIN: b'\xff\xff\xff\x00\xff\xff\xff\xff\xff\xff'
            r"STDIN: b\'(\\x((?!(00))([0-9a-f]{2}))){3}\\x00(\\x([0-9a-f]{2})){6}\'",
            # STDIN: b'\xff\xff\xff\xff\x00\xff\xff\xff\xff\xff'
            r"STDIN: b\'(\\x((?!(00))([0-9a-f]{2}))){4}\\x00(\\x([0-9a-f]{2})){5}\'",
            # STDIN: b'\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'
            r"STDIN: b\'(\\x((?!(00))([0-9a-f]{2}))){10}\'",
        ]

        inputs = f"{str(m.workspace)}/test_*.input"

        # Make a list of the generated input states
        stdins = []
        for inpt in glob(inputs):
            with open(inpt) as f:
                stdins.append(f.read())

        # Check the number of input states matches the number of regexes
        self.assertEqual(len(stdins), len(expected))

        # Assert that every regex has a matching input
        for e in expected:
            match = False
            for s in stdins:
                if re.fullmatch(e, s) == None:
                    match = True
                    break
            self.assertTrue(match)


class StrncpyTest(ModelTest):
    def _assert_concrete(self, s, d, n):
        # Checks that n characters are copied until a NULL in the src
        # and that NULL is written for the distance between src and NULL
        cpu = self.state.cpu
        src = cpu.read_int(s, 8)
        dst = cpu.read_int(d, 8)
        offset = 0

        # Check that min(n, length of src) characters are copied from src to dst
        while not must_be_NULL(self.state, src) and offset < n:
            self.assertEqual(src, dst)
            offset += 1
            src = cpu.read_int(s + offset, 8)
            dst = cpu.read_int(d + offset, 8)

        # Check that N - length of src characters are NULL padded
        while offset < n:
            self.assertEqual(0, dst)
            offset += 1
            dst = cpu.read_int(d + offset, 8)

    def _test_strncpy(self, string, n):
        """
        This method creates memory for a given src (with no possible NULL bytes but and a
        final NULL byte) and dst string pointers, asserts that everything is copied from src
        to dst until the NULL byte, and asserts the memory address returned by strcpy is
        equal to the given dst address.
        """
        dst_len = n + 1
        cpu = self.state.cpu
        s = self._push_string(string)
        d = self._push_string_space(dst_len)
        dst_vals = [None] * dst_len
        for i in range(dst_len):
            # Set each dst byte to a random char to simplify equal comparisons
            c = random.randrange(1, 255)
            cpu.write_int(d + i, c, 8)
            dst_vals[i] = c

        ret = strncpy(self.state, d, s, n)

        # addresses should match
        self.assertEqual(ret, d)
        # assert everything is copied up to the 1st possible 0 is copied
        self._assert_concrete(s, d, n)

        # Delete stack space created
        self._pop_string_space(dst_len + len(string))

    def test_concrete(self):
        self._test_strncpy("abc\0", n=4)
        self._test_strncpy("abcdefghijklm\0", n=20)
        self._test_strncpy("a\0", n=10)

    def test_small_n(self):
        self._test_strncpy("a\0", n=1)
        self._test_strncpy("abcdefghijklm\0", n=0)

    def test_concrete_empty(self):
        self._test_strncpy("\0", n=1)
        self._test_strncpy("\0", n=10)

    def test_symbolic(self):
        # Create src and dst strings
        # This binary is compiled using gcc (Ubuntu 7.5.0-3ubuntu1~18.04) 7.5.0
        # with flags: -g -static -fno-builtin
        BIN_PATH = os.path.join(
            os.path.dirname(__file__), "binaries/str_model_tests", "sym_strncpy_test"
        )
        tmp_dir = tempfile.TemporaryDirectory(prefix="mcore_test_sym_")
        m = Manticore(BIN_PATH, stdin_size=10, workspace_url=str(tmp_dir.name))

        addr_of_strncpy = 0x0400490

        @m.hook(addr_of_strncpy)
        def strncpy_model(state):
            state.invoke_model(strncpy)

        m.run()
        m.finalize()

        # Approximate regexes for expected testcase output
        # Example Match above each regex
        # Manticore varies the hex output slightly per run
        expected = [
            # STDIN: b'\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'
            r"STDIN: b\'\\x00(\\x([0-9a-f]{2})){9}\'",
            # STDIN: b'\xff\x00\xff\xff\xff\xff\xff\xff\xff\xff'
            r"STDIN: b\'(\\x((?!(00))([0-9a-f]{2}))){1}\\x00(\\x([0-9a-f]{2})){8}\'",
            # STDIN: b'\xff\xff\x00\xff\xff\xff\xff\xff\xff\xff'
            r"STDIN: b\'(\\x((?!(00))([0-9a-f]{2}))){2}\\x00(\\x([0-9a-f]{2})){7}\'",
            # STDIN: b'\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff'
            r"STDIN: b\'(\\x((?!(00))([0-9a-f]{2}))){10}\'",
        ]

        inputs = f"{str(m.workspace)}/test_*.input"

        # Make a list of the generated input states
        stdins = []
        for inpt in glob(inputs):
            with open(inpt) as f:
                stdins.append(f.read())

        # Check the number of input states matches the number of regexes
        self.assertEqual(len(stdins), len(expected))

        # Assert that every regex has a matching input
        for e in expected:
            match = False
            for s in stdins:
                if re.fullmatch(e, s) == None:
                    match = True
                    break
            self.assertTrue(match)
