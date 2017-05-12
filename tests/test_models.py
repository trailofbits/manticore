import unittest

from manticore.core.smtlib import ConstraintSet, solver
from manticore.core.state import State
from manticore.platforms import linux

from manticore.models import strcmp


class StrcmpTest(unittest.TestCase):
    l = linux.SLinux('/bin/ls')
    state = State(ConstraintSet(), l)
    stack_top = state.cpu.RSP

    def _clear_constraints(self):
        self.state.constraints = ConstraintSet()

    def tearDown(self):
        self._clear_constraints()
        self.state.cpu.RSP = self.stack_top

    def _push_string(self, s):
        cpu = self.state.cpu
        cpu.RSP -= len(s)
        cpu.write_bytes(cpu.RSP, s)
        return cpu.RSP

    def _push2(self, s1, s2):
        s1ptr = self._push_string(s1)
        s2ptr = self._push_string(s2)
        return s1ptr, s2ptr

    def test_concrete_eq(self):
        s = 'abc\0'
        strs = self._push2(s, s)
        ret = strcmp(self.state, *strs)
        self.assertEqual(ret, 0)

    def test_concrete_lt(self):
        def _concrete_lt(s1, s2):
            strs = self._push2(s1, s2)
            ret = strcmp(self.state, *strs)
            self.assertTrue(ret < 0)
        _concrete_lt('a\0', 'b\0')
        _concrete_lt('a\0', 'ab\0')


    def test_concrete_gt(self):
        def _concrete_gt(s1, s2):
            strs = self._push2(s1, s2)
            ret = strcmp(self.state, *strs)
            self.assertTrue(ret > 0)
        _concrete_gt('c\0', 'b\0')
        _concrete_gt('bc\0', 'b\0')

    def test_symbolic_actually_concrete(self):
        s1 = 'ab\0'
        s2 = self.state.symbolicate_buffer('d+\0')
        strs = self._push2(s1, s2)

        ret = strcmp(self.state, *strs)
        self.assertFalse(solver.can_be_true(self.state.constraints, ret >= 0))

    def test_symbolic_concrete(self):
        s1 = 'hi\0'
        s2 = self.state.symbolicate_buffer('+++\0')
        strs = self._push2(s1, s2)

        ret = strcmp(self.state, *strs)
        self.assertTrue(solver.can_be_true(self.state.constraints, ret != 0))
        self.assertTrue(solver.can_be_true(self.state.constraints, ret == 0))

        self.state.constrain(s2[0] == ord('a'))
        ret = strcmp(self.state, *strs)
        self.assertFalse(solver.can_be_true(self.state.constraints, ret <= 0))
        self._clear_constraints()

        self.state.constrain(s2[0] == ord('z'))
        ret = strcmp(self.state, *strs)
        self.assertFalse(solver.can_be_true(self.state.constraints, ret >= 0))
        self._clear_constraints()

        self.state.constrain(s2[0] == ord('h'))
        self.state.constrain(s2[1] == ord('i'))
        ret = strcmp(self.state, *strs)
        self.assertFalse(solver.can_be_true(self.state.constraints, ret > 0))

        self.state.constrain(s2[2] == ord('\0'))
        ret = strcmp(self.state, *strs)
        self.assertFalse(solver.can_be_true(self.state.constraints, ret != 0))
