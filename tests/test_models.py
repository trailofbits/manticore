import unittest

from manticore.core.smtlib import ConstraintSet
from manticore.core.state import State
from manticore.platforms import linux

from manticore.models import strcmp


class StrcmpTest(unittest.TestCase):
    def setUp(self):
        l = linux.SLinux('/bin/ls')
        self.state = State(ConstraintSet(), l)

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

    def test_symbolic_concrete(self):
        cpu = self.state.cpu
        s1 = 'hi\0'
        z = self._push_string(s1)

        s2 = self.state.symbolicate_buffer('+++\0')
        cpu.RSP -= len(s2)
        cpu.write_bytes(cpu.RSP, s2)
        assert 0



        # print s2


        # strs = self._push2(s1, s2)

        ret = strcmp(self.state, *strs)
        print ret
        assert 0

