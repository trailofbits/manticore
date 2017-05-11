import unittest

from manticore.core.state import State
from manticore.core.smtlib import BitVecVariable
from manticore.core.smtlib import ConstraintSet
from manticore.platforms import linux

class FakeMemory(object):
    def __init__(self):
        self._constraints = None

    @property
    def constraints(self):
        return self._constraints

class FakeCpu(object):
    def __init__(self):
        self._memory = FakeMemory()

    @property
    def memory(self):
        return self._memory

class FakePlatform(object):
    def __init__(self):
        self._constraints = None
        self.procs = [FakeCpu()]

    @property
    def current(self):
        return self.procs[0]

    @property
    def constraints(self):
        return self._constraints


class StateTest(unittest.TestCase):
    def setUp(self):
        l = linux.Linux('/bin/ls')
        self.state = State(ConstraintSet(), l)

    def test_solve_one(self):
        val = 42
        expr = BitVecVariable(32, 'tmp')
        self.state.constrain(expr == val)
        solved = self.state.solve_one(expr)
        self.assertEqual(solved, val)

    def test_solve_n(self):
        expr = BitVecVariable(32, 'tmp')
        self.state.constrain(expr > 4)
        self.state.constrain(expr < 7)
        solved = self.state.solve_n(expr, 2)
        self.assertEqual(solved, [5,6])

    def test_solve_n2(self):
        expr = BitVecVariable(32, 'tmp')
        self.state.constrain(expr > 4)
        self.state.constrain(expr < 100)
        solved = self.state.solve_n(expr, 5)
        self.assertEqual(len(solved), 5)

    def test_policy_one(self):
        expr = BitVecVariable(32, 'tmp')
        self.state.constrain(expr > 0)
        self.state.constrain(expr < 100)
        solved = self.state.concretize(expr, 'ONE')
        self.assertEqual(len(solved), 1)
        self.assertIn(solved[0], xrange(100))
    
    def test_state(self):
        constraints = ConstraintSet()
        initial_state = State(constraints, FakePlatform())

        arr = initial_state.symbolicate_buffer('+'*100, label='SYMBA')
        initial_state.constrain(arr[0] > 0x41)
        self.assertTrue(len(initial_state.constraints.declarations) == 1 ) 
        with initial_state as new_state:

            self.assertTrue(len(initial_state.constraints.declarations) == 1 ) 
            self.assertTrue(len(new_state.constraints.declarations) == 1 ) 
            arrb = new_state.symbolicate_buffer('+'*100, label='SYMBB')

            self.assertTrue(len(initial_state.constraints.declarations) == 1 ) 
            self.assertTrue(len(new_state.constraints.declarations) == 1 ) 

            new_state.constrain(arrb[0] > 0x42)


            self.assertTrue(len(new_state.constraints.declarations) == 2 ) 


        self.assertTrue(len(initial_state.constraints.declarations) == 1 ) 

    def test_new_symbolic_buffer(self):
        length = 64
        expr = self.state.new_symbolic_buffer(length)
        self.assertEqual(len(expr), length)

    def test_new_symbolic_value(self):
        length = 64
        expr = self.state.new_symbolic_value(length)
        self.assertEqual(expr.size, length)

    def test_new_bad_symbolic_value(self):
        length = 62
        with self.assertRaises(Exception):
            expr = self.state.new_symbolic_value(length)

    def test_record_branches(self):
        branch = 0x80488bb
        target = 0x8048997
        fallthrough = 0x80488c1
        self.state.last_pc = (0, branch)

        self.state.record_branches([target, fallthrough])

        self.assertEqual(self.state.branches[(branch, target)], 1)
        self.assertEqual(self.state.branches[(branch, fallthrough)], 1)

        self.state.record_branches([target, fallthrough])

        self.assertEqual(self.state.branches[(branch, target)], 2)
        self.assertEqual(self.state.branches[(branch, fallthrough)], 2)

