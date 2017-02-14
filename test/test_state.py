import unittest

from core.executor import State
from core.smtlib import BitVecVariable
from core.smtlib import ConstraintSet
from models import linux

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

class FakeModel(object):
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
        self.state.add(expr == val)
        solved = self.state.solve_one(expr)
        self.assertEqual(solved, val)

    def test_solve_n(self):
        expr = BitVecVariable(32, 'tmp')
        self.state.add(expr > 4)
        self.state.add(expr < 7)
        solved = self.state.solve_n(expr, 2)
        self.assertEqual(solved, [5,6])

    def test_solve_n2(self):
        expr = BitVecVariable(32, 'tmp')
        self.state.add(expr > 4)
        self.state.add(expr < 100)
        solved = self.state.solve_n(expr, 5)
        self.assertEqual(len(solved), 5)
    
    def test_state(self):
        constraints = ConstraintSet()
        initial_state = State(constraints, FakeModel())

        arr = initial_state.symbolicate_buffer('+'*100, label='SYMBA')
        initial_state.add(arr[0] > 0x41)
        self.assertTrue(len(initial_state.constraints.declarations) == 1 ) 
        with initial_state as new_state:

            self.assertTrue(len(initial_state.constraints.declarations) == 1 ) 
            self.assertTrue(len(new_state.constraints.declarations) == 1 ) 
            arrb = new_state.symbolicate_buffer('+'*100, label='SYMBB')

            self.assertTrue(len(initial_state.constraints.declarations) == 1 ) 
            self.assertTrue(len(new_state.constraints.declarations) == 1 ) 

            new_state.add(arrb[0] > 0x42)


            self.assertTrue(len(new_state.constraints.declarations) == 2 ) 


        self.assertTrue(len(initial_state.constraints.declarations) == 1 ) 
