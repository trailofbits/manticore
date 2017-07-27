import signal
import unittest

from multiprocessing.managers import SyncManager

from manticore.platforms import linux
from manticore.utils.event import Signal
from manticore.core.state import State
from manticore.core.smtlib import BitVecVariable, ConstraintSet
from manticore.core.workspace import *

manager = SyncManager()
manager.start(lambda: signal.signal(signal.SIGINT, signal.SIG_IGN))

class FakeMemory(object):
    def __init__(self):
        self._constraints = None

    @property
    def constraints(self):
        return self._constraints

    @constraints.setter
    def constraints(self, constraints):
        self._constraints = constraints

class FakeCpu(object):
    def __init__(self):
        self.will_decode_instruction = Signal()
        self.will_execute_instruction = Signal()
        self.did_execute_instruction = Signal()
        self.will_emulate_instruction = Signal()
        self.did_emulate_instruction = Signal()

        self.will_read_register = Signal()
        self.will_write_register = Signal()
        self.will_read_memory = Signal()
        self.will_write_memory = Signal()

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

    @constraints.setter
    def constraints(self, constraints):
        self._constraints = constraints
        for proc in self.procs:
            proc.memory.constraints = constraints


class StateTest(unittest.TestCase):
    _multiprocess_can_split_ = True
    def setUp(self):
        l = linux.Linux('/bin/ls')
        self.state = State(ConstraintSet(), l)
        self.lock = manager.Condition(manager.RLock())

    def test_workspace_save_load(self):
        self.state.constraints.add(True)
        workspace = Workspace(self.lock, 'mem:')
        id_ = workspace.save_state(self.state)
        state = workspace.load_state(id_)


        # Make sure our memory maps come back through serialization
        for left, right in  zip(sorted(self.state.mem._maps),
                                sorted(state.mem._maps)):
            self.assertEqual(left.start, right.start)
            self.assertEqual(left.end,   right.end)
            self.assertEqual(left.name,  right.name)

        # Check constraints
        self.assertEqual(str(state.constraints),
                         str(self.state.constraints))

    def test_workspace_id_start_with_zero(self):
        workspace = Workspace(self.lock, 'mem:')
        id_ = workspace.save_state(self.state)
        self.assertEquals(id_, 0)

    def test_output(self):
        out = ManticoreOutput('mem:')
        out.save_testcase(self.state, 'saving state')
        keys = [x[14:] for x in out._store._data.keys()]

        # Make sure we log everything we should be logging
        self.assertIn('smt', keys)
        self.assertIn('trace', keys)
        self.assertIn('syscalls', keys)
        self.assertIn('stdout', keys)
        self.assertIn('stdin', keys)
        self.assertIn('messages', keys)
        self.assertIn('txt', keys)
        self.assertIn('pkl', keys)
