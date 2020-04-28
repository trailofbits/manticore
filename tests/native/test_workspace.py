import unittest

from manticore.core.smtlib import ConstraintSet
from manticore.core.workspace import *
from manticore.native.state import State
from manticore.platforms import linux
from manticore.utils.event import Eventful


class FakeMemory:
    def __init__(self):
        self._constraints = None

    @property
    def constraints(self):
        return self._constraints

    @constraints.setter
    def constraints(self, constraints):
        self._constraints = constraints


class FakeCpu(Eventful):
    def __init__(self):
        super().__init__()

        self._memory = FakeMemory()

    @property
    def memory(self):
        return self._memory


class FakePlatform:
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
        # if not hasattr(self, 'manager'):
        #    self.manager = SyncManager()
        #    self.manager.start(lambda: signal.signal(signal.SIGINT, signal.SIG_IGN))
        dirname = os.path.dirname(__file__)
        l = linux.Linux(os.path.join(dirname, "binaries", "basic_linux_amd64"))
        self.state = State(ConstraintSet(), l)
        # self.lock = self.manager.Condition()

    def test_workspace_save_load(self):
        self.state.constraints.add(True)
        workspace = Workspace("mem:")
        id_ = workspace.save_state(self.state)
        state = workspace.load_state(id_)

        # Make sure our memory maps come back through serialization
        for left, right in zip(sorted(self.state.mem._maps), sorted(state.mem._maps)):
            self.assertEqual(left.start, right.start)
            self.assertEqual(left.end, right.end)
            self.assertEqual(left.name, right.name)

        # Check constraints
        self.assertEqual(str(state.constraints), str(self.state.constraints))

    def test_workspace_id_start_with_zero(self):
        workspace = Workspace("mem:")
        id_ = workspace.save_state(self.state)
        self.assertEqual(id_, 0)

    def test_output(self):
        out = ManticoreOutput("mem:")
        name = "mytest"
        message = "custom message"
        testcase = out.testcase(prefix=name)

        out.save_testcase(self.state, testcase, message)
        workspace = out._store._data

        # Make sure names are constructed correctly
        for entry, data in workspace.items():
            if entry.startswith("."):
                continue
            self.assertTrue(entry.startswith(name))
            if "messages" in entry:
                self.assertTrue(message in data)

        keys = [x.split(".")[1] for x in workspace.keys()]

        for key in self.state.platform.generate_workspace_files():
            self.assertIn(key, keys)

        # Make sure we log everything we should be logging
        self.assertIn("smt", keys)
        self.assertIn("trace", keys)
        self.assertIn("messages", keys)
        self.assertIn("input", keys)
        # self.assertIn('pkl', keys)  # This is not done by the platform but
        # by the core
