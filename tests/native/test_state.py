import io
import unittest
import os
from contextlib import redirect_stdout

from manticore.core.state import StateBase
from manticore.utils.event import Eventful
from manticore.platforms import linux
from manticore.native.state import State
from manticore.core.smtlib import BitVecVariable, ConstraintSet
from manticore.native import Manticore
from manticore.native.plugins import Merger
from manticore.core.plugin import Plugin
from manticore.utils import config
from manticore.utils.helpers import pickle_dumps


class FakeMemory:
    def __init__(self):
        self._constraints = None

    @property
    def constraints(self):
        return self._constraints

    @constraints.setter
    def constraints(self, constraints):
        self._constraints = constraints


class FakeCpu:
    def __init__(self):
        self._memory = FakeMemory()

    @property
    def memory(self):
        return self._memory


class FakePlatform(Eventful):
    def __init__(self):
        super().__init__()
        self._constraints = None
        self.procs = [FakeCpu()]

    def __getstate__(self):
        state = super().__getstate__()
        state["cons"] = self._constraints
        state["procs"] = self.procs
        return state

    def __setstate__(self, state):
        super().__setstate__(state)
        self._constraints = state["cons"]
        self.procs = state["procs"]

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
        dirname = os.path.dirname(__file__)
        l = linux.Linux(os.path.join(dirname, "binaries", "basic_linux_amd64"))
        self.state = State(ConstraintSet(), l)

    def test_solve_one(self):
        val = 42
        expr = BitVecVariable(32, "tmp")
        self.state.constrain(expr == val)
        solved = self.state.solve_one(expr)
        self.assertEqual(solved, val)

    def test_solve_n(self):
        expr = BitVecVariable(32, "tmp")
        self.state.constrain(expr > 4)
        self.state.constrain(expr < 7)
        solved = sorted(self.state.solve_n(expr, 2))
        self.assertEqual(solved, [5, 6])

    def test_solve_n2(self):
        expr = BitVecVariable(32, "tmp")
        self.state.constrain(expr > 4)
        self.state.constrain(expr < 100)
        solved = self.state.solve_n(expr, 5)
        self.assertEqual(len(solved), 5)

    def test_solve_min_max(self):
        expr = BitVecVariable(32, "tmp")
        self.state.constrain(expr > 4)
        self.state.constrain(expr < 7)
        self.assertEqual(self.state.solve_min(expr), 5)
        self.assertEqual(self.state.solve_max(expr), 6)
        self.assertEqual(self.state.solve_minmax(expr), (5, 6))

    def test_policy_one(self):
        expr = BitVecVariable(32, "tmp")
        self.state.constrain(expr > 0)
        self.state.constrain(expr < 100)
        solved = self.state.concretize(expr, "ONE")
        self.assertEqual(len(solved), 1)
        self.assertIn(solved[0], range(100))

    def test_state(self):
        constraints = ConstraintSet()
        initial_state = State(constraints, FakePlatform())

        arr = initial_state.symbolicate_buffer("+" * 100, label="SYMBA")
        initial_state.constrain(arr[0] > 0x41)
        self.assertTrue(len(initial_state.constraints.declarations) == 1)
        with initial_state as new_state:
            self.assertTrue(len(initial_state.constraints.declarations) == 1)
            self.assertTrue(len(new_state.constraints.declarations) == 1)
            arrb = new_state.symbolicate_buffer("+" * 100, label="SYMBB")

            self.assertTrue(len(initial_state.constraints.declarations) == 1)
            self.assertTrue(len(new_state.constraints.declarations) == 1)

            new_state.constrain(arrb[0] > 0x42)

            self.assertTrue(len(new_state.constraints.declarations) == 2)

        self.assertTrue(len(initial_state.constraints.declarations) == 1)

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

    def test_tainted_symbolic_buffer(self):
        taint = ("TEST_TAINT",)
        expr = self.state.new_symbolic_buffer(64, taint=taint)
        self.assertEqual(expr.taint, frozenset(taint))

    def test_tainted_symbolic_value(self):
        taint = ("TEST_TAINT",)
        expr = self.state.new_symbolic_value(64, taint=taint)
        self.assertEqual(expr.taint, frozenset(taint))

    def test_state_hook(self):
        initial_state = State(ConstraintSet(), FakePlatform())

        def fake_hook(_: StateBase) -> None:
            return None

        self.assertTrue(len(initial_state._hooks) == 0)
        self.assertTrue(len(initial_state._after_hooks) == 0)

        # This hook should be propagated to child state
        initial_state.add_hook(0x4000, fake_hook, after=False)

        self.assertTrue(len(initial_state._hooks) == 1)
        self.assertTrue(len(initial_state._after_hooks) == 0)

        with initial_state as new_state:
            # Child state has parent's hook
            self.assertTrue(len(new_state._hooks) == 1)
            self.assertTrue(len(new_state._after_hooks) == 0)

            # Try adding the same hook
            new_state.add_hook(0x4000, fake_hook, after=False)
            # Should not add again
            self.assertTrue(len(new_state._hooks) == 1)

            # Add two hooks for after and before instruction
            new_state.add_hook(0x4001, fake_hook, after=True)
            new_state.add_hook(0x4001, fake_hook, after=False)

            # A new hook added to both lists
            self.assertTrue(len(new_state._hooks) == 2)
            self.assertTrue(len(new_state._after_hooks) == 1)

            # Ensure parent state was not affected
            self.assertTrue(len(initial_state._hooks) == 1)
            self.assertTrue(len(initial_state._after_hooks) == 0)

            # Remove one of the hooks we added
            new_state.remove_hook(0x4000, fake_hook, after=False)
            # Try to remove a non-existent hook
            self.assertFalse(new_state.remove_hook(0x4000, fake_hook, after=True))

            # Ensure removal
            self.assertTrue(len(new_state._hooks) == 1)
            self.assertTrue(len(new_state._after_hooks) == 1)

            # Ensure parent state wasn't affected
            self.assertTrue(len(initial_state._hooks) == 1)
            self.assertTrue(len(initial_state._after_hooks) == 0)

            # Add hook to all PC in our parent state
            initial_state.add_hook(None, fake_hook, after=True)

        # Ensure only the hooks we added are still here
        self.assertTrue(len(initial_state._hooks) == 1)
        self.assertTrue(len(initial_state._after_hooks) == 1)

    def testContextSerialization(self):
        import pickle as pickle

        initial_file = ""
        new_file = ""
        new_new_file = ""
        constraints = ConstraintSet()
        initial_state = State(constraints, FakePlatform())
        initial_state.context["step"] = 10
        initial_file = pickle_dumps(initial_state)
        with initial_state as new_state:
            self.assertEqual(initial_state.context["step"], 10)
            self.assertEqual(new_state.context["step"], 10)

            new_state.context["step"] = 20

            self.assertEqual(initial_state.context["step"], 10)
            self.assertEqual(new_state.context["step"], 20)
            new_file = pickle_dumps(new_state)

            with new_state as new_new_state:
                self.assertEqual(initial_state.context["step"], 10)
                self.assertEqual(new_state.context["step"], 20)
                self.assertEqual(new_new_state.context["step"], 20)

                new_new_state.context["step"] += 10

                self.assertEqual(initial_state.context["step"], 10)
                self.assertEqual(new_state.context["step"], 20)
                self.assertEqual(new_new_state.context["step"], 30)

                new_new_file = pickle_dumps(new_new_state)

                self.assertEqual(initial_state.context["step"], 10)
                self.assertEqual(new_state.context["step"], 20)
                self.assertEqual(new_new_state.context["step"], 30)

            self.assertEqual(initial_state.context["step"], 10)
            self.assertEqual(new_state.context["step"], 20)

        self.assertEqual(initial_state.context["step"], 10)

        del initial_state
        del new_state
        del new_new_state

        initial_state = pickle.loads(initial_file)
        self.assertEqual(initial_state.context["step"], 10)
        new_state = pickle.loads(new_file)
        self.assertEqual(new_state.context["step"], 20)
        new_new_state = pickle.loads(new_new_file)
        self.assertEqual(new_new_state.context["step"], 30)


"""
This function needs to be a global function for the following test or else we
get the following error
    E       AttributeError: Can't pickle local object 'StateHooks.test_state_hooks.<locals>.do_nothing'
"""


def do_nothing(_: StateBase) -> None:
    return None


def fin(_: StateBase) -> None:
    print("Reached fin callback")
    return None


class StateHooks(unittest.TestCase):
    def setUp(self):
        core = config.get_group("core")
        core.seed = 61
        core.mprocessing = core.mprocessing.single

        dirname = os.path.dirname(__file__)
        self.m = Manticore(os.path.join(dirname, "binaries", "basic_linux_amd64"), policy="random")

    def test_state_hooks(self):
        @self.m.hook(0x400610, after=True)
        def process_hook(state: State) -> None:
            # We can't remove because the globally applied hooks are stored in
            # the Manticore class, not State
            self.assertFalse(state.remove_hook(0x400610, process_hook, after=True))
            # We can remove this one because it was applied specifically to this
            # State (or its parent)
            self.assertTrue(state.remove_hook(None, do_nothing, after=True))

            state.add_hook(None, do_nothing, after=False)
            state.add_hook(None, do_nothing, after=True)
            state.add_hook(0x400647, fin, after=True)
            state.add_hook(0x400647, fin, after=False)

        for state in self.m.ready_states:
            self.m.add_hook(None, do_nothing, after=True, state=state)

        f = io.StringIO()
        with redirect_stdout(f):
            self.m.run()
        self.assertIn("Reached fin callback", f.getvalue())


class StateMergeTest(unittest.TestCase):

    # Need to add a plugin that counts the number of states in did_fork_state, and records the max
    # Then, when we hit

    class StateCounter(Plugin):
        def did_fork_state_callback(self, *_args, **_kwargs):
            self.max_states = max(
                self.max_states,
                self.manticore.count_busy_states()
                + self.manticore.count_ready_states()
                + self.manticore.count_killed_states()
                + self.manticore.count_terminated_states(),
            )

        @property
        def max_states(self):
            with self.manticore.locked_context() as ctx:
                return ctx.setdefault("max_states", 0)

        @max_states.setter
        def max_states(self, new_val):
            with self.manticore.locked_context() as ctx:
                ctx["max_states"] = new_val

    def setUp(self):
        core = config.get_group("core")
        core.seed = 61
        core.mprocessing = core.mprocessing.single

        dirname = os.path.dirname(__file__)
        self.m = Manticore(
            os.path.join(dirname, "binaries", "basic_state_merging"), policy="random"
        )
        self.plugin = self.StateCounter()

        self.m.register_plugin(Merger())
        self.m.register_plugin(self.plugin)

    def test_state_merging(self):
        @self.m.hook(0x40065D)
        def hook_post_merge(*_args, **_kwargs):
            with self.m.locked_context() as ctx:
                ctx["state_count"] = (
                    self.m.count_busy_states()
                    + self.m.count_ready_states()
                    + self.m.count_killed_states()
                    + self.m.count_terminated_states()
                )

        self.m.run()
        s = config.get_group("core").seed
        self.assertLess(
            self.m.context["state_count"],
            self.plugin.max_states,
            f"State merging failed with seed: {s}",
        )
