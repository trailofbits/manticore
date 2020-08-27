import unittest
from manticore.native import Manticore
from manticore.core.plugin import IntrospectionAPIPlugin, StateDescriptor
from pathlib import Path
from time import sleep
from manticore.utils.enums import StateLists
import io
import contextlib

ms_file = str(
    Path(__file__).parent.parent.parent.joinpath("examples", "linux", "binaries", "multiple-styles")
)


class TestDaemonThread(unittest.TestCase):
    def daemon(self, _thread):
        while True:
            self.fired = True
            sleep(1)

    def test_daemon(self):
        self.fired = False
        m = Manticore(ms_file, stdin_size=17)
        m.register_daemon(self.daemon)
        m.run()

        self.assertTrue(self.fired)


class TestIntrospect(unittest.TestCase):
    def introspect_loop(self, thread):
        while True:
            self.history.append(thread.manticore.introspect())
            sleep(0.5)

    def test_introspect_daemon(self):
        self.history = []
        m = Manticore(ms_file, stdin_size=17)
        m.register_daemon(self.introspect_loop)
        m.run()

        sleep(1)  # Leave time for the callback to fire after we've finished
        self.assertGreater(len(self.history), 0)
        progression = []
        for hist in self.history:
            hist = hist.values()
            progression.append(
                (
                    sum(1 if (st.state_list == StateLists.ready) else 0 for st in hist),
                    sum(1 if (st.state_list == StateLists.busy) else 0 for st in hist),
                    sum(1 if (st.state_list == StateLists.terminated) else 0 for st in hist),
                )
            )
        self.assertEqual(progression[-1][0], 0)  # Once finished, we have no ready states
        self.assertEqual(progression[-1][1], 0)  # Once finished, we have no busy states
        # Once finished, we have only terminated states.
        self.assertGreater(progression[-1][2], 0)

        f = io.StringIO()
        with contextlib.redirect_stdout(f):
            m.pretty_print_states()
        self.assertIn("Terminated States: {}".format(progression[-1][2]), f.getvalue())


class MyIntrospector(IntrospectionAPIPlugin):
    def on_execution_intermittent_callback(self, state, update_cb, *args, **kwargs):
        super().on_execution_intermittent_callback(state, update_cb, *args, **kwargs)
        with self.locked_context("manticore_state", dict) as context:
            context[state.id].i_am_custom = True


class TestCustomIntrospector(unittest.TestCase):
    def introspect_loop(self, thread):
        while True:
            self.history.append(thread.manticore.introspect())
            sleep(0.5)

    def test_custom_introspector(self):
        self.history = []
        m = Manticore(ms_file, introspection_plugin_type=MyIntrospector, stdin_size=17)
        m.register_daemon(self.introspect_loop)
        m.run()

        self.assertGreater(len(self.history), 0)
        self.assertTrue(any(getattr(st, "i_am_custom", False) for st in self.history[-1].values()))


if __name__ == "__main__":
    unittest.main()
