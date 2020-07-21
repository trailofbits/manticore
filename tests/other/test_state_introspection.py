import unittest
from manticore.native import Manticore
from pathlib import Path
from time import sleep
from manticore.utils.enums import StateLists

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

    def introspect_loop(self, thread):
        while True:
            self.history.append(thread.manticore.introspect())
            sleep(0.5)

    def test_introspect_daemon(self):
        self.history = []
        m = Manticore(ms_file, stdin_size=17)
        m.register_daemon(self.introspect_loop)
        m.run()

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
        self.assertEqual(progression[0][1], 1)  # We start with just one busy state
        self.assertGreater(progression[-1][2], 0)  # Once finished, we have some terminated states
        self.assertEqual(progression[-1][0], 0)  # Once finished, we have no ready states
        # Once finished, we have more terminated than busy states. We may not have completely finished
        # when the callback fires
        self.assertGreater(progression[-1][2], progression[-1][1])


if __name__ == "__main__":
    unittest.main()
