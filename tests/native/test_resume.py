import unittest
from manticore.native import Manticore
from manticore.core.state import SerializeState, TerminateState
from pathlib import Path


ms_file = str(
    Path(__file__).parent.parent.parent.joinpath("examples", "linux", "binaries", "multiple-styles")
)


class TestResume(unittest.TestCase):
    def test_resume(self):
        m = Manticore(ms_file, stdin_size=17)

        # First instruction of `main`
        @m.hook(0x4009AE)
        def serialize(state):
            with m.locked_context() as context:
                if context.get("kill", False):
                    raise TerminateState("Abandoning...")
                context["kill"] = True
            raise SerializeState("/tmp/ms_checkpoint.pkl")

        m.run()
        self.assertEqual(m.count_terminated_states(), 1)
        for state in m.terminated_states:
            self.assertEqual(state.cpu.PC, 0x4009AE)

        m = Manticore.from_saved_state("/tmp/ms_checkpoint.pkl")
        self.assertEqual(m.count_ready_states(), 1)
        for st in m.ready_states:
            self.assertEqual(state.cpu.PC, 0x4009AE)
        m.run()

        self.assertEqual(m.count_terminated_states(), 18)
        self.assertTrue(
            any("exit status: 0" in str(st._terminated_by) for st in m.terminated_states)
        )
        m.finalize()
        for st in m.terminated_states:
            if "exit status: 0" in str(st._terminated_by):
                self.assertEqual(st.solve_one(st.input_symbols[0]), b"coldlikeminisodas")


if __name__ == "__main__":
    unittest.main()
