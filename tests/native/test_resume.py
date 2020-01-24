import unittest
from manticore.native import Manticore
from manticore.core.plugin import Plugin
from manticore.core.state import SerializeState, TerminateState
from pathlib import Path


class InsnCounterPlugin(Plugin):
    def did_execute_instruction_callback(self, state, last_pc, pc, instruction):
        with self.locked_context("counter", dict) as ctx:
            val = ctx.setdefault(instruction.mnemonic, 0)
            ctx[instruction.mnemonic] = val + 1


ms_file = str(
    Path(__file__).parent.parent.parent.joinpath("examples", "linux", "binaries", "multiple-styles")
)


class TestResume(unittest.TestCase):
    def test_resume(self):
        m = Manticore(ms_file, stdin_size=18)
        plugin = InsnCounterPlugin()
        m.register_plugin(plugin)
        m.run()

        counts_canonical = plugin.context.get("counter")

        m = Manticore(ms_file, stdin_size=18)
        plugin = InsnCounterPlugin()
        m.register_plugin(plugin)

        @m.hook(0x0400A55)
        def serialize(state):
            with m.locked_context() as context:
                if context.get("kill", False):
                    raise TerminateState("Abandoning...")
                context["kill"] = True
            raise SerializeState("/tmp/ms_checkpoint.pkl")

        m.run()

        counts_save = plugin.context.get("counter")

        m = Manticore.from_saved_state("/tmp/ms_checkpoint.pkl")
        plugin = InsnCounterPlugin()
        m.register_plugin(plugin)
        m.run()

        counts_resume = plugin.context.get("counter")

        for k in counts_canonical:
            with self.subTest(k):
                self.assertEqual(
                    counts_save.get(k, 0) + counts_resume.get(k, 0),
                    counts_canonical[k],
                    f"Mismatched {k} count",
                )


if __name__ == "__main__":
    unittest.main()
