import unittest
from manticore.wasm import ManticoreWASM
from manticore.wasm.types import I32
from manticore.core.plugin import Plugin
from manticore.core.state import SerializeState, TerminateState
from pathlib import Path


class CallCounterPlugin(Plugin):
    def did_execute_instruction_callback(self, state, instruction):
        with self.locked_context("counter", dict) as ctx:
            val = ctx.setdefault(instruction.mnemonic, 0)
            ctx[instruction.mnemonic] = val + 1


class SerializerPlugin(Plugin):
    killed = False

    def did_execute_instruction_callback(self, state, instruction):
        if self.killed:
            raise TerminateState("Abandoning")
        with self.locked_context("counter", dict) as ctx:
            if instruction.mnemonic == "loop" and ctx.get(instruction.mnemonic, 0) == 24:
                self.killed = True
                raise SerializeState("/tmp/collatz_checkpoint.pkl")
            val = ctx.setdefault(instruction.mnemonic, 0)
            ctx[instruction.mnemonic] = val + 1


collatz_file = str(
    Path(__file__).parent.parent.parent.joinpath("examples", "wasm", "collatz", "collatz.wasm")
)


class TestResume(unittest.TestCase):
    def test_resume(self):
        m = ManticoreWASM(collatz_file)
        plugin = CallCounterPlugin()
        m.register_plugin(plugin)
        m.collatz(lambda s: [I32(1337)])
        m.run()

        counts_canonical = plugin.context.get("counter")

        m = ManticoreWASM(collatz_file)
        plugin = SerializerPlugin()
        m.register_plugin(plugin)
        m.collatz(lambda s: [I32(1337)])
        m.run()

        counts_save = plugin.context.get("counter")

        m = ManticoreWASM.from_saved_state("/tmp/collatz_checkpoint.pkl")
        plugin = CallCounterPlugin()
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

        results = []
        for idx, val_list in enumerate(m.collect_returns()):
            results.append(val_list[0][0])

        self.assertEqual(sorted(results), [44])


if __name__ == "__main__":
    unittest.main()
