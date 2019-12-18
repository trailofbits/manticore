import unittest
from manticore.wasm import ManticoreWASM
from manticore.wasm.cli import wasm_main
from manticore.wasm.types import I32
from manticore.core.plugin import Plugin
from manticore.utils import config
from pathlib import Path
from collections import namedtuple
import glob
import time


def getchar(state, addr):
    res = state.new_symbolic_value(32, "getchar_res")
    state.constrain(res > 0)
    state.constrain(res < 8)
    return [res]


def arg_gen(state):
    arg = state.new_symbolic_value(32, "collatz_arg")
    state.constrain(arg > 3)
    state.constrain(arg < 9)
    state.constrain(arg % 2 == 0)
    return [arg]


class CallCounterPlugin(Plugin):
    def did_execute_instruction_callback(self, state, instruction):
        with self.locked_context("counter", dict) as ctx:
            val = ctx.setdefault(instruction.mnemonic, 0)
            ctx[instruction.mnemonic] = val + 1


wasm_file = str(
    Path(__file__).parent.parent.parent.joinpath("examples", "wasm", "collatz", "collatz.wasm")
)


class TestExamples(unittest.TestCase):
    def test_getchar(self):
        m = ManticoreWASM(wasm_file, env={"getchar": getchar})
        m.invoke("main")
        m.run()
        results = []
        for idx, val_list in enumerate(m.collect_returns()):
            results.append(val_list[0][0])

        self.assertEqual(sorted(results), [0, 1, 2, 5, 7, 8, 16])

    def test_symbolic_args(self):
        m = ManticoreWASM(wasm_file, env={})
        m.invoke("collatz", arg_gen)
        m.run()

        results = []
        for idx, val_list in enumerate(m.collect_returns()):
            results.append(val_list[0][0])

        self.assertEqual(sorted(results), [2, 3, 8])

        m.finalize()

        inputs = []
        for fn in glob.glob(m.workspace + "/*.input"):
            with open(fn, "r") as f:
                raw = f.read().strip()
                inputs.append(int(raw.replace("collatz_arg: ", "")))

        self.assertEqual(sorted(inputs), [4, 6, 8])

    def test_plugin(self):
        def arg_gen(_state):
            return [I32(1337)]

        m = ManticoreWASM(wasm_file)
        counter_plugin = CallCounterPlugin()
        m.register_plugin(counter_plugin)
        m.invoke("collatz", arg_gen)
        m.run()

        # counts = m.context.get("<class 'test_examples.CallCounterPlugin'>").get("counter")
        counts = counter_plugin.context.get("counter")

        self.assertEqual(counts["br_if"], 45)
        self.assertEqual(counts["loop"], 44)
        self.assertEqual(counts["i32.add"], 88)

        results = []
        for idx, val_list in enumerate(m.collect_returns()):
            results.append(val_list[0][0])

        self.assertEqual(sorted(results), [44])

    def test_implicit_call(self):
        m = ManticoreWASM(wasm_file)
        counter_plugin = CallCounterPlugin()
        m.register_plugin(counter_plugin)
        m.collatz(lambda s: [I32(1337)])

        counts = counter_plugin.context.get("counter")

        self.assertEqual(counts["br_if"], 45)
        self.assertEqual(counts["loop"], 44)
        self.assertEqual(counts["i32.add"], 88)

        results = []
        for idx, val_list in enumerate(m.collect_returns()):
            results.append(val_list[0][0])

        self.assertEqual(sorted(results), [44])

    def test_wasm_main(self):
        """Doesn't check the output, just that the main function runs and doesn't error"""
        start = time.time()
        config.get_group("cli").add("profile", False)
        wasm_main(
            namedtuple("Args", ["argv", "workspace", "policy"])([wasm_file], "/tmp", "ALL"), None
        )
        self.assertGreaterEqual(
            time.time() - start,
            0.2,
            "Running the Collatz example should probably take more than 0.2 seconds.",
        )


if __name__ == "__main__":
    unittest.main()
