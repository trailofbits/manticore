import unittest
from manticore.wasm import ManticoreWASM
from manticore.wasm.types import I32
from manticore.core.plugin import Plugin
from pathlib import Path


def getchar(constraints, addr):
    res = constraints.new_bitvec(32, "getchar_res")
    constraints.add(res > 0)
    constraints.add(res < 8)
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

    def test_plugin(self):
        def arg_gen(_state):
            return [I32(1337)]

        m = ManticoreWASM(wasm_file)
        plugin = CallCounterPlugin()
        m.register_plugin(plugin)
        m.invoke("collatz", arg_gen)
        m.run()

        # counts = m.context.get("<class 'test_examples.CallCounterPlugin'>").get("counter")
        counts = plugin.context.get("counter")

        self.assertEqual(counts["br_if"], 45)
        self.assertEqual(counts["loop"], 44)
        self.assertEqual(counts["i32.add"], 88)

        results = []
        for idx, val_list in enumerate(m.collect_returns()):
            results.append(val_list[0][0])

        self.assertEqual(sorted(results), [44])


if __name__ == "__main__":
    unittest.main()
