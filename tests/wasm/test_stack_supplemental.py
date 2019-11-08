import unittest
from manticore.wasm import ManticoreWASM
from manticore.wasm.types import I32
from manticore.core.plugin import Plugin
from manticore.wasm.structure import Stack, AtomicStack

from pathlib import Path


class StackTrackerPlugin(Plugin):
    def will_pop_item_callback(self, state, depth):
        with self.locked_context("push_pop_seq", list) as seq:
            seq.append("+")

    def did_pop_item_callback(self, state, item, depth):
        with self.locked_context("push_pop_seq", list) as seq:
            seq.append("-")


wasm_file = str(
    Path(__file__).parent.parent.parent.joinpath("examples", "wasm", "collatz", "collatz.wasm")
)


class TestStack(unittest.TestCase):
    def test_trace(self):
        """
        This checks the sequence of pushes and pops that take place during an example execution.
        That sequence isn't meant to be invariant, so if you change the implementation and break
        this test, by all means, replace it with the new sequence.
        :return:
        """

        def arg_gen(_state):
            return [I32(1337)]

        m = ManticoreWASM(wasm_file)
        tracker_plugin = StackTrackerPlugin()
        m.register_plugin(tracker_plugin)
        m.invoke("collatz", arg_gen)
        m.run()

        results = []
        for idx, val_list in enumerate(m.collect_returns()):
            results.append(val_list[0][0])

        self.assertEqual(sorted(results), [44])
        push_pop_seq = "".join(tracker_plugin.context.get("push_pop_seq"))

        self.assertEqual(push_pop_seq, "+-" * 892)

    def test_has_at_least(self):
        s = Stack()
        s.push(I32(1))
        self.assertFalse(s.has_at_least(I32, 2))
        s.push(I32(2))
        self.assertTrue(s.has_at_least(I32, 2))

    def test_empty(self):
        s = Stack()
        with AtomicStack(s) as a:
            a.push(1)
            a.push(2)

            self.assertEqual(len(s.data), 2)
            self.assertFalse(a.empty())
            a.pop()
            a.pop()

            self.assertTrue(a.empty())
        self.assertTrue(s.empty())

    def test_rollback(self):
        orig = [i for i in range(10)]

        s = Stack()
        for i in range(10):
            s.push(i)
        a = AtomicStack(s)
        self.assertEqual(list(s.data), orig)

        a.push(10)
        self.assertEqual(list(s.data), [i for i in range(11)])

        a.rollback()
        self.assertEqual(list(s.data), orig)

        for i in range(3):
            a.pop()
        self.assertEqual(list(s.data), [i for i in range(7)])

        a.rollback()
        self.assertEqual(list(s.data), orig)

        a.pop()
        a.pop()
        for i in range(9):
            a.push(20 + i)
        a.pop()
        a.pop()
        for i in range(5):
            a.push(30 + i)

        self.assertEqual(
            list(s.data), [0, 1, 2, 3, 4, 5, 6, 7, 20, 21, 22, 23, 24, 25, 26, 30, 31, 32, 33, 34]
        )

        a.rollback()
        self.assertEqual(list(s.data), orig)


if __name__ == "__main__":
    unittest.main()
