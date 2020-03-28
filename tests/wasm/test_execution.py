import unittest
from manticore.wasm import ManticoreWASM
from manticore.wasm.types import Value_t
from pathlib import Path


test_if_file = str(Path(__file__).parent.joinpath("inputs", "if.wasm"))
test_br_if_file = str(Path(__file__).parent.joinpath("inputs", "br_if.wasm"))


class TestSymbolicBranch(unittest.TestCase):
    def can_terminate_with(self, val, state):
        stack = state.platform.stack
        assert stack.has_type_on_top(Value_t, 1)
        result = stack.peek()

        input_arg = state.context["arg"]
        return state.can_be_true(result == val)

    def test_if(self):
        m = ManticoreWASM(test_if_file)

        def arg_gen(state):
            arg = state.new_symbolic_value(32, "arg")
            state.context["arg"] = arg
            return [arg]

        m.main(arg_gen)
        m.run()

        assert any((self.can_terminate_with(0, state) for state in m.terminated_states))

    def test_br_if(self):
        m = ManticoreWASM(test_br_if_file)

        def arg_gen(state):
            arg = state.new_symbolic_value(32, "arg")
            state.context["arg"] = arg
            return [arg]

        m.main(arg_gen)
        m.run()

        assert any((self.can_terminate_with(0, state) for state in m.terminated_states))


if __name__ == "__main__":
    unittest.main()
