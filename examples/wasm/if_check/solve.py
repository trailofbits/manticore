from manticore.wasm import ManticoreWASM
from manticore.core.plugin import Plugin


def getchar(state):
    """ Symbolic `getchar` implementation. Returns an arbitrary single byte """
    res = state.new_symbolic_value(32, "getchar_res")
    state.constrain(0 < res)
    state.constrain(res < 256)
    return [res]


class PrintRetPlugin(Plugin):
    """ A plugin that looks for states that returned zero and solves for their inputs """

    def will_terminate_state_callback(self, state, *args):
        retval = state.stack.peek()
        if retval == 0:
            print("Solution found!")
            for sym in state.input_symbols:
                solved = state.solve_one(sym)
                print(f"{sym.name}: {chr(solved)} --> Return {retval}")


# Pass our symbolic implementation of the `getchar` function into the WASM environment
# as an import.
m = ManticoreWASM("if_check.wasm", env={"getchar": getchar})

# Register our state termination callback
m.register_plugin(PrintRetPlugin())

# Run the main function, which will call getchar
m.main()

# Save a copy of the inputs to the disk
m.finalize()
