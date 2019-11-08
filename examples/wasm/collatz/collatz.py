"""
Three different ways of evaluating the Collatz conjecture.

Example 1: Pass a symbolic argument to the `collatz` function
Example 2: Pass a symbolic version of `getchar` as an imported function
Example 3: Concretely evaluate `collatz(1337)` and count the instructions executed

See: examples/collatz.c
"""

from manticore.wasm import ManticoreWASM
from manticore.wasm.types import I32
from manticore.core.plugin import Plugin
from manticore.utils.log import set_verbosity


print(
    """

============ Example 1 ============
"""
)

m = ManticoreWASM("collatz.wasm")
set_verbosity(2)


def arg_gen(state):
    # Generate a symbolic argument to pass to the collatz function.
    # Possible values: 4, 6, 8
    arg = state.new_symbolic_value(32, "collatz_arg")
    state.constrain(arg > 3)
    state.constrain(arg < 9)
    state.constrain(arg % 2 == 0)
    return [arg]


# Set up Manticore to run the collatz function with the given argument generator.
# We use an argument generator function instead of a list of arguments because Manticore
# might have multiple states waiting to begin execution, and we can conveniently map a
# generator function over all the ready states and get access to their respective
# constraint sets.
m.invoke("collatz", arg_gen)

# Run the collatz function
m.run()

# Manually collect return values
for idx, val_list in enumerate(m.collect_returns()):
    print("State", idx, "::", val_list[0])

# Finalize the run (dump testcases)
m.finalize()


print(
    """

============ Example 2 ============
"""
)


def getchar(constraints, _addr):
    """
    Stub implementation of the getchar function. All WASM cares about is that it accepts the right
    number of arguments and returns the correct type. All _we_ care about is that it returns a symbolic
    value, for which Manticore will produce all possible outputs.

    :param constraints: The current constraint set
    :param _addr: Memory index of the string that gets printed by getchar
    :return: A symbolic value of the interval [1, 7]
    """
    res = constraints.new_bitvec(32, "getchar_res")
    constraints.add(res > 0)
    constraints.add(res < 8)
    return [res]


# Pass our symbolic implementation of the `getchar` function into the WASM environment
# as an import.
m = ManticoreWASM("collatz.wasm", env={"getchar": getchar})

# Invoke the main function, which will call getchar
m.invoke("main")

# Run the example
m.run()

# Manually collect return values
for idx, val_list in enumerate(m.collect_returns()):
    print("State", idx, "::", val_list[0])

# Finalize the run (dump testcases)
m.finalize()


print(
    """

============ Example 3 ============
"""
)


class CounterPlugin(Plugin):
    """
    A plugin that counts the number of times each instruction occurs
    """

    def did_execute_instruction_callback(self, state, instruction):
        with self.locked_context("counter", dict) as ctx:
            val = ctx.setdefault(instruction.mnemonic, 0)
            ctx[instruction.mnemonic] = val + 1

    def did_terminate_state_callback(self, state, *args):
        insn_sum = 0
        with self.locked_context("counter") as ctx:
            for mnemonic, count in sorted(ctx.items(), key=lambda x: x[1], reverse=True):
                print("{: <10} {: >4}".format(mnemonic, count))
                insn_sum += count
        print(insn_sum, "instructions executed")


def arg_gen(_state):
    return [I32(1337)]


m = ManticoreWASM("collatz.wasm")

# Registering the plugin connects its callbacks to the correct events
m.register_plugin(CounterPlugin())

# Invoke `collatz(1337)`
m.invoke("collatz", arg_gen)

# Run the collatz function
m.run()

# Manually collect return values
for idx, val_list in enumerate(m.collect_returns()):
    print("State", idx, "::", val_list[0])

# Finalize the run (dump testcases)
m.finalize()
