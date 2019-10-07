from manticore.wasm import ManticoreWASM
from manticore.utils.log import set_verbosity

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
