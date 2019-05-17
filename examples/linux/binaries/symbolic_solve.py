from manticore import Manticore


def fixme():
    raise Exception("Fill in the blanks!")


# Let's initialize the manticore control object
m = Manticore("multiple-styles")

# Now, we can hook the success state and figure out the flag! `fixme()` here
# should be an address we'd like to get to
@m.hook(fixme())
def solve(state):
    # Where is the flag in memory? It's probably offset from the base pointer
    # somehow
    flag_base = state.cpu.RBP - fixme()

    # We're going to build a solution later
    solution = ""

    # How big is the flag? We should be able to figure this out from traditional
    # static analysis
    for i in range(fixme()):
        # We can get the symbolic flag out
        symbolic_character = state.cpu.read_int(flag_base + i, 8)
        # And now we just need to solve for it in z3. How might we do that?
        # Perhaps `grep -r "def solve" manticore` can help our case
        concrete_character = fixme()
        solution += chr(concrete_character)

    # And this should give us a solution, after which we're done!
    print(solution)
    m.terminate()


# play with these numbers!
m.verbosity = 0
procs = 1

m.run(procs)
