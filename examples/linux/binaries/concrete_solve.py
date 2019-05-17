from manticore import Manticore


def fixme():
    raise Exception("Fill in the blanks!")


# Let's initialize the manticore control object
m = Manticore("multiple-styles")

# First, let's give it some fake data for the input. Anything the same size as
# the real flag should work fine!
m.concrete_data = "infiltrate miami!"

# Now we're going to want to execute a few different hooks and share data, so
# let's use the m.context dict to keep our solution in
m.context["solution"] = ""

# Now we want to hook that compare instruction that controls the main loop.
# Where is it again?
@m.hook(fixme())
def solve(state):
    # Our actual flag should have something to do with AL at this point, let's
    # just read it out real quick
    flag_byte = state.cpu.AL - fixme()

    m.context["solution"] += chr(flag_byte)

    # But how can we make the comparison pass? There are a couple solutions here
    fixme()


# play with these numbers!
m.verbosity = 0
procs = 1

m.run(procs)
print(m.context["solution"])
