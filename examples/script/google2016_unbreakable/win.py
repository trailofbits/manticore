from manticore import Manticore

"""
Leverages Manticore to solve the Google 2016 challenge: 
unbreakable-enterprise-product-activation

Author: @ctfhacker
Binary: https://github.com/ctfs/write-ups-2016/blob/master/google-ctf-2016/reverse/unbreakable-enterprise-product-activation-150/unbreakable-enterprise-product-activation.bz2
"""

m = Manticore('unbreakable')

"""
These values can be found at 0x4005b8
"""
input_addr = 0x6042c0
num_bytes = 0x43

# Entry point
@m.hook(0x400729)
def hook(state):
    """ CAUTION: HACK """
    """ From entry point, jump directly to code performing check """

    # Create a symbolic buffer for our input
    buffer = state.new_symbolic_buffer(0x43)

    # We are given in the challenge that the flag begins with CTF{
    # So we can apply constraints to ensure that is true
    state.constraints.add(buffer[0] == ord('C'))
    state.constraints.add(buffer[1] == ord('T'))
    state.constraints.add(buffer[2] == ord('F'))
    state.constraints.add(buffer[3] == ord('{'))

    # Store our symbolic input in the global buffer read by the check
    state.cpu.write_bytes(input_addr, buffer)

    # By default, `hook` doesn't patch the instruction, so we hop over
    # the hooked strncpy and execute the next instruction
    state.cpu.EIP = 0x4005bd

# Failure case
@m.hook(0x400850)
def hook(state):
    """ Stop executing paths that reach the `failure` function"""
    print("Invalid path.. abandoning")
    state.abandon()

# Success case
@m.hook(0x400724)
def hook(state):
    print("Hit the final state.. solving")

    buffer = state.cpu.read_bytes(input_addr, num_bytes)
    res = ''.join(chr(state.solve_one(x)) for x in buffer)
    print(res) # CTF{0The1Quick2Brown3Fox4Jumped5Over6The7Lazy8Fox9}

    # We found the flag, no need to continue execution
    m.terminate()

m.workers = 10
m.run()
