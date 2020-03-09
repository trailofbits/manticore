#!/usr/bin/env python

import sys
from manticore.native import Manticore

"""
Demonstrates the ability to guide Manticore's state exploration. In this case,
abandoning a state we're no longer interested in.

Usage:

 $ gcc -static -g src/state_explore.c -o state_explore # -static is optional
 $ ADDRESS=0x$(objdump -S state_explore | grep -A 1 'value == 0x41' | tail -n 1 | sed 's|^\s*||g' | cut -f1 -d:)
 $ python ./state_control.py state_explore $ADDRESS

"""

if __name__ == "__main__":
    if len(sys.argv) < 3:
        sys.stderr.write(f"Usage: {sys.argv[0]} [binary] [address]\n")
        sys.exit(2)

    m = Manticore(sys.argv[1])

    # Uncomment to see debug output
    # m.verbosity = 2

    # Set to the address of the conditional at state_explore.c:38, which will be
    # abandoned. If line 36 of this script is commented out, Manticore will
    # explore all reachable states.
    to_abandon = int(sys.argv[2], 0)

    @m.hook(to_abandon)
    def explore(state):
        print(f"Abandoning state at PC: {state.cpu.PC:x}")
        state.abandon()

    print(f"Adding hook to: {to_abandon:x}")

    m.run()
