#!/usr/bin/env python

import sys
from manticore.native import Manticore

"""
Demonstrates the ability to set a basic hook on a specific program counter and
the ability to read from memory.
"""

if __name__ == "__main__":
    path = sys.argv[1]
    pc = int(sys.argv[2], 0)

    m = Manticore(path)

    # Trigger an event when PC reaches a certain value
    @m.hook(pc)
    def reached_goal(state):
        cpu = state.cpu

        assert cpu.PC == pc

        instruction = cpu.read_int(cpu.PC)
        print("Execution goal reached.")
        print(f"Instruction bytes: {instruction:08x}")

    m.run()
