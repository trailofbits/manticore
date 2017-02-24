#!/usr/bin/env python

import sys
from manticore import Manticore

# This example demonstrates a basic hook (PC register)

if __name__ == '__main__':
    print sys.argv
    path = sys.argv[1]
    pc = int(sys.argv[2], 0)

    m = Manticore(path)

    # Trigger an event when PC reaches a certain value
    @m.hook(pc)
    def reached_goal(state):
        cpu = state.cpu

        assert cpu.PC == pc

        instruction = cpu.read_int(cpu.PC)
        print "Execution goal reached."
        print "Instruction bytes: {:08x}".format(instruction)

    # Start path exploration. m.run() returns when Manticore
    # finishes
    m.run()

