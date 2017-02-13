#!/usr/bin/env python

import sys
from manticore import Manticore

# This example demonstrates a basic hook (PC register)

def get_args():
    class Args(object): pass
    args = Args()
    args.replay = None; args.data = ''; args.dumpafter = 0; args.maxstates = 0;
    args.maxstorage = 0; args.stats = True; args.verbose = False; args.log = '-';
    return args

if __name__ == '__main__':
    path = sys.argv[1]
    args = get_args()

    args.programs = sys.argv[1:]
    # Create a new Manticore object
    m = Manticore(None, path, args)

    # Trigger an event when PC reaches a certain value
    def reached_goal(state):
        cpu = state.cpu

        assert cpu.pc == 0x10858

        instruction = cpu.read(cpu.pc, 4)
        print "Execution goal reached."
        print "Instruction bytes: {:08x}".format(cpu.pc)

    m.add_pc_hook(0x10858, reached_goal)

    # Start path exploration. start() returns when Manticore
    # finishes
    m.start()

