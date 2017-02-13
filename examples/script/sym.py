#!/usr/bin/env python

import sys
from core.smtlib.expression import *
from capstone.arm import *
from capstone.x86 import *
from manticore import Manticore

# This example demonstrates creating hooks on arbitrary values of the program
# counter.

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

    if m.arch == 'arm':
        target = (0x1082c, 'R4')
    else:
        target = (0x400a83, 'EBX')

    def entered_func(state):
        '''For ARM, Make R4 symbolic at 0x1082c, as r4 is used in a branch right
           after.
        '''

        cpu = state.cpu

        sym_var = BitVecVariable(32, 'from_callback', taint=())

        # Make destination register symbolic
        setattr(cpu, target[1], sym_var)


    m.add_pc_hook(target[0], entered_func)

    # Start path exploration. start() returns when Manticore finishes
    m.start()

    # Print high level statistics
    #m.dump_stats()

