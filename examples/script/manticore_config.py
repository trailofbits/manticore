#!/usr/bin/env python

import sys
from manticore import Manticore

# This example demonstrates the basic high level config
# interface

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

    # Set a few settings
    m.procs = 4
    m.solver = 'z3'

    # Start path exploration. start() returns when Manticore
    # finishes
    m.start()

    # Print high level statistics
    m.dump_stats()

