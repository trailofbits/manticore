#!/usr/bin/env python

import sys
from manticore import Manticore

# This example demonstrates the basic high level config
# interface


if __name__ == '__main__':
    path = sys.argv[1]
    bin_args = sys.argv[1:]

    # Create a new Manticore object
    m = Manticore(path, bin_args)

    # Set a few settings
    m.procs = 4
    m.solver = 'z3'
    m.verbosity = 2

    # Start path exploration. start() returns when Manticore
    # finishes
    m.run()

    # Print high level statistics
    m.dump_stats()

