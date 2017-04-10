#!/usr/bin/env python

import sys
from manticore import Manticore

'''
Minimal example demonstrating setting execution hooks, the ability to target
multiple target architectures, and symbolicating memory.
'''

if __name__ == '__main__':

    if len(sys.argv) < 2:
        print "Usage: {} [binary] [arguments]".format(sys.argv[0])
        sys.exit(1)

    # Create a new Manticore object
    m = Manticore(sys.argv[1], sys.argv[2:])

    if m.arch == 'arm':
        target = (0x1082c, 'R4')
    else:
        target = (0x400a83, 'EBX')

    @m.hook(target[0])
    def entered_func(state):
        '''
        For ARM, Make R4 symbolic at 0x1082c, as r4 is used in a branch right
        after.
        '''
        sym_var = state.new_symbolic_value(32, label='from_callback')
        state.cpu.write_register(target[1], sym_var)

    # Start path exploration. start() returns when Manticore finishes
    m.verbosity = 2
    m.run()

    # Print high level statistics
    m.dump_stats()

