#!/usr/bin/env python

import sys

from manticore import Manticore

'''
Solves modified version of baby-re, compiled for arm.
'''

if __name__ == '__main__':
    path = sys.argv[1]
    m = Manticore(path)

    @m.hook(0x109f0)
    def myhook(state):
        flag = ''
        cpu = state.cpu
        arraytop = cpu.R11
        base = arraytop - 0x18
        for i in xrange(4):
            symbolic_input = cpu.read_int(base + i*4)
            # TODO apis to contrain input to ascii
            concrete_input = state.solve_one(symbolic_input)
            flag += chr(concrete_input & 0xff)
        print 'flag is:', flag
        m.terminate()

    m.run()
