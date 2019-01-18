#!/usr/bin/env python

import sys

from manticore.core.plugin import Merger
from manticore.utils import config

from manticore.native import Manticore
'''
Demonstrates the ability to do state merging on a simple program by merging states with id 2, 4 that happen to be 
at the same program location 0x40060d. This script uses the Merger plugin to apply opportunistic state merging.
'''
if __name__ == '__main__':
    consts = config.get_group('executor')
    consts.seed = 2
    path = sys.argv[1]
    m = Manticore(path, policy='random')

    def will_load_state_callback(_, state_id):
        print("about to load state_id = " + str(state_id))

    def did_load_state_callback(_, state, state_id):
        print("loaded state_id = " + str(state_id) + " at cpu = " + hex(state.cpu.PC))

    m.subscribe('will_load_state', will_load_state_callback)
    m.subscribe('did_load_state', did_load_state_callback)
    m.register_plugin(Merger())
    m.run()

