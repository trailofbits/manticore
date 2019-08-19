#!/usr/bin/env python

import sys

from manticore.native.plugins import Merger
from manticore.utils import config

from manticore.native import Manticore
from manticore import set_verbosity

"""
Demonstrates the ability to do state merging on a simple program by merging states with id 2, 4 that happen to be 
at the same program location 0x40060d. This script uses the Merger plugin to apply opportunistic state merging.
"""
if __name__ == "__main__":
    config.get_group("core").seed = 2
    config.get_group("core").mprocessing = config.get_group("core").mprocessing.single
    path = sys.argv[1]
    m = Manticore(path, policy="random")

    def will_load_state_callback(_mc, state_id):
        print("about to load state_id = " + str(state_id))

    def did_load_state_callback(_mc, state):
        print("loaded state_id = " + str(state.id) + " at cpu = " + hex(state.cpu.PC))

    m.subscribe("will_load_state", will_load_state_callback)
    m.subscribe("did_load_state", did_load_state_callback)
    m.register_plugin(Merger())
    m.run()
