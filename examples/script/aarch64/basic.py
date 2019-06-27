#!/usr/bin/env python3

import os
import struct
import sys

from manticore.native import Manticore

# Examples:
# printf "\x41\x00\x00\x00" | PYTHONPATH=. ./examples/script/aarch64/basic.py
# printf "++\x00\x00"       | PYTHONPATH=. ./examples/script/aarch64/basic.py
# printf "++++"             | PYTHONPATH=. ./examples/script/aarch64/basic.py
# printf "ffffff"           | PYTHONPATH=. ./examples/script/aarch64/basic.py

DIR = os.path.dirname(__file__)
FILE = os.path.join(DIR, "basic")
STDIN = sys.stdin.readline()

# Avoid writing anything to 'STDIN' here.  Do it in the 'init' hook as that's
# more flexible.
m = Manticore(FILE, concrete_start="", stdin_size=0)


@m.init
def init(state):
    state.platform.input.write(state.symbolicate_buffer(STDIN, label="STDIN"))


# Hook the 'if' case.
@m.hook(0x4006BC)
def hook_if(state):
    print("hook if")
    state.abandon()


# Hook the 'else' case.
@m.hook(0x4006CC)
def hook_else(state):
    print("hook else")
    # See how the constraints are affected by input.
    print_constraints(state, 6)

    w0 = state.cpu.W0

    if isinstance(w0, int):  # concrete
        print(hex(w0))
    else:
        print(w0)  # symbolic

    solved = state.solve_one(w0)
    print(struct.pack("<I", solved))


# Hook 'puts' in the 'else' case.
@m.hook(0x4006D4)
def hook_puts(state):
    print("hook puts")
    cpu = state.cpu
    print(cpu.read_string(cpu.X0))


def print_constraints(state, nlines):
    i = 0
    for c in str(state.constraints).split("\n"):
        if i >= nlines:
            break
        print(c)
        i += 1


m.run()
