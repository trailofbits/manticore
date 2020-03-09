#!/usr/bin/env python

"""
A simple trace following execution driver script. Only supports passing symbolic arguments via argv.
"""


import argparse
import itertools
import sys
import time

from manticore import issymbolic
from manticore.core.plugin import ExtendedTracer, Plugin
from manticore.native import Manticore


def _partition(pred, iterable):
    t1, t2 = itertools.tee(iterable)
    return list(itertools.filterfalse(pred, t1)), list(filter(pred, t2))


class TraceReceiver(Plugin):
    def __init__(self, tracer):
        self._trace = None
        self._tracer = tracer
        super().__init__()

    @property
    def trace(self):
        return self._trace

    def will_generate_testcase_callback(self, state, testcase, msg):
        self._trace = state.context[self._tracer.context_key]

        instructions, writes = _partition(lambda x: x["type"] == "regs", self._trace)
        total = len(self._trace)
        print(
            f"Recorded concrete trace: {len(instructions)}/{total} instructions, {len(writes)}/{total} writes"
        )


class Follower(Plugin):
    def __init__(self, trace):
        self.index = 0
        self.trace = trace
        self.last_instruction = None
        self.symbolic_ranges = []
        self.active = True
        super().__init__()

    def add_symbolic_range(self, pc_start, pc_end):
        self.symbolic_ranges.append((pc_start, pc_end))

    def get_next(self, type):
        event = self.trace[self.index]
        assert event["type"] == type
        self.index += 1
        return event

    def did_write_memory_callback(self, state, where, value, size):
        if not self.active:
            return
        write = self.get_next("mem_write")

        if not issymbolic(value):
            return

        assert write["where"] == where and write["size"] == size
        state.constrain(value == write["value"])

    def did_execute_instruction_callback(self, state, last_pc, pc, insn):
        if not self.active:
            return
        event = self.get_next("regs")
        self.last_instruction = event["values"]
        if issymbolic(pc):
            state.constrain(state.cpu.RIP == self.last_instruction["RIP"])
        else:
            for start, stop in self.symbolic_ranges:
                if start <= pc <= stop:
                    self.active = False


def main():
    parser = argparse.ArgumentParser(description="Follow a concrete trace")
    parser.add_argument(
        "-f", "--explore_from", help="Value of PC from which to explore symbolically", type=str
    )
    parser.add_argument(
        "-t",
        "--explore_to",
        type=str,
        default=sys.maxsize,
        help="Value of PC until which to explore symbolically. (Probably don't want this set)",
    )
    parser.add_argument("--verbose", "-v", action="count", default=0, help="Increase verbosity")
    parser.add_argument(
        "cmd",
        type=str,
        nargs="+",
        help='Program and arguments. Use "--" to separate script arguments from target arguments',
    )
    args = parser.parse_args(sys.argv[1:])

    range = None
    if args.explore_from:
        range = (args.explore_from, args.explore_to)

    # Create a concrete Manticore and record it
    m1 = Manticore.linux(args.cmd[0], args.cmd[1:])
    t = ExtendedTracer()
    r = TraceReceiver(t)
    m1.verbosity(args.verbose)
    m1.register_plugin(t)
    m1.register_plugin(r)
    m1.run(procs=1)

    time.sleep(3)

    # Create a symbolic Manticore and follow last trace
    symbolic_args = ["+" * len(arg) for arg in args.cmd[1:]]
    m2 = Manticore.linux(args.cmd[0], symbolic_args)
    f = Follower(r.trace)
    if range:
        f.add_symbolic_range(*range)
    m2.verbosity(args.verbose)
    m2.register_plugin(f)
    m2.run()


if __name__ == "__main__":
    main()
