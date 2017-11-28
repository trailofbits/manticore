#!/usr/bin/env python

'''
A simple trace following execution driver script. Only supports passing symbolic arguments via argv.

'''

import sys
import time
import argparse
import itertools

from manticore import Manticore
from manticore.core.plugin import ExtendedTracer, Follower, Plugin

def _partition(pred, iterable):
    t1, t2 = itertools.tee(iterable)
    return (list(itertools.ifilterfalse(pred, t1)), filter(pred, t2))

class TraceReceiver(Plugin):
    def __init__(self, tracer):
        self._trace = None
        self._tracer = tracer
        super(self.__class__, self).__init__()

    @property
    def trace(self):
        return self._trace

    def will_generate_testcase_callback(self, state, test_id, msg):
        self._trace = state.context[self._tracer.context_key]

        instructions, writes = _partition(lambda x: x['type'] == 'regs', self._trace)
        total = len(self._trace)
        print 'Recorded concrete trace: {}/{} instructions, {}/{} writes'.format(
            len(instructions), total, len(writes), total)



def main():
    parser = argparse.ArgumentParser(description='Follow a concrete trace')
    parser.add_argument('-f', '--explore_from', help='Value of PC from which to explore symbolically', type=str)
    parser.add_argument('-t', '--explore_to', type=str, default=sys.maxint,
                        help="Value of PC until which to explore symbolically. (Probably don't want this set)")
    parser.add_argument('--verbose', '-v', action='count', help='Increase verbosity')
    parser.add_argument('cmd', type=str, nargs='+',
                        help='Program and arguments. Use "--" to separate script arguments from target arguments')
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
    symbolic_args = ['+'*len(arg) for arg in args.cmd[1:]]
    m2 = Manticore.linux(args.cmd[0], symbolic_args)
    f = Follower(r.trace)
    if range:
        f.add_symbolic_range(*range)
    m2.verbosity(args.verbose)
    m2.register_plugin(f)
    m2.run()

if __name__=='__main__':
    main()
