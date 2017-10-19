#!/usr/bin/env python

import sys
import time
import struct
import itertools

from manticore import Manticore
from manticore import models
from manticore.core.plugin import ExtendedTracer, Follower, Plugin

def partition(pred, iterable):
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

        instructions, writes = partition(lambda x: x['type'] == 'regs', self._trace)
        total = len(self._trace)
        print 'Recorded concrete trace: {}/{} instructions, {}/{} writes'.format(
            len(instructions), total, len(writes), total)



# Create a concrete Manticore and record it
m1 = Manticore.linux(sys.argv[1], ['--first', '--second', '-a', '123'])
t = ExtendedTracer()
r = TraceReceiver(t)
m1.verbosity(2)
m1.register_plugin(t)
m1.register_plugin(r)
m1.run()

time.sleep(10)

# Create a symbolic Manticore and follow last trace
m2 = Manticore.linux(sys.argv[1], ['+++++++', '++++++++', '++', '+++'])
f = Follower(r.trace)
f.add_symbolic_range(0x400b22, 0x400ba7)
m2.register_plugin(f)
m2.verbosity(2)
m2.run()
