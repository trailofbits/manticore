#!/usr/bin/env python

import sys
import time
import struct
import itertools

from manticore import Manticore
from manticore.core.plugin import ExtendedTracer, Plugin
from manticore.utils.helpers import issymbolic
from manticore.core.smtlib import Operators

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

t = ExtendedTracer()
r = TraceReceiver(t)

m = Manticore.linux(sys.argv[1], concrete_start=struct.pack('<I', 0x34))
m.register_plugin(t)
m.register_plugin(r)
m.run()

time.sleep(10)

# -----------------------------------------------------------------------------

class Follower(Plugin):
    def __init__(self, trace):
        self.index = 0
        self.trace = trace
        self.last_instruction = None
        super(self.__class__, self).__init__()

    def get_next_instruction(self):
        while self.trace[self.index]['type'] != 'regs':
            self.index += 1
        self.last_instruction = self.trace[self.index]['values']
        self.index += 1
        return self.last_instruction

    def will_fork_state_callback(self, state, expression, solutions, policy):
        print 'Forking, constraining PC to {:x}'.format(self.last_instruction['RIP'])
        state.constrain(state.cpu.RIP == self.last_instruction['RIP'])

    def get_intermediate_writes(self):
        writes = []
        start = self.index
        while self.trace[start]['type'] == 'mem_write':
            writes.append(self.trace[start])
            start += 1
        return writes

    def did_write_memory_callback(self, state, where, value, size):
        if issymbolic(value):
            writes = self.get_intermediate_writes()
            for w in writes:
                if w['where'] != where:
                    continue
                assert w['size'] == size
                symval = state.new_symbolic_value(size, label='concrete_{}'.format(self.index))
                state.constrain(symval == w['value'])
                #state.cpu.write_int(where, symval, size)

                # Copied from Cpu.write_int to not emit another write_memory event
                state.cpu.memory[where:where+size/8] = \
                    [Operators.CHR(Operators.EXTRACT(symval, offset, 8)) for offset in xrange(0, size, 8)]

    def did_execute_instruction_callback(self, state, last_pc, pc, insn):
        val = self.get_next_instruction()
        if issymbolic(pc):
            print val
            state.constrain(state.cpu.RIP == val['RIP'])

f = Follower(r.trace)
skip = True
m = Manticore.linux(sys.argv[1])
m.register_plugin(f)
m.verbosity(2)

#@m.hook(None)
#def follow(state):
#    global skip
#    if skip: skip = False; return
#    f.index += 1

m.run()
