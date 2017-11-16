#!/usr/bin/env python

'''
A simple concolic execution driver script. Only currently supports passing symbolic arguments via argv.

'''

import sys
import time
import argparse
import itertools

from manticore import Manticore
from manticore.core.plugin import ExtendedTracer, Follower, Plugin
from manticore.core.smtlib.constraints import ConstraintSet
from manticore.core.smtlib import Z3Solver, solver
from manticore.core.smtlib.visitors  import pretty_print as pp

import copy
from manticore.core.smtlib.expression import *

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

def flip(constraint):
    '''
    flips a constraint (Equal)
    '''
    c = copy.deepcopy(constraint)
    
    # assume they are the equal -> ite form that we produce on standard branches
    assert len(c.operands) == 2
    a, forcepc = c.operands
    assert isinstance(a, BitVecITE) and isinstance(forcepc, BitVecConstant)

    assert len(a.operands) == 3
    cond, iifpc, eelsepc = a.operands
    assert isinstance(iifpc, BitVecConstant) and isinstance(eelsepc, BitVecConstant)

    # print 'forcepc is', hex(forcepc.value)
    # print 'iifpc is', hex(iifpc.value)
    # print 'eelsepc is', hex(eelsepc.value)

    if forcepc.value == iifpc.value:
        # print 'setting forcepc to', eelsepc.value
        # forcepc = eelsepc
        c.operands[1] = eelsepc
    else:
        c.operands[1] = iifpc
    
    # print 'NEW C'
    # print pp(c)
    # print '-'*33

    return c

def eq(a, b):
    # this ignores checking the conditions, only checks the 2 possible pcs
    # the one that it is forced to

    ite1, force1 = a.operands
    ite2, force2 = b.operands

    if force1.value != force2.value:
        return False

    _, first1, second1 = ite1.operands
    _, first2, second2 = ite1.operands

    if first1.value != first2.value:
        return False
    if second1.value != second2.value:
        return False

    return True
    

def eqls(a, b):
	# a b and 2 iterables of branch constraints
    for aa, bb in zip(a, b):
        if not eq(aa, bb):
            return False
    return True



def permu(cons, includeself):
    first = cons[0]
    first_flipped = flip(cons[0])
    
    if len(cons) == 1:
        if includeself:
            return [[first], [first_flipped]]
        else:
            return [[first_flipped]]
    ret = []
    others = permu(cons[1:], True)
    for o in others:
        add = [first] + o
        if includeself:
            ret.append(add)
        elif not eqls(add, cons):
            ret.append(add)
    for o in others:
        ret.append([first_flipped] + o)
    return ret




# def permu(constupl):
#     '''
#     takes tuple of constraints (Equal)s
#     returns list of tuples


#     takes constraint set. returns a new one where each constraint 
#     returns a list of constraints sets where 
#     '''

#     ret = []
#     for i, c in enumerate(constupl):
#         conscopy = list(copy.deepcopy(constupl)) # possibly not necessary
#         conscopy[i] = flip(c)
#         ret.append(tuple(conscopy))
#     return ret

def newcs(constupl):
    x = ConstraintSet()
    x._constraints = list(constupl)
    return x



def input_from_cons(constupl, datas):
    newset = newcs(constupl)
    # newset = ConstraintSet()
    # # probably some unnecessary conversion bt lists and tuples
    # newset._constraints = list(constupl)

    ret = ''

    for data in datas:
        for c in data:
            ret += chr(solver.get_value(newset, c))

    return ret


def main():
    # parser = argparse.ArgumentParser(description='Follow a concrete trace')
    # parser.add_argument('-f', '--explore_from', help='Value of PC from which to explore symbolically', type=str)
    # parser.add_argument('-t', '--explore_to', type=str, default=sys.maxint,
    #                     help="Value of PC until which to explore symbolically. (Probably don't want this set)")
    # parser.add_argument('--verbose', '-v', action='count', help='Increase verbosity')
    # parser.add_argument('cmd', type=str, nargs='+',
    #                     help='Program and arguments. Use "--" to separate script arguments from target arguments')
    # args = parser.parse_args(sys.argv[1:])

    # range = None
    # if args.explore_from:
    #     range = (args.explore_from, args.explore_to)

    # Create a concrete Manticore and record it
    #

    # todo randomly generated concrete start

    # prog = sys.argv[1]
    prog = 'basic'

    import random, struct
    # a = struct.pack('<I', random.randint(0, 10))
    # b = struct.pack('<I', random.randint(0, 10))
    # c = struct.pack('<I', random.randint(0, 10))
    a = struct.pack('<I', 0)
    b = struct.pack('<I', 5)
    c = struct.pack('<I', 0)
    xx = a + b + c

    m1 = Manticore.linux(prog, concrete_start=xx)
    t = ExtendedTracer()
    r = TraceReceiver(t)
    m1.verbosity(2)
    m1.register_plugin(t)
    m1.register_plugin(r)
    m1.run(procs=1)


    # time.sleep(3)

    # Create a symbolic Manticore and follow last trace
    # symbolic_args = ['+'*len(arg) for arg in args.cmd[1:]]



    m2 = Manticore.linux(prog)
    f = Follower(r.trace)
    # if range:
    #     f.add_symbolic_range(*range)
    m2.verbosity(2)
    m2.register_plugin(f)



    endd = 0x400ae9
    @m2.hook(endd)
    def x(s):
        with m2.locked_context() as ctx:
            ctx['sss'] = s
            ctx['readdata'] = []
            for name, fd, data in s.platform.syscall_trace:
                print name
                print 123123
                if name in ('_receive', '_read') and fd == 0:
                    print 55555
                    ctx['readdata'] += [data]





    m2.run()



    st = m2.context['sss']
    datas = m2.context['readdata']

    cons = st.constraints.constraints







    def x(conn):
        for c in conn:
            print pp(c)
            print '-'*33

    # x(cons)
    import IPython
    IPython.embed()


if __name__=='__main__':
    main()
