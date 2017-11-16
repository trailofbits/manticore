#!/usr/bin/env python

'''
A simple concolic execution driver script. Only currently supports passing symbolic arguments via argv.

'''

import sys
import random, struct
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

prog = 'basic'
endd = 0x400ae9

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



# permutes constraints. highly possibly that returned constraints can be
# unsat this does it blindly, without any attention to the constraints
# themselves
def permu(cons, includeself=False):
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

def concrete_run_get_trace(inp):
    m1 = Manticore.linux(prog, concrete_start=inp)
    t = ExtendedTracer()
    r = TraceReceiver(t)
    m1.verbosity(1)
    m1.register_plugin(t)
    m1.register_plugin(r)
    m1.run(procs=1)
    return r.trace


def symbolic_run_get_cons(trace):
    m2 = Manticore.linux(prog)
    f = Follower(trace)
    m2.verbosity(1)
    m2.register_plugin(f)


    @m2.hook(endd)
    def x(s):
        with m2.locked_context() as ctx:
            ctx['sss'] = s
            ctx['readdata'] = []
            for name, fd, data in s.platform.syscall_trace:
                if name in ('_receive', '_read') and fd == 0:
                    ctx['readdata'] += [data]

    m2.run()

    # lol
    # return the ConstraintSet and the data from stdin

    st = m2.context['sss']
    datas = m2.context['readdata']

    # cons = st.constraints.constraints
    return list(st.constraints.constraints), datas

def x(conn):
    for c in conn:
        print pp(c)
        print '-'*33

def xxx(con):
    return hex(con.operands[1].value), (hex(con.operands[0].operands[1].value), hex(con.operands[0].operands[2].value))

def newinold(new, olds):
    for old in olds:
        if eq(new, old):
            return True
    return False

def getnew(oldcons, newcons):
    ret = []
    for new in newcons:
        if not newinold(new, oldcons):
            ret.append(new)
    return ret

def consaresat(cons):
    return solver.can_be_true(newcs(cons), True)

def get_new_constrs_for_queue(oldcons, newcons):
    ret = []

    # i'm pretty sure its correct to assume newcons is a superset of oldcons

    neww = getnew(oldcons, newcons)
    if not neww:
        return ret


    perms = permu(neww)
    for p in perms:
        candidate = oldcons + p
        # candidate new constraint sets might not be sat because we blindly
        # permute the new constraints that the path uncovered and append them
        # back onto the original set. we do this without regard for how the
        # permutation of the new constraints combines with the old constratins
        # to affect the satisfiability of the whole
        if consaresat(candidate):
            ret.append(candidate)

    return ret

def log(s):
    print '[+]', s, '\n'

def inp2ints(inp):
    a, b, c = struct.unpack('<III', inp)
    return 'a={} b={} c={}'.format(a, b, c)



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
    import Queue

    q = Queue.Queue()

    # a = struct.pack('<I', random.randint(0, 10))
    # b = struct.pack('<I', random.randint(0, 10))
    # c = struct.pack('<I', random.randint(0, 10))
    a = struct.pack('<I', 0)
    b = struct.pack('<I', 5)
    b = struct.pack('<I', 4) # causes a bug; 8 paths instead of 5
    c = struct.pack('<I', 0)
    xx = a + b + c

    log('seed input generated: {}'.format(inp2ints(xx)))

    paths = 1

    log('running initial concrete run')
    trc = concrete_run_get_trace(xx)

    log('getting constraints on initial run')
    cons, datas = symbolic_run_get_cons(trc)

    to_queue = get_new_constrs_for_queue([], cons)

    log('permuting constraints and adding {} constraints sets to queue'.format(len(to_queue)))

    for each in to_queue:
        q.put(each)

    # hmmm probably issues with the datas stuff here? probably need to store
    # the datas in the q or something. what if there was a new read(2) deep in the program, changing the datas
    while not q.empty():
        log('get constraint set from queue, queue size: {}'.format(q.qsize()))
        cons = q.get()
        inp = input_from_cons(cons, datas)
        log('generated input from constraints: {}'.format(inp2ints(inp)))



        log('running generate input concretely')
        trc = concrete_run_get_trace(inp)
        paths +=1 

        log('doing symex on new generated input')
        newcons, datas = symbolic_run_get_cons(trc)


        # hmmm ideally do some smart stuff so we don't have to check if the
        # constraints are unsat. something like the compare the constraints set
        # which you used to generate the input, and the constraint set you got
        # from the symex. sounds pretty hard
        #
        # but maybe a dumb way where we blindly permute the constraints
        # and just check if they're sat before queueing will work

        to_queue = get_new_constrs_for_queue(cons, newcons)

        log('permuting constraints and adding {} constraints sets to queue'.format(len(to_queue)))

        for each in to_queue:
            q.put(each)

    log('paths found: {}'.format(paths))



if __name__=='__main__':
    main()
