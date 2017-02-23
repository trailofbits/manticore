# Copyright (c) 2013, Felipe Andres Manzano
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
#     * Redistributions of source code must retain the above copyright notice,
#       this list of conditions and the following disclaimer.
#     * Redistributions in binary form must reproduce the above copyright
#       notice,this list of conditions and the following disclaimer in the
#       documentation and/or other materials provided with the distribution.
#     * Neither the name of the copyright holder nor the names of its
#       contributors may be used to endorse or promote products derived from
#       this software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
# ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
# LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
# CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
# SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
# INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
# CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
# ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
# POSSIBILITY OF SUCH DAMAGE.
import sys
import time
import os
import copy
import cPickle
import cProfile
import random
import logging
import traceback
import signal
import weakref
try:
    import cStringIO as StringIO
except:
    import StringIO
from math import ceil, log

from ..utils.nointerrupt import DelayedKeyboardInterrupt
from .cpu.abstractcpu import ConcretizeRegister, ConcretizeMemory, \
        InvalidPCException, IgnoreAPI
from .memory import MemoryException, SymbolicMemoryException
from .smtlib import solver, Expression, Operators, SolverException, Array, BitVec, Bool, ConstraintSet
from ..utils.event import Signal
from ..utils.helpers import issymbolic

#Multiprocessing
from multiprocessing import Manager
from multiprocessing.managers import BaseManager, SyncManager


logger = logging.getLogger("EXECUTOR")

#initilizer for SyncManager
def mgr_init():
    signal.signal(signal.SIGINT, signal.SIG_IGN)
manager = SyncManager()
manager.start(mgr_init) 

class SyscallNotImplemented(Exception):
    ''' Exception raised when you try to call a not implemented
        system call. Go to linux.py and add it!
    '''
    pass

class ProcessExit(Exception):
    def __init__(self, code):
        super(ProcessExit, self).__init__("Process exited correctly. Code: %s"%code)

class RestartSyscall(Exception):
    pass

class Deadlock(Exception):
    pass

class MaxConsecutiveIntructions(Exception):
    pass

class AbandonState(Exception):
    pass

class ForkState(Exception):
    def __init__(self, condition):
        self.condition=condition

class State(object):
    #Class global counter
    _state_count = manager.Value('i', 0)
    _lock = manager.Lock()
    @staticmethod
    def get_new_id():
        with State._lock:
            ret = State._state_count.value
            State._state_count.value +=1
        return ret

    def __init__(self, constraints, model):
        self.trace = []
        self.model = model
        self.forks = 0
        self.co = self.get_new_id()
        self.constraints = constraints
        self.model._constraints = constraints
        for proc in self.model.procs:
            proc._constraints = constraints
            proc.memory._constraints = constraints
        
        self.input_symbols = list()
        #Stats I'm not sure we need in general
        self.last_pc = (None, None)
        self.visited = set()
        self.branches = {}
        self._child = None

    def __reduce__(self): 
        return (self.__class__, (self.constraints, self.model), {'visited': self.visited, 'last_pc': self.last_pc, 'forks': self.forks, 'co': self.co, 'input_symbols':self.input_symbols, 'branches': self.branches} )

    @staticmethod
    def state_count():
        return State._state_count.value

    @property
    def cpu(self):
        return self.model.current

    @property
    def mem(self):
        return self.model.current.memory

    @property
    def name(self):
        return 'state_%06d.pkl'%(self.co)

    def __enter__(self):
        assert self._child is None
        new_state = State(self.constraints.__enter__(), self.model)
        new_state.visited = set(self.visited)
        new_state.trace = self.last_pc
        new_state.forks = self.forks + 1
        new_state.co = State.get_new_id()
        new_state.input_symbols = self.input_symbols
        new_state.branches = self.branches
        self._child = new_state
        return new_state

    def __exit__(self, ty, value, traceback):
        self.constraints.__exit__(ty, value, traceback)
        self._child = None


    def execute(self):
        trace_item = (self.model._current, self.cpu.PC)
        try:
            result = self.model.execute()
        except:
            trace_item = None
            raise
        assert self.model.constraints is self.constraints
        assert self.mem.constraints is self.constraints
        self.visited.add(trace_item)
        self.last_pc = trace_item
        return result

    def add(self, constraint, check=False):
        self.constraints.add(constraint)

    def abandon(self):
        '''Abandon the currently-active state
        
        Note: This must be called from the Executor loop, or a user-provided
        callback.'''
        raise AbandonState

    def new_symbolic_buffer(self, nbytes, **options):
        '''Create and return a symbolic buffer of length |nbytes|. The buffer is
        not written into State's memory; write it to the state's memory to
        introduce it into the program state.

        Args:
            nbytes - Length of the new buffer
            options - Options to set on the returned expression. Valid options:
                name --  The name to assign to the buffer (str)
                cstring -- Whether or not to enforce that the buffer is a cstring
                 (i.e. no \0 bytes, except for the last byte). (bool)

        Returns:
            Expression representing the buffer. 
        '''
        name = options.get('name', 'buffer')
        expr = self.constraints.new_array(name=name, index_max=nbytes)
        self.input_symbols.append(expr)

        if options.get('cstring', False):
            for i in range(nbytes - 1):
                self.constraints.add(expr[i] != 0)

        return expr


    def new_symbolic_value(self, nbits, **options):
        '''Create and return a symbolic value that is |nbits| bits wide. Assign
        the value to a register or write it into the address space to introduce
        it into the program state.

        Args:
            nbits - The bitwidth of the value returned.
            options - Options to set on the returned expression. Valid options:
                label -- The label to assign to the value.

        Returns:
            Expression representing the value.
        '''
        assert nbits in (1, 4, 8, 16, 32, 64, 128, 256)
        name = options.get('label', 'val')
        expr = self.constraints.new_bitvec(nbits, name=name)
        self.input_symbols.append(expr)
        return expr

    def symbolicate_buffer(self, data, label = 'INPUT', wildcard='+', string=False):
        '''Mark parts of a buffer as symbolic (demarked by the wildcard byte)

        Args:
            data -- The string to symbolicate. If no wildcard bytes are provided,
                this is the identity function on the first argument.
            label -- The label to assign to the value
            wildcard -- The byte that is considered a wildcard
            string -- Ensure bytes returned can not be \0

        Returns:
            If data does not contain any wildcard bytes, data itself. Otherwise,
            a list of values derived from data. Non-wildcard bytes are kept as
            is, wildcard bytes are replaced by Expression objects.
        '''
        if wildcard in data:
            size = len(data)
            symb = self.constraints.new_array(name=label, index_max=size)
            self.input_symbols.append(symb)
            for j in xrange(size):
                if data[j] != wildcard:
                    symb[j] = data[j]
            data = [symb[i] for i in range(size)]

        if string:
            for b in data:
                if issymbolic(b):
                    self.constraints.add(b != 0)
                else:
                    assert b!=0
        return data


    def concretize(self, symbolic, policy, maxcount=100):
        vals = []
        if policy == 'MINMAX':
            vals = solver.minmax(self.constraints, symbolic)
        elif policy == 'SAMPLED':
            m, M = solver.minmax(self.constraints, symbolic)
            vals += [m, M]
            if M-m > 3:
                if solver.can_be_true(self.constraints, symbolic == (m+M)/2):
                    vals.append((m+M)/2)
            if M-m > 100:
                vals += solver.get_all_values(self.constraints, symbolic, maxcnt=maxcount, silent=True)
        else:
            assert policy == 'ALL'
            vals = solver.get_all_values(self.constraints, symbolic, maxcnt=maxcount, silent=False)

        return list(set(vals))

    @property
    def _solver(self):
        from .smtlib import solver
        return solver

    def solve_one(self, expr):
        # type: (Expression) -> int
        return self._solver.get_value(self.constraints, expr)

    def solve_n(self, expr, nsolves=1, policy='minmax'):
        # type: (Expression, int) -> list
        return self._solver.get_all_values(self.constraints, expr, nsolves, silent=True)


def sync(f):
    """ Synchronization decorator. """
    def newFunction(self, *args, **kw):
        self._lock.acquire()
        try:
            return f(self, *args, **kw)
        finally:
            self._lock.release()
    return newFunction

class Executor(object):

    def shutdown(self):
        with self._lock:
            self._shutdown.value+=1
            ret = self._shutdown.value
            self._lock.notify_all()
        return ret

    def isShutdown(self):
        return self._shutdown.value != 0

    def __init__(self, initial, workspace=None, policy='random', **options):
        assert os.path.isdir(workspace)
        self.workspace = workspace
        logger.debug("Workspace set: %s", self.workspace)

        self.max_states = options.get('maxstates', 0)
        self.max_storage = options.get('maxstorage', 0)
        self.replay_path = options.get('replay', None) #(dest, cond, origin)
        self._dump_every = options.get('dumpafter', 0)
        self._profile = cProfile.Profile()
        self.profiling = options.get('dumpstats', False)

        # Signals
        self.will_execute_pc = Signal()
        self.will_fork = Signal()

        self.policy_order = 'max'
        if policy[0] in '+-':
            self.policy_order = {'+':'max', '-':'min'}[policy[0]]
            policy = policy[1:]
        assert policy in ['random','adhoc','uncovered','dicount','icount','syscount','depth','bucket']
        self.policy = policy

        self._states = manager.dict()
        self._test_number = manager.Value('i', 0 )
        self._running = manager.Value('i', 0 )
        self._count = manager.Value('i', 0 )
        self._shutdown = manager.Value('i', 0)
        #self.timeout = manager.Event()
        self._visited = manager.list()
        self._errors = manager.list()
        self._all_branches = manager.list()
        self._lock = manager.Condition(manager.Lock())
        #Stats
        self._stats = manager.list()

        #search previously generated states
        saved_states = [ self._getFilename(filename) for filename in os.listdir(self.workspace) if filename.endswith('.pkl') ]
        for filename in saved_states:
            try:
                with open(filename, "r") as f:
                    new_state = cPickle.loads(f.read())
                    #Todo check is related to 'os' ?
                self.putState( new_state )
                assert State.state_count() >=  new_state.co+1
            except:
                logger.info("Failed to load saved state %s", filename)
        self._test_number.value = len(saved_states) #conservative estimate
        
        #Normally...
        if len(saved_states) == 0 :
            self.putState( initial )
        else:
            #If we are continuin from a set of saved states replay is not supported
            assert self.replay_path is None 

    def dump_stats(self):
        if not self.profiling:
            logger.debug("Profiling not enabled.")
            return

        import pstats
        class PstatsFormatted:
            def __init__(self, d):
                self.stats = dict(d)
            def create_stats(self):
                pass

        ps = None
        for item in self._stats:
            try:
                stat = PstatsFormatted(item)
                if ps is None:
                    ps = pstats.Stats(stat)
                else:
                    ps.add(stat)
            except TypeError:
                logger.debug("Incorrectly formatted profiling information in _stats, skipping")

        if ps is None:
            logger.info("Profiling failed")
        else:
            filename = self._getFilename('profiling.bin') 
            logger.info("Dumping profiling info at %s", filename)
            ps.dump_stats(filename)
            
            '''(For each function called in the python program) - 
                How long each call took (percall, inclusive and exclusive) - 
                How many times it was called (ncalls) - 
                How long it took (cumtime: includes the times of other functions it calls) - 
                How long it actually took (tottime: excludes the times of other functions) - 
                What functions it called (callers) - 
                What functions called it (callees)'''

            getstate_time = 0.0
            putstate_time = 0.0
            solver_time = 0.0

            for (func_file, func_line, func_name), (cc, nc, tt, ct, callers) in ps.stats.iteritems():
                #This if tries to sum only independient stuff
                if func_name == '_getState':
                    getstate_time += ct
                elif func_name == '_putState':
                    putstate_time += ct
                elif func_file.endswith('solver.py') and 'setstate' not in func_name and 'getstate' not in func_name and 'ckl' not in func_name:
                    solver_time += ct
                #print (func_file, func_line, func_name), (cc, nc, tt, ct)

            logger.info("Total profiled time: %f", ps.total_tt)
            logger.info("Loading state time: %f", getstate_time)
            logger.info("Saving state time: %f", putstate_time)
            logger.info("Solver time: %f", solver_time)
            logger.info("Other time: %f", ps.total_tt - (getstate_time+putstate_time+solver_time))

    def _getFilename(self, filename):
        return os.path.join(self.workspace, filename)

    @property
    def count(self):
        return self._count.value

    @property
    def visited(self):
        return self._visited 

    @property
    def errors(self):
        return self._errors 

    @property
    def dump_every(self):
        return self._dump_every or 0

    @dump_every.setter
    def dump_every(self, val):
        assert(isinstance(val, (int, long)))
        self._dump_every = val

    @sync
    def delState(self, state):
        return self._delState(state)

    def _delState(self, state):
        logger.debug("Removing state %d from storage", state.co)
        assert state.name in self._states
        del self._states[state.name]
        os.remove(self._getFilename(state.name))

    @sync
    def putState(self, state):
        return self._putState(state)

    def _putState(self, state):
        logger.debug("Saving state %d to file %s", state.co, state.name)

        with open(self._getFilename(state.name), 'w+') as f:
            try:
                f.write(cPickle.dumps(state, 2))
            except RuntimeError:
                # there recursion limit exceeded problem, 
                # try a slower, iterative solution
                from ..utils import iterpickle
                logger.info("WARNING: using iterpickle to dump state")
                f.write(iterpickle.dumps(state, 2))

            filesize = f.tell()
            f.flush()

        #Calculate some statistics so we can choose which state to analyze 
        # without loading the file later.
        receive_size = 0
        transmit_size = 0
        for sysname, fd, data in state.model.syscall_trace:
            if sysname == '_receive':
                receive_size += len(data)
            if sysname == '_transmit':
                transmit_size += len(data)

        # if we did *not* concretize PC, this will be expression
        # or equal to state.last_pc (which we get from trace)
        reg_pc = state.cpu.PC
        # if we *did* concretize on PC, this value
        # and last executed value will (may?) differ

        # get last executed instruction
        last_cpu, last_pc = state.last_pc

        try:
            state.branches[(last_pc, state.cpu.PC)] += 1
        except KeyError:
            state.branches[(last_pc, state.cpu.PC)] = 1
        item = (last_pc, state.cpu.PC)
        assert not issymbolic(last_pc)
        assert not issymbolic(state.cpu.PC)
        if item not in self._all_branches:
            self._all_branches.append(item)

        assert not issymbolic(last_pc)

        self._states[state.name] = {'received' : receive_size,
                                    'transmited': transmit_size,
                                    'icount': state.model.current.icount,
                                    'dicount': len(state.visited),
                                    'proc': last_cpu,
                                    'pc': last_pc,
                                    'syscount': len(state.model.syscall_trace),
                                    'smem': len(state.model.current.memory._symbols),
                                    'symbols': len(str(state.constraints)),
                                    'nsyscalls': len(state.model.syscall_trace),
                                    'forks': state.forks,
                                    'filesize':filesize,
                                    'branches':state.branches,
                                   }

        logger.debug("Adding state %s to processing list. State list size: %d", state.name, len(self._states))
        fields = sorted(self._states[state.name].keys())
        logger.debug('STAT:      name'+'  '.join(['%10s'%x for x in fields]))
        logger.debug('STAT:%10s'%state.co+'  '.join(['%10s'%str(self._states[state.name][x]) for x in fields]))
        self._lock.notify_all()

    def lenState(self):
        return len(self._states)

    @sync
    def getState(self, policy='random', order='max', fudge=1):
        return self._getState(policy, order, fudge)

    def _getState(self, policy='random', order='max', fudge=1):
        assert order in ['max','min']
        assert abs(fudge)>0
        assert policy in ['random','adhoc','uncovered','dicount','icount','syscount','depth','bucket']

        def _bucket(stat):
            def bucket(n):
                if not isinstance(n, int):
                    return 0
                return pow(2, ceil(log(n)/log(2)) )

            count = 0
            for branch, n in stat['branches'].items():
                count += (bucket(n) - n) / (bucket(n)/2)

            if count == 0 :
                return 0.0
            return -float(count)

        def _random(stat):
            ''' Every state with the same likelihood '''
            return 1.0

        def _uncovered(stat):
            return (stat['proc'], stat['pc']) not in self._visited

        def _dicount(stat):
            return stat['dicount']

        def _icount(stat):
            return stat['icount']

        def _syscount(stat):
            return stat['syscount']

        def _depth(stat):
            return stat['forks']

        def _adhoc(stat):
            return  ( (stat['proc'], stat['pc']) not in self._visited, 
                      stat['received']   < 25, 
                      stat['transmited'] < 25,
                      float(stat['received'])/(stat['transmited']+1),
                      float(stat['dicount'])/(stat['icount']+1)
                    )
        while len(self._states) == 0 and self._running.value > 0 and not self.isShutdown():
            logger.debug("Waiting for available states")
            self._lock.wait()
        if len(self._states) == 0 and self._running.value == 0 or self.isShutdown():
            return None


        metric = locals()['_%s'%policy]

        #FIXME: move the metric to an external function and make it smooth.
        # It should estimate the likelihood to find a crash under this state
        possible_states = list( sorted( self._states.items(), key = lambda (st_name,st_stat): metric(st_stat) ) )
        logger.debug('Prioritizing metric %s %r', order, sorted(map(metric, self._states.values() ) ) )


        if policy == 'bucket':
            logger.info("Metric %r", 'bucket'*10 )

            for st_name, st_stat in sorted( self._states.items(), key = lambda (st_name,st_stat): metric(st_stat) ):
                brs = st_stat['branches']
                vals = []
                for branch in self._all_branches:
                    try:
                        vals.append(brs[branch])
                    except:
                        vals.append(None)
                logger.info("Metric for state %s %r: %r", st_name, vals, metric(st_stat) )

        if order == 'max':
            possible_states = possible_states[-fudge:]
        else:
            possible_states = possible_states[:fudge]

        random.shuffle(possible_states)

        st_name, st_x = possible_states.pop()

        filename = self._getFilename(st_name)
        logger.debug("Selecting a new state to analyze %s. Using policy: %s. Processing list size is %d", filename, policy, len(self._states))

        with open(filename, 'rb') as f:
            new_state = cPickle.loads(f.read())
        self._delState(new_state)
        logger.debug("Selected state: %s (%r)", new_state.co, metric(st_x))

        return new_state 

    def add_hook(self, pc, callback, user_data=None):
        '''This setups a hook.
            Invokes callback when the specified address pc is reached
            Returns an id to reference this specific hook.
        '''
        if self.hooks is None:
            self.hooks = {}
        self.hooks.setdefault(pc, set()).add( (callback, user_data) )
        return hash( (pc, callback, user_data) )

    def del_hook(self, n):
        ''' Deletes the hook by id '''
        for pc, callback, user_data in self.hooks.items():
            if hash((pc, callback, user_data)) == n:
                self.hooks[pc].remove((callback, user_data))
                if len(self.hooks[pc]) == 0 :
                    del self.hooks[pc]
                    return True
        return False

    def generate_testcase(self, state, message = 'Testcase generated'):
        with self._lock:
            self._test_number.value += 1
            test_number = self._test_number.value

        logger.info("Generating testcase No. %d for state No.%d - %s",
                test_number, state.co, message)

        start = time.time()

        # Save state
        statefile = 'test_{:08x}.pkl'.format(test_number)
        with open(self._getFilename(statefile), 'wb') as f:
            try:
                f.write(cPickle.dumps(state, 2))
            except RuntimeError:
                # there recursion limit exceeded problem, 
                # try a slower, iterative solution
                from ..utils import iterpickle
                logger.info("WARNING: using iterpickle to dump state")
                f.write(iterpickle.dumps(state, 2))
            f.flush()
        logger.debug("saved in %d seconds", time.time() - start)

        # Summarize state
        output = StringIO.StringIO()
        memories = set()

        output.write("Command line:\n  " + ' '.join(sys.argv) + '\n')
        output.write('Status:\n  {}\n'.format(message))
        output.write('\n')

        for cpu in filter(None, state.model.procs):
            idx = state.model.procs.index(cpu)
            output.write("================ PROC: %02d ================\n"%idx)

            output.write("Memory:\n")
            if hash(cpu.memory) not in memories:
                for m in str(cpu.memory).split('\n'):
                    output.write("  %s\n"%m)
                memories.add(hash(cpu.memory))

            output.write("CPU:\n{}".format(cpu))

            if hasattr(cpu, "instruction"):
                i = cpu.instruction
                output.write("  Instruction: 0x%x\t(%s %s)\n" %(i.address, i.mnemonic, i.op_str))
            else:
                output.write("  Instruction: {symbolic}\n")

        with open(self._getFilename('test_%08x.messages'%test_number),'a') as f:
            f.write(output.getvalue())
            output.close()

        tracefile = 'test_{:08x}.trace'.format(test_number)
        with open(self._getFilename(tracefile), 'w') as f:
            for _, pc in state.visited:
                f.write('0x{:08x}\n'.format(pc))

        # Save constraints formula
        smtfile = 'test_{:08x}.smt'.format(test_number)
        with open(self._getFilename(smtfile), 'wb') as f:
            f.write(str(state.constraints))
        
        assert solver.check(state.constraints)
        for symbol in state.input_symbols:
            buf = solver.get_value(state.constraints, symbol)
            file(self._getFilename('test_%08x.txt'%test_number),'a').write("%s: %s\n"%(symbol.name, repr(buf)))
        
        file(self._getFilename('test_%08x.syscalls'%test_number),'a').write(repr(state.model.syscall_trace))

        stdout = ''
        for sysname, fd, data in state.model.syscall_trace:
            if sysname == '_transmit' and fd == 1:
                stdout += ''.join(map(str, data))
        file(self._getFilename('test_%08x.stdout'%test_number),'a').write(stdout)

        # Save STDIN solution
        stdin_file = 'test_{:08x}.stdin'.format(test_number)
        with open(self._getFilename(stdin_file), 'wb') as f:
            try:
                for sysname, fd, data in state.model.syscall_trace:
                    if sysname != '_receive' or fd != 0:
                        continue
                    for c in data:
                        f.write(chr(solver.get_value(state.constraints, c)))
            except SolverException, e:
                f.seek(0)
                f.write("{SolverException}\n")
                f.truncate()

        return test_number



    def getTotalUsedStorage(self):
        #approximation
        return sum(map(lambda x: x['filesize'], self._states))

    def fork(self, current_state, symbolic, vals, setstate=None):
        '''
        Fork current_state into len(vals) states.
        Assert in each fork that symbolic == val[x] and set the state   
        Yeah I know.
        '''
        self.will_fork(current_state, symbolic, vals)

        if setstate is None:
            setstate = lambda x,y: None
        with self._lock:
            #Check if we have too many states going on
            if self.max_states !=0:
                N = self.lenStates()
                if N + len(vals) > self.max_states :
                    logger.info("Max number of states reached, sampling")
                    #lets keep only a few values
                    if self.max_states > N:
                        #There is still some room keep a few of the values
                        remaining = self.max_states - N
                        assert remaining > 0
                        vals = random.sample(vals, min(remaining, len(vals)) ) 
                    else:
                        #No room really so keep only one (Which will replace the curent state)
                        vals = random.sample(vals, 1) 
                    logger.debug("Sampled possible values are: %s", ["0x%016x"%x for x in vals])                        

            #Check if we are using too much stoage
            if self.max_storage != 0:
                total_used_storage = self.getTotalUsedStorage()
                if total_used_storage > self.max_storage:
                    #inhibit forking
                    vals = random.sample(vals, 1) 
                    logger.info("Too much storage used(%d). Inhibiting fork", total_used_storage)

        children = []
        if len(vals) == 1:
            constraint = symbolic == vals[0]
            current_state.add(constraint, check=True) #We already know it's sat
            setstate(current_state, vals[0])
            #current_state._try_simplify()
        else:
            #Shuffle the possibilities, 
            random.shuffle(vals)
            #this will save all the states to files
            parent = current_state.co

            #Make a new variable
            if isinstance(symbolic, BitVec):
                new_var = current_state.constraints.new_bitvec(symbolic.size)
            elif isinstance(symbolic, Bool):
                new_var = current_state.constraints.new_bool()
            else:
                raise Exception('Unsupported concretization type %s', type(symbolic))
            current_state.constraints.add(new_var == symbolic)

            for new_value in vals:
                with current_state as new_state:
                    new_state.add(symbolic == new_value, check=False) #We already know it's sat
                    #and set the PC of the new state to the concrete pc-dest
                    #(or other register or memory address to concrete)
                    setstate(new_state, new_value) 
                    #add the state to the list of pending states
                    self.putState(new_state)
                    children.append(new_state.co)


            logger.debug("Forking state %d into states %r",parent, children)
            current_state = None

        return current_state

    @sync
    def visit(self, pc):
        if pc not in self._visited:
            self._visited.append(pc)

    @sync
    def newerror(self, pc):
        if pc not in self._errors:
            self._errors.append(pc)

    def _startRun(self):
        #notify siblings we are about to start a run
        with self._lock:
            self._running.value+=1

    def _stopRun(self, count=0):
        #notify siblings we are about to stop this run
        #log how many intruction were executed
        with self._lock:
            self._running.value-=1
            self._count.value += count
            self._lock.notify_all()

    def run(self):
        if self.profiling:
            self._profile.enable()

        policy_order=self.policy_order
        policy=self.policy
        replay_path = self.replay_path

        count = 0
        current_state = None
        current_icount = 0
        local_visited = set()

        with DelayedKeyboardInterrupt():
            #notify siblings we are about to start a run
            self._startRun()

        logger.debug("Starting Manticore Symbolic Emulator mainloop (pid %d).",os.getpid())


        while not self.isShutdown():
            try:
                #select a suitable state to analize
                if current_state is None:

                    #notify siblings we are about to stop this run
                    self._stopRun()

                    with self._lock:
                        current_state = self._getState(policy=policy, order=policy_order)
                        assert current_state is None or current_state.constraints._child is None
                        self._running.value+=1

                    #notify siblings we are about to start a run
                    #self._startRun()

                    if current_state is None:
                        logger.debug("No more states in the queue, byte bye!")
                        break
                    assert current_state is not None

                    logger.setState(current_state.co)
                    current_icount = 0

                try:
                    if current_state:
                        assert solver.check(current_state.constraints)

                    #execute until exception or finish or max consecutive instructions without exception 
                    max_iters = self.dump_every + count

                    # allow us to terminate manticore processes
                    while not self.isShutdown():
                        # Announce that we're about to execute
                        self.will_execute_pc(current_state, current_state.cpu.PC)

                        if not current_state.execute():
                            break

                        if replay_path:
                            if self.replay_path[len(current_state.trace)-1] != current_state.trace[-1][1]:
                                logger.debug("Silently ignoring state, trace dosen't match the replay")
                                current_state = None
                                continue

                        #TODO: maybe generalize as hook
                        if current_state.last_pc not in local_visited:
                            local_visited.add(current_state.last_pc)
                            self.visit(current_state.last_pc)

                        count += 1

                        if self.dump_every and count >= max_iters:
                            if not issymbolic(current_state.cpu.PC):
                                raise MaxConsecutiveIntructions()

                except MaxConsecutiveIntructions as e:
                    logger.debug("Maximun number of consecutive instructions run in one state. Lets put this state in the pool and choose again")
                    self.generate_testcase(current_state, "Intermediate state. Maximun number of consecutive instructions")
                    #add the state to the list of pending states
                    self.putState(current_state)
                    current_state = None

                except AbandonState, e:
                    current_state = None

                except ForkState as e:
                    logger.debug("Forking state")
                    current_state = self.fork(current_state, e.condition, [True, False])

                except ConcretizeMemory as e:
                    logger.debug("Concretizing memory at %x(%d) using policy %s.", e.address, e.size, e.policy)
                    symbolic = current_state.cpu.read_int(e.address, e.size)
                    vals = current_state.concretize(symbolic, e.policy)
                    def setstate(state, val):
                        state.cpu.write_int(e.address, val, e.size)
                    current_state = self.fork(current_state, symbolic, vals, setstate)
                    del vals, symbolic, setstate

                except ConcretizeRegister as e:

                    logger.debug("Concretizing register %s using policy %s.", e.reg_name, e.policy)
                    symbolic = current_state.cpu.read_register(e.reg_name)

                    try:
                        vals = current_state.concretize(symbolic, e.policy)
                    except SolverException as se:
                        # too many solution for concretization.
                        assert se.message == 'Max number of different solutions hit'
                        msg = "SolverException: {}\n".format(se.message)
                        if e.reg_name.upper() in ['EIP', 'RIP', 'PC']:
                            #Detect dangling EIP
                            msg += "Solver Exception: Dangling PC: {}".format(e.reg_name) 
                        else:
                            msg += "Solver Exception: highly symbolic register {}. Try policy=SAMPLED instead of ALL?".format(e.reg_name)

                        self.generate_testcase(current_state, msg)
                        current_state = None
                        del symbolic
                        continue

                    if len(vals) == 0:
                        logger.error("Cannot get list of concrete values for:\n %s", current_state.constraints)
                        current_state = None
                        del vals, symbolic
                        continue

                    assert len(vals) > 0, "It should be at least one solution"
                    logger.debug("%s. Possible values are: %s", e.message, ["0x%016x"%x for x in vals])

                    def setstate(state, val):
                        # XXX This only applies to ARM since x86 has no conditional instructions
                        if hasattr(state.cpu, 'forceNextInstruction'):
                            state.cpu.forceNextInstruction()
                        state.cpu.write_register(e.reg_name, val)
                    current_state = self.fork(current_state, symbolic, vals, setstate)
                    del vals, symbolic, setstate

                except SymbolicMemoryException as e:
                    logger.error('SymbolicMemoryException at PC: 0x%16x. Cause: %s', current_state.current.PC, e.cause)
                    logger.info('Constraint for crashing! %s', e.constraint)

                    children = []
                    with current_state as new_state:
                        new_state.add(e.constraint==False)
                        if solver.check(new_state.constraints):
                            self.putState(new_state)
                            children.append(new_state.co)

                    with current_state as new_state:
                        children.append(new_state.co)
                        new_state.add(e.constraint)
                        self.newerror(new_state.current.PC)
                        self.generate_testcase(new_state, "Symbolic Memory Exception: " + str(e))

                    logger.info("Forking state %d into states %r",current_state.co, children)
                    new_state = current_state = None

                except MemoryException as e:
                    logger.error("MemoryException at PC: 0x{:016x}. Cause: {}\n".format(current_state.cpu.instruction.address, e.cause))
                    self.newerror(current_state.cpu.PC)
                    self.generate_testcase(current_state, "Memory Exception: " + str(e))
                    current_state = None

                except InvalidPCException as e:
                    self.generate_testcase(current_state, "Invalid PC Exception" + str(e))
                    current_state = None

                except ProcessExit:
                    self.generate_testcase(current_state, "Program finished correctly")
                    current_state = None

                except Deadlock:
                    self.generate_testcase(current_state, "Deadlock detected")
                    current_state = None

                except SolverException as e:
                    import traceback
                    exc_type, exc_value, exc_traceback = sys.exc_info()
                    print "*** print_exc:"
                    traceback.print_exc()

                    if solver.check(current_state.constraints):
                        self.generate_testcase(current_state, "Solver failed" + str(e))
                    current_state = None

            except KeyboardInterrupt as e:
                logger.error("Interrupted!")
                logger.setState(None)
                current_state = None
                break

            except SyscallNotImplemented as e:
                logger.error("SYSCALL NOT IMPLEMENTED, PLEASE IMPLEMENT\n%s", str(e))
                self.generate_testcase(current_state, "UNIMPLEMENTED syscall "+str(e))
                current_state = None

            except AssertionError as e:
                import traceback
                trace = traceback.format_exc()
                logger.error("Failed an internal assertion: %s\n%s", str(e), trace )
                for log in trace.splitlines():
                    logger.error(log)
                if solver.check(current_state.constraints):
                    if isinstance(current_state.cpu.PC, (int, long)):
                        PC = "{:08x}".format(current_state.cpu.PC)
                    else:
                        PC = str(current_state.cpu.PC)

                    self.generate_testcase(current_state, "Assertion Failure {} at {}: {}".format(str(e), PC, trace))
                current_state = None

            except Exception as e:
                import traceback
                trace = traceback.format_exc()
                logger.error("THIS SHOULD NOT REACHABLE! Exception in user code: %s\n%s", str(e), trace)
                for log in trace.splitlines():
                    logger.error(log) 
                current_state = None

        with DelayedKeyboardInterrupt():
            #notify siblings we are about to stop this run
            self._stopRun(count)
            if self.profiling:
                self._profile.disable()
                self._profile.create_stats()
                with self._lock:
                     self._stats.append(self._profile.stats.items())

        return count


