import sys
import time
import os
import copy
import cPickle
import cProfile
import random
import logging
import pstats
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
        InvalidPCException, IgnoreAPI, SymbolicPCException
from .memory import MemoryException, SymbolicMemoryException
from .smtlib import solver, Expression, Operators, SolverException, Array, BitVec, Bool, ConstraintSet
from ..utils.event import Signal
from ..utils.helpers import issymbolic

from multiprocessing.managers import SyncManager

def mgr_init():
    signal.signal(signal.SIGINT, signal.SIG_IGN)
manager = SyncManager()
manager.start(mgr_init)

from .state import AbandonState, State

logger = logging.getLogger("EXECUTOR")

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

class ForkState(Exception):
    def __init__(self, condition):
        self.condition=condition


def sync(f):
    """ Synchronization decorator. """
    def newFunction(self, *args, **kw):
        self._lock.acquire()
        try:
            return f(self, *args, **kw)
        finally:
            self._lock.release()
    return newFunction

class ProfilingResults(object):
    def __init__(self, raw_stats, instructions_executed):
        self.raw_stats = raw_stats
        self.instructions_executed = instructions_executed

        self.time_elapsed = raw_stats.total_tt

        self.loading_time = 0
        self.saving_time = 0
        self.solver_time = 0
        for (func_file, _, func_name), (_, _, _, func_time, _) in raw_stats.stats.iteritems():
            if func_name == '_getState':
                self.loading_time += func_time
            elif func_name == '_putState':
                self.saving_time += func_time
            elif func_file.endswith('solver.py') and 'setstate' not in func_name and 'getstate' not in func_name and 'ckl' not in func_name:
                self.solver_time += func_time

    def __str__(self):
        return '\n'.join([ "Total time: {} seconds".format(self.time_elapsed),
                           "Total instructions executed: {}".format(self.instructions_executed),
                           "Average instructions per second: {}".format(self.instructions_executed / self.time_elapsed),
                           "Time spent loading states: {} seconds".format(self.loading_time),
                           "Time spent saving states: {} seconds".format(self.saving_time),
                           "Time spent in solver: {} seconds".format(self.solver_time)])


class Executor(object):
    '''
    The executor guides the execution of a single state, handles state forking 
    and selection, maintains run statistics and handles all exceptional
    conditions (system calls, memory faults, concretization, etc.)
    '''

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

    def dump_stats(self):
        if not self.profiling:
            logger.debug("Profiling not enabled.")
            return

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
            results = ProfilingResults(ps, self.count)

            logger.info("Total profiled time: %f", results.time_elapsed)
            logger.info("Loading state time: %f", results.loading_time)
            logger.info("Saving state time: %f", results.saving_time)
            logger.info("Solver time: %f", results.solver_time)
            logger.info("Other time: %f", results.time_elapsed - (results.loading_time + results.saving_time + results.solver_time))
            return results

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
        '''
        Serialize and store a given state.

        :param state: The state to serialize
        '''
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
                logger.warning("Using iterpickle to dump state")
                f.write(iterpickle.dumps(state, 2))

            filesize = f.tell()
            f.flush()

        #Calculate some statistics so we can choose which state to analyze 
        # without loading the file later.
        receive_size = 0
        transmit_size = 0
        for sysname, fd, data in state.platform.syscall_trace:
            if sysname in ('_receive', '_read'):
                receive_size += len(data)
            if sysname in ('_transmit', '_write'):
                transmit_size += len(data)

        # if we did *not* concretize PC, this will be expression
        # or equal to state.last_pc (which we get from trace)
        reg_pc = state.cpu.PC
        # if we *did* concretize on PC, this value
        # and last executed value will (may?) differ

        # get last executed instruction
        last_cpu, last_pc = state.last_pc

        item = (last_pc, state.cpu.PC)
        assert not issymbolic(last_pc)
        assert not issymbolic(state.cpu.PC)
        if item not in self._all_branches:
            self._all_branches.append(item)

        assert not issymbolic(last_pc)

        self._states[state.name] = {'received' : receive_size,
                                    'transmited': transmit_size,
                                    'icount': state.platform.current.icount,
                                    'dicount': len(state.visited),
                                    'proc': last_cpu,
                                    'pc': last_pc,
                                    'syscount': len(state.platform.syscall_trace),
                                    'smem': len(state.platform.current.memory._symbols),
                                    'symbols': len(str(state.constraints)),
                                    'nsyscalls': len(state.platform.syscall_trace),
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
        '''
        Load a stored state according to policy and order.

        :param policy: One of: 'random','adhoc','uncovered','dicount','icount','syscount','depth', or 'bucket'
        :param order: 'max' or 'min'
        :param fudge: Whether to skip any
        :return: a State instance
        '''
        return self._getState(policy, order, fudge)

    def _getState(self, policy='random', order='max', fudge=1):
        if not self._states.items():
            return None
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
            logger.info("Metric: bucket")

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

    def generate_testcase(self, state, message = 'Testcase generated'):
        '''
        Create a serialized description of a given state.

        :param state: The state to generate information about
        :param message: Accompanying message
        '''
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

        for cpu in filter(None, state.platform.procs):
            idx = state.platform.procs.index(cpu)
            output.write("================ PROC: {:02d} ================\n".format(idx))

            output.write("Memory:\n")
            if hash(cpu.memory) not in memories:
                for m in str(cpu.memory).split('\n'):
                    output.write("  {:s}\n".format(m))
                memories.add(hash(cpu.memory))

            output.write("CPU:\n{}".format(cpu))

            if hasattr(cpu, "instruction") and cpu.instruction is not None:
                i = cpu.instruction
                output.write("  Instruction: 0x{:x}\t({:s} {:s})\n".format(i.address, i.mnemonic, i.op_str))
            else:
                output.write("  Instruction: {symbolic}\n")

        with open(self._getFilename('test_{:08x}.messages'.format(test_number)),'a') as f:
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
            open(self._getFilename('test_{:08x}.txt'.format(test_number)),'a').write("{:s}: {:s}\n".format(symbol.name, repr(buf)))
        
        open(self._getFilename('test_{:08x}.syscalls'.format(test_number)),'a').write(repr(state.platform.syscall_trace))

        # save symbolic files
        files = getattr(state.platform, 'files', None)
        if files is not None:
            for f in files:
                array = getattr(f, 'array', None)
                if array is not None:
                    buf = solver.get_value(state.constraints, array)
                    filename = os.path.basename(array.name)
                    filename = 'test_{:08x}.{:s}'.format(test_number, filename)
                    open(self._getFilename(filename),'a').write("{:s}".format(buf))

        stdout = ''
        stderr = ''
        for sysname, fd, data in state.platform.syscall_trace:
            if sysname in ('_transmit', '_write') and fd == 1:
                stdout += ''.join(map(str, data))
            if sysname in ('_transmit', '_write') and fd == 2:
                stderr += ''.join(map(str, data))
        open(self._getFilename('test_{:08x}.stdout'.format(test_number)),'a').write(stdout)
        open(self._getFilename('test_{:08x}.stderr'.format(test_number)),'a').write(stderr)

        # Save STDIN solution
        stdin_file = 'test_{:08x}.stdin'.format(test_number)
        with open(self._getFilename(stdin_file), 'wb') as f:
            try:
                for sysname, fd, data in state.platform.syscall_trace:
                    if sysname not in ('_receive', '_read') or fd != 0:
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
                        #No room really so keep only one (Which will replace the current state)
                        vals = random.sample(vals, 1) 
                    logger.debug("Sampled possible values are: %s", ["0x%016x"%x for x in vals])                        

            #Check if we are using too much storage
            if self.max_storage != 0:
                total_used_storage = self.getTotalUsedStorage()
                if total_used_storage > self.max_storage:
                    #inhibit forking
                    vals = random.sample(vals, 1) 
                    logger.info("Too much storage used(%d). Inhibiting fork", total_used_storage)

        children = []
        if len(vals) == 1:
            current_state.constrain(symbolic == vals[0])
            setstate(current_state, vals[0])
            #current_state._try_simplify()
        else:
            #Shuffle the possibilities, 
            random.shuffle(vals)
            #this will save all the states to files
            parent = current_state.co

            for new_value in vals:
                with current_state as new_state:
                    new_state.constrain(symbolic == new_value)
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
        #log how many instructions were executed
        with self._lock:
            self._running.value-=1
            self._count.value += count
            self._lock.notify_all()

    def run(self):
        '''
        Entry point of the Executor; called by workers to start analysis.
        '''
        if self.profiling:
            self._profile.enable()

        policy_order=self.policy_order
        policy=self.policy

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
                #select a suitable state to analyze
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
                        # Make sure current instruction is decoded so that hooks can access it
                        current_state.cpu.decode_instruction(current_state.cpu.PC)

                        # Announce that we're about to execute
                        self.will_execute_pc(current_state)

                        if not current_state.execute():
                            break

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

                    if isinstance(e, SymbolicPCException):
                        current_state.record_branches(vals)

                    def setstate(state, val):
                        # XXX This only applies to ARM since x86 has no conditional instructions
                        if hasattr(state.cpu, 'forceNextInstruction'):
                            state.cpu.forceNextInstruction()
                        state.cpu.write_register(e.reg_name, val)
                    current_state = self.fork(current_state, symbolic, vals, setstate)
                    del vals, symbolic, setstate

                except SymbolicMemoryException as e:
                    logger.error('SymbolicMemoryException at PC: 0x%16x. Cause: %s', current_state.cpu.PC, e.cause)
                    logger.info('Constraint for crashing! %s', e.constraint)

                    children = []
                    with current_state as new_state:
                        new_state.constrain(e.constraint==False)
                        if solver.check(new_state.constraints):
                            self.putState(new_state)
                            children.append(new_state.co)

                    with current_state as new_state:
                        children.append(new_state.co)
                        new_state.constrain(e.constraint)
                        self.newerror(new_state.cpu.PC)
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
                logger.error("Syscall not implemented: %s", str(e))
                self.generate_testcase(current_state, "Unimplemented syscall "+str(e))
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
                logger.error("Exception: %s\n%s", str(e), trace)
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


