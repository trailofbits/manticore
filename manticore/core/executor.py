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
from .cpu.abstractcpu import DecodeException, ConcretizeRegister
from .memory import ConcretizeMemory
from .smtlib import solver, Expression, Operators, SolverException, Array, BitVec, Bool, ConstraintSet
from ..utils.event import Signal
from ..utils.helpers import issymbolic
from .state import Concretize, TerminateState
from multiprocessing.managers import SyncManager
from contextlib import contextmanager

#This is the single global manager that will handle all shared memory among workers
def mgr_init():
    signal.signal(signal.SIGINT, signal.SIG_IGN)
manager = SyncManager()
manager.start(mgr_init)

#module wide logger
logger = logging.getLogger("EXECUTOR")


def sync(f):
    """ Synchronization decorator. """
    def newFunction(self, *args, **kw):
        self._lock.acquire()
        try:
            return f(self, *args, **kw)
        finally:
            self._lock.release()
    return newFunction


class Policy(object):
    ''' Base class for prioritization of state search '''
    def __init__(self):
        pass

    def features(self, state):
        ''' Save state features for prioritization before a state is stored '''
        pass

    def priority(self, state_id):
        ''' A numeric value representing likelihood to reach the interesting program spot '''
        return 1.0

class Random(Policy):
    def __init__(self):
        super(Random, self).__init__()

    def priority(self, state_id):
        return random.uniform(0,1)

class Executor(object):
    '''
    The executor guides the execution of an initial state or a paused previous run. 
    It handles all exceptional conditions (system calls, memory faults, concretization, etc.)
    '''

    def __init__(self, initial=None, workspace=None, policy='random', **options):
        assert os.path.isdir(workspace), 'Workspace must be a directory'
        self.workspace = workspace
        logger.debug("Workspace set: %s", self.workspace)

        # Signals / Callbacks handlers will be invoked potentially at differeent 
        # worker processes. State provides a local context to save data.

        #Executor
        self.will_start_run = Signal()
        self.will_finish_run = Signal()
        self.will_fork_state = Signal()
        self.will_backup_state = Signal()
        self.will_restore_state = Signal()
        self.will_terminate_state = Signal()
        self.will_generate_testcase = Signal()

        #Cpu
        self.will_decode_instruction = Signal()
        self.will_execute_instruction = Signal()
        self.will_read_register = Signal()
        self.will_write_register = Signal()
        self.will_read_memory = Signal()
        self.will_write_memory = Signal()


        #Be sure every state will forward us their signals
        self.will_restore_state += self._register_state_callbacks

        #The main executor lock. Acquire this for accessing shared objects
        self._lock = manager.Condition(manager.RLock())

        #Shutdown Event
        self._shutdown = manager.Event()

        #States on storage. Shared dict state name ->  state stats
        self._states = manager.list()

        #Number of currently running workers. Initially no runnign workers
        self._running = manager.Value('i', 0 )

        #Number of generated testcases
        self._test_count = manager.Value('i', 0 )

        #Number of total intermediate states
        self._state_count = manager.Value('i', 0 )

        #Executor wide shared context
        self._shared_context = manager.dict()
    
        #scheduling priority policy (wip)
        self.policy = Random()

        if not self._load_workspace():
            state_id = self.backup(initial)
            self._states.append(state_id)

    @contextmanager
    def locked_context(self):
        ''' Executor context is a shared memory object. All workers share this. 
            It needs a lock. Its used like this:

            with executor.context() as context:
                vsited = context['visited']
                visited.append(state.cpu.PC)
                context['visited'] = visited
        '''
        with self._lock:
            yield self._shared_context
        #FIXME What if we do a: 
        # for name,value in self._shared_context.items():
        #   self._shared_context[name]=value
        # too expensive ?


    def _register_state_callbacks(self, state, state_id):
        '''
            Install forwarding callbacks in state so the events can go up. 
            Going up, we prepend state in the arguments.
        ''' 
        self.will_decode_instruction.when(state, state.will_decode_instruction)
        self.will_execute_instruction.when(state, state.will_execute_instruction)
        self.will_read_register.when(state, state.will_read_register)
        self.will_write_register.when(state, state.will_write_register)
        self.will_read_memory.when(state, state.will_read_memory)
        self.will_write_memory.when(state, state.will_write_memory)


    def _load_workspace(self):
        #Browse and load states in a workspace in case we are trying to 
        # continue from paused run
        saved_states = []
        for filename in os.listdir(self.workspace):
            if filename.startswith('state_') and filename.endswith('.pkl'):
                saved_states.append(self._getFilename(filename)) 
        
        #We didn't find any saved intermediate states in the workspace
        if not saved_states:
            return False

        #search finalized testcases
        saved_testcases = []
        for filename in os.listdir(self.workspace):
            if filename.startsswith('test_') and filename.endswith('.pkl'):
                saved_testcases.append(self._getFilename(filename)) 

        if saved_states or saved_testcases:
            #We are trying to continue a paused analysis
            if initial is not None:
                raise Exception('Cant set initial state when continuing from previous workspace: {}'.format(workspace))

        #Load saved states into the queue
        for filename in saved_states:
            #with open(filename, "r") as f:
            #    temp_state = cPickle.loads(f.read())
            #    self.policy.measure(temp_state)
            state_id = int(filename[6:-4])
            self._states.append(state_id)

        #reset test and states counter 
        for filename in saved_states:
            state_id = int(filename[6:-4])
            self._state_counter.value = max(self._state_counter.value, state_id)

        for filename in saved_testcases:
            state_id = int(filename[6:-4])
            self._test_counter.value = max(self._test_counter.value, state_id)
        
        return True

    ################################################
    # Workspace filenames 
    def _workspace_filename(self, filename):
        return os.path.join(self.workspace, filename)

    def _state_filename(self, state_id):
        filename = 'state_%06d.pkl'%state_id
        return self._workspace_filename(filename)

    def _testcase_filename(self, state_id):
        filename = 'test_%06d.pkl'%state_id
        return self._workspace_filename(filename)

    ################################################
    #Shared counters 
    @sync
    def _new_state_id(self):
        ''' This gets an uniq shared id for a new state '''
        self._state_count.value += 1
        return self._state_count.value

    @sync
    def _new_testcase_id(self):
        ''' This gets an uniq shared id for a new testcase '''
        self._test_count.value += 1
        return self._test_count.value

    ###############################################
    # Synchronization helpers
    @sync
    def _start_run(self):
        #notify siblings we are about to start a run()
        self._running.value+=1

    @sync
    def _stop_run(self, count=0):
        #notify siblings we are about to stop this run()
        self._running.value-=1
        assert self._running.value >=0
        self._lock.notify_all()


    ################################################
    #Public API
    @property
    def running(self):
        ''' Report an estimate  of how many workers are currently running '''
        return self._running.value

    def shutdown(self):
        ''' This will stop all workers '''
        self._shutdown.set()

    def is_shutdown(self):
        ''' Returns True if shutdown was requested '''
        return self._shutdown.is_set()


    ###############################################
    # Priority queue 
    @sync
    def put(self, state_id):
        ''' Enqueue it for processing '''
        self._states.append(state_id)
        self._lock.notify_all()
        return state_id

    @sync
    def get(self):
        ''' Dequeue a state with the max priority '''

        #A shutdown has been requested
        if self.is_shutdown():
            return None

        #if not more states in the queue lets wait for some forks
        while len(self._states) == 0:
            #if no worker is running bail out
            if self.running == 0:
                return None
            #if a shutdown has been requested bail out
            if self.is_shutdown():
                return None
            #if there is actually some workers running wait for state forks
            logger.debug("Waiting for available states")
            self._lock.wait()
            
        state_id = random.choice(self._states)
        del  self._states[self._states.index(state_id)]
        return state_id

    ###############################################################
    # File Storage 
    def backup(self, state):
        ''' Put state in secondary storage and retuns an state_id for it'''
        state_id = self._new_state_id()
        state_filename = self._state_filename(state_id)
        logger.debug("Saving state %d to file %s", state_id, state_filename)
        with open(state_filename, 'w+') as f:
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

        #broadcast event
        self.will_backup_state(state, state_id)

        return state_id

    def restore(self, state_id):
        ''' Brings a state from storage selected by state_id'''
        if state_id is None:
            return None
        filename = self._state_filename(state_id)
        logger.info("Restoring state: %s from %s", state_id, filename )

        with open(filename, 'rb') as f:
            loaded_state = cPickle.loads(f.read())

        logger.info("Removing state %s from storage", state_id)
        os.remove(filename)

        #Broadcast event
        self.will_restore_state(loaded_state, state_id)
        return loaded_state 

    def list(self):
        ''' Returns the list of states ids currently queued '''
        return list(self._states)

    def generate_testcase(self, state, message = 'Testcase generated'):
        '''
        Create a serialized description of a given state.

        :param state: The state to generate information about
        :param message: Accompanying message
        '''
        testcase_id = self._new_testcase_id()
        logger.info("Generating testcase No. %d  - %s", testcase_id, message)

        #broadcast test generation. This is the time for other modules 
        #to output whatever helps to understand this testcase
        self.will_generate_testcase(state, testcase_id, message)

        # Save state
        start = time.time()
        filename = self._testcase_filename(testcase_id)
        with open(filename, 'wb') as f:
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


    def fork(self, state, expression, policy='ALL', setstate=None):
        '''
        Fork state on expression concretizations.
        Using policy build a list of solutions for expression.
        For the state on each solution setting the new state with setstate 

        For example if expression is a Bool it may have 2 solutions. True or False.
    
                                 Parent  
                            (expression = ??)
       
                   Child1                         Child2
            (expression = True)             (expression = True)
               setstate(True)                   setstate(False)

        The optional setstate() function is supposed to set the concrete value 
        in the child state.
        
        '''
        assert isinstance(expression, Expression)

        if setstate is None:
            setstate = lambda x,y: None

        #Find a set of solutions for expression
        solutions = state.concretize(expression, policy)

        #We are about to fork current_state
        with self._lock:
            self.will_fork_state(state, expression, solutions, policy)

        #Build and enqueue a state for each solution 
        children = []
        for new_value in solutions:
            with state as new_state:
                new_state.constrain(expression == new_value) #We already know it's sat
                #and set the PC of the new state to the concrete pc-dest
                #(or other register or memory address to concrete)
                setstate(new_state, new_value) 
                #save the state to secondary storage
                state_id = self.backup(new_state)
                #add the state to the list of pending states
                self.put(state_id)
                #maintain a list of childres for logging purpose
                children.append(state_id)
        
        logger.debug("Forking current state into states %r",children)
        return None

    def run(self):
        '''
        Entry point of the Executor; called by workers to start analysis.
        '''

        #policy_order=self.policy_order
        #policy=self.policy

        count = 0
        current_state = None
        current_state_id = None

        with DelayedKeyboardInterrupt():
            #notify siblings we are about to start a run
            self._start_run()

        logger.debug("Starting Manticore Symbolic Emulator Worker (pid %d).",os.getpid())


        while not self.is_shutdown():
            try:
                #select a suitable state to analyze
                if current_state is None:

                    with self._lock:
                        #notify siblings we are about to stop this run
                        self._stop_run()
                        #Select a single state_id
                        current_state_id = self.get()
                        #Restore selected state from secondary storage
                        current_state = self.restore(current_state_id)
                        #notify siblings we have a state to play with
                        self._start_run()

                    #If current_state is still None. We are done.
                    if current_state is None:
                        logger.debug("No more states in the queue, byte bye!")
                        break
                    
                    assert current_state is not None

                try:

                    # Allows to terminate manticore worker on user request
                    while not self.is_shutdown():
                        if not current_state.execute():
                            break
                    else:
                        #Notify this worker is done
                        self.will_terminate_state(current_state, 'Shutdown')
                        current_state = None


                #Handling Forking and terminating exceptions
                except Concretize as e:
                    #expression
                    #policy
                    #setstate()

                    logger.info("Generic state fork on condition")
                    self.fork(current_state, e.expression, e.policy, e.setstate)
                    current_state = None

                except TerminateState as e:
                    #logger.error("MemoryException at PC: 0x{:016x}. Cause: {}\n".format(current_state.cpu.instruction.address, e.cause))
                    #self.generate_testcase(current_state, "Memory Exception: " + str(e))
                    #self.generate_testcase(current_state, "Invalid PC Exception" + str(e))
                    #self.generate_testcase(current_state, "Program finished correctly")
                    #logger.error("Syscall not implemented: %s", str(e))

                    #Notify this worker is done
                    self.will_terminate_state(current_state, current_state_id, e)

                    logger.info("Generic terminate state")
                    if e.testcase:
                        self.generate_testcase(current_state, str(e))
                    current_state = None


                except SolverException as e:
                    import traceback
                    exc_type, exc_value, exc_traceback = sys.exc_info()
                    print "*** print_exc:"
                    traceback.print_exc()

                    #Notify this worker is done
                    self.will_terminate_state(current_state, e)

                    if solver.check(current_state.constraints):
                        self.generate_testcase(current_state, "Solver failed" + str(e))
                    current_state = None

            except KeyboardInterrupt as e:
                logger.error("Interrupted!")
                #Notify this worker is done
                self.will_terminate_state(current_state, e)

                logger.setState(None)
                current_state = None
                break

            except AssertionError as e:

                #Notify this worker is done
                self.will_terminate_state(current_state, e)


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
                #Notify this worker is done
                self.will_terminate_state(current_state, e)
                current_state = None

        with DelayedKeyboardInterrupt():
            #notify siblings we are about to stop this run
            self._stop_run()


        #Notify this worker is done (not sure it's needed)
        self.will_finish_run()


