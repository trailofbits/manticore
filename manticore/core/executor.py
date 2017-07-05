import sys
import time
import os
import copy
import cPickle
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

from ..utils.nointerrupt import WithKeyboardInterruptAs
from .cpu.abstractcpu import DecodeException, ConcretizeRegister
from .memory import ConcretizeMemory
from .smtlib import solver, Expression, Operators, SolverException, Array, BitVec, Bool, ConstraintSet
from ..utils.event import Eventful
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
    def __init__(self, executor, *args, **kwargs):
        super(Policy, self).__init__(*args, **kwargs)
        self._executor = executor
        self._executor.subscribe('did_add_state', self._add_state_callback)
        
    @contextmanager
    def locked_context(self):
        ''' Policy shared context dictionary '''
        with self._executor.locked_context() as ctx:
            policy_context = ctx.get('policy', None)
            if policy_context is None:
                policy_context = dict()
            yield policy_context
            ctx['policy'] = policy_context

    def _add_state_callback(self, state_id, state):
        ''' Save prepare(state) on policy shared context before 
            the state is stored
        '''
        with self.locked_context() as ctx:
            metric = self.prepare(state)
            if metric is not None:
                ctx[state_id] = metric

    def prepare(self, state):
        ''' Process a state and keep enough data to later decide it's
            priority #fixme rephrase
        '''
        return None

    def choice(self, state_ids):
        ''' Select a state id from states_id.
            self.context has a dict mapping state_ids -> prepare(state)'''
        raise NotImplemented

class Random(Policy):
    def __init__(self, executor, *args, **kwargs):
        super(Random, self).__init__(executor, *args, **kwargs)

    def choice(self, state_ids):
        return random.choice(state_ids)

class Uncovered(Policy):
    def __init__(self, executor, *args, **kwargs):
        super(Uncovered, self).__init__(executor, *args, **kwargs)
        #hook on the necesary executor signals 
        #on callbacks save data in executor.context['policy']

    def prepare(self, state):
        ''' this is what we need to save for choosing later '''
        return state.cpu.PC

    def choice(self, state_ids):
        # Use executor.context['uncovered'] = state_id -> stats
        # am
        with self._executor.locked_context() as ctx: 
            lastpc = ctx['policy']
            visited = ctx.get('visited', ())
            interesting = set()
            for _id in state_ids:
                if lastpc.get(_id, None) not in visited:
                    interesting.add(_id)
            if len(interesting) > 0:
                return random.choice(tuple(interesting))
            else:
                return random.choice(state_ids)


class Executor(Eventful):
    '''
    The executor guides the execution of an initial state or a paused previous run. 
    It handles all exceptional conditions (system calls, memory faults, concretization, etc.)
    '''

    def __init__(self, initial=None, workspace=None, policy='random', context=None, **kwargs):
        super(Executor, self).__init__(**kwargs)

        assert os.path.isdir(workspace), 'Workspace must be a directory'
        self.workspace = workspace
        logger.debug("Workspace set: %s", self.workspace)

        # Signals / Callbacks handlers will be invoked potentially at different 
        # worker processes. State provides a local context to save data.

        #Be sure every state will forward us their signals
        self.subscribe('will_load_state', self._register_state_callbacks)

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
        if context is None:
            context = {}
        self._shared_context = manager.dict(context)
    
        #scheduling priority policy (wip)
        #Set policy
        policies = {'random': Random, 
                    'uncovered': Uncovered
                    }
        self._policy = policies[policy](self)
        assert isinstance(self._policy, Policy)


        if self.load_workspace():
            if initial is not None:
                logger.error("Ignoring initial state")
        else:
            if initial is not None:
                self.add(initial)
                ##FIXME PUBSUB  We need to forward signals here so they get declared
                ##forward signals from initial state so they are declared here
                self.forward_events_from(initial, True)

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



    def _register_state_callbacks(self, state, state_id):
        '''
            Install forwarding callbacks in state so the events can go up. 
            Going up, we prepend state in the arguments.
        ''' 
        #Forward all state signals
        self.forward_events_from(state, True)

    def add(self, state):
        '''
            Enqueue state.
            Save state on storage, assigns an id to it, then add it to the 
            priority queue
        '''
        #save the state to secondary storage
        state_id = self.store(state)
        #add the state to the list of pending states
        self.put(state_id)
        self.publish('did_add_state', state_id, state)
        return state_id

    def load_workspace(self):
        #Browse and load states in a workspace in case we are trying to 
        # continue from paused run
        saved_states = []
        for filename in os.listdir(self.workspace):
            if filename.startswith('state_') and filename.endswith('.pkl'):
                saved_states.append(self._workspace_filename(filename)) 
        
        #We didn't find any saved intermediate states in the workspace
        if not saved_states:
            return False

        #search finalized testcases
        saved_testcases = []
        for filename in os.listdir(self.workspace):
            if filename.startswith('test_') and filename.endswith('.pkl'):
                saved_testcases.append(self._workspace_filename(filename)) 


        #Load saved states into the queue
        for filename in saved_states:
            state_id = int(filename[6:-4])
            self._states.append(state_id)

        #reset test and states counter 
        for filename in saved_states:
            state_id = int(filename[6:-4])
            self._state_count.value = max(self._state_counter.value, state_id)

        for filename in saved_testcases:
            state_id = int(filename[6:-4])
            self._test_count.value = max(self._test_counter.value, state_id)

        #Return True if we have loaded some sates to continue from
        return len(saved_states)>0

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
    def _stop_run(self):
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
            
        state_id = self._policy.choice(list(self._states))
        del  self._states[self._states.index(state_id)]
        return state_id

    ###############################################################
    # File Storage 
    def store(self, state):
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

            f.flush()

        #broadcast event
        self.publish('will_store_state', state, state_id)
        return state_id

    def load(self, state_id):
        ''' Brings a state from storage selected by state_id'''
        if state_id is None:
            return None
        filename = self._state_filename(state_id)
        logger.debug("Restoring state: %s from %s", state_id, filename )

        with open(filename, 'rb') as f:
            loaded_state = cPickle.loads(f.read())

        logger.debug("Removing state %s from storage", state_id)
        os.remove(filename)

        #Broadcast event
        self.publish('will_load_state', loaded_state, state_id)
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
        logger.debug("Generating testcase No. %d  - %s", testcase_id, message)

        #broadcast test generation. This is the time for other modules 
        #to output whatever helps to understand this testcase
        self.publish('will_generate_testcase', state, testcase_id, message)

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
                logger.debug("WARNING: using iterpickle to dump state")
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
            self.publish('will_fork_state', state, expression, solutions, policy)

        #Build and enqueue a state for each solution 
        children = []
        for new_value in solutions:
            with state as new_state:
                new_state.constrain(expression == new_value) #We already know it's sat
                #and set the PC of the new state to the concrete pc-dest
                #(or other register or memory address to concrete)
                setstate(new_state, new_value)
                #enqueue new_state 
                state_id = self.add(new_state)
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
        current_state = None
        current_state_id = None

        with WithKeyboardInterruptAs(self.shutdown):
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
                            #load selected state from secondary storage
                            current_state = self.load(current_state_id)
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
                            self.publish('will_terminate_state', current_state, current_state_id, 'Shutdown')
                            current_state = None


                    #Handling Forking and terminating exceptions
                    except Concretize as e:
                        #expression
                        #policy
                        #setstate()

                        logger.debug("Generic state fork on condition")
                        self.fork(current_state, e.expression, e.policy, e.setstate)
                        current_state = None

                    except TerminateState as e:
                        #Notify this worker is done
                        self.publish('will_terminate_state', current_state, current_state_id, e)

                        logger.debug("Generic terminate state")
                        if e.testcase:
                            self.generate_testcase(current_state, str(e))
                        current_state = None

                    except SolverException as e:
                        import traceback
                        exc_type, exc_value, exc_traceback = sys.exc_info()
                        print "*** print_exc:"
                        traceback.print_exc()

                        #Notify this state is done
                        self.publish('will_terminate_state', current_state, current_state_id, e)

                        if solver.check(current_state.constraints):
                            self.generate_testcase(current_state, "Solver failed" + str(e))
                        current_state = None

                except (Exception, AssertionError) as e:
                    import traceback
                    trace = traceback.format_exc()
                    print str(e), trace
                    logger.error("Exception: %s\n%s", str(e), trace)
                    for trace_line in trace.splitlines():
                        logger.error(trace_line) 
                    #Notify this worker is done
                    self.publish('will_terminate_state', current_state, current_state_id, 'Exception')
                    current_state = None
                    logger.setState(None)
    
            assert current_state is None

            #notify siblings we are about to stop this run
            self._stop_run()

            #Notify this worker is done (not sure it's needed)
            self.publish('will_finish_run', )


