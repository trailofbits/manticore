
import os
import random
import logging
import signal

from ..exceptions import ExecutorError, SolverError
from ..utils.nointerrupt import WithKeyboardInterruptAs
from ..utils.event import Eventful
from ..utils import config
from .smtlib import Z3Solver, Expression
from .state import Concretize, TerminateState

from .workspace import Workspace
from multiprocessing.managers import SyncManager
from contextlib import contextmanager

# This is the single global manager that will handle all shared memory among workers

consts = config.get_group('executor')
consts.add('seed', default=1337, description='The seed to use when randomly selecting states')


def mgr_init():
    signal.signal(signal.SIGINT, signal.SIG_IGN)


logger = logging.getLogger(__name__)


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
        super().__init__(*args, **kwargs)
        self._executor = executor
        self._executor.subscribe('did_enqueue_state', self._add_state_callback)

    @contextmanager
    def locked_context(self, key=None, default=dict):
        ''' Policy shared context dictionary '''
        keys = ['policy']
        if key is not None:
            keys.append(key)
        with self._executor.locked_context('.'.join(keys), default) as policy_context:
            yield policy_context

    def _add_state_callback(self, state_id, state):
        ''' Save summarize(state) on policy shared context before
            the state is stored
        '''
        summary = self.summarize(state)
        if summary is None:
            return
        with self.locked_context('summaries', dict) as ctx:
            ctx[state_id] = summary

    def summarize(self, state):
        '''
            Extract the relevant information from a state for later
            prioritization
        '''
        return None

    def choice(self, state_ids):
        ''' Select a state id from state_ids.
            self.context has a dict mapping state_ids -> summarize(state)'''
        raise NotImplementedError


class Random(Policy):
    def __init__(self, executor, *args, **kwargs):
        super().__init__(executor, *args, **kwargs)
        random.seed(consts.seed)  # For repeatable results

    def choice(self, state_ids):
        return random.choice(state_ids)


class Uncovered(Policy):
    def __init__(self, executor, *args, **kwargs):
        super().__init__(executor, *args, **kwargs)
        # hook on the necessary executor signals
        # on callbacks save data in executor.context['policy']
        with self._executor.locked_context() as ctx:
            ctx['policy'] = {}
        self._executor.subscribe('will_load_state', self._register)

    def _register(self, *args):
        self._executor.subscribe('will_execute_instruction', self._visited_callback)

    def _visited_callback(self, state, pc, instr):
        ''' Maintain our own copy of the visited set
        '''
        with self.locked_context('visited', set) as ctx:
            ctx.add(pc)

    def summarize(self, state):
        ''' Save the last pc before storing the state '''
        return state.platform.PC

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
        return random.choice(tuple(interesting))


class BranchLimited(Policy):
    def __init__(self, executor, *args, **kwargs):
        super().__init__(executor, *args, **kwargs)
        self._executor.subscribe('will_load_state', self._register)
        self._limit = kwargs.get('limit', 5)

    def _register(self, *args):
        self._executor.subscribe('will_execute_instruction', self._visited_callback)

    def _visited_callback(self, state, pc, instr):
        ''' Maintain our own copy of the visited set
        '''
        pc = state.platform.current.PC
        with self.locked_context('visited', dict) as ctx:
            ctx[pc] = ctx.get(pc, 0) + 1

    def summarize(self, state):
        return state.cpu.PC

    def choice(self, state_ids):
        interesting = set(state_ids)
        with self.locked_context() as policy_ctx:
            visited = policy_ctx.get('visited', dict())
            summaries = policy_ctx.get('summaries', dict())
        lst = []
        for id_, pc in summaries.items():
            cnt = visited.get(pc, 0)
            if id_ not in state_ids:
                continue
            if cnt <= self._limit:
                lst.append((id_, visited.get(pc, 0)))
        lst = sorted(lst, key=lambda x: x[1])

        if lst:
            return lst[0][0]
        else:
            return None


class Executor(Eventful):
    '''
    The executor guides the execution of a single state, handles state forking
    and selection, maintains run statistics and handles all exceptional
    conditions (system calls, memory faults, concretization, etc.)
    '''

    _published_events = {'enqueue_state', 'generate_testcase', 'fork_state', 'load_state', 'terminate_state'}

    def __init__(self, initial=None, store=None, policy='random', context=None, **kwargs):
        super().__init__(**kwargs)

        # Signals / Callbacks handlers will be invoked potentially at different
        # worker processes. State provides a local context to save data.

        self.subscribe('did_load_state', self._register_state_callbacks)

        # This is the global manager that will handle all shared memory access among workers
        self.manager = SyncManager()
        self.manager.start(lambda: signal.signal(signal.SIGINT, signal.SIG_IGN))

        # The main executor lock. Acquire this for accessing shared objects
        self._lock = self.manager.Condition()

        # Shutdown Event
        self._shutdown = self.manager.Event()

        # States on storage. Shared dict state name ->  state stats
        self._states = self.manager.list()

        # Number of currently running workers. Initially no running workers
        self._running = self.manager.Value('i', 0)

        self._workspace = Workspace(self._lock, store)

        # Executor wide shared context
        if context is None:
            context = {}
        self._shared_context = self.manager.dict(context)

        # scheduling priority policy (wip)
        # Set policy
        policies = {'random': Random,
                    'uncovered': Uncovered,
                    'branchlimited': BranchLimited,
                    }
        self._policy = policies[policy](self)
        assert isinstance(self._policy, Policy)

        if self.load_workspace():
            if initial is not None:
                logger.error("Ignoring initial state")
        else:
            if initial is not None:
                self.add(initial)

    def __del__(self):
        self.manager.shutdown()

    @contextmanager
    def locked_context(self, key=None, default=dict):
        ''' Executor context is a shared memory object. All workers share this.
            It needs a lock. Its used like this:

            with executor.context() as context:
                visited = context['visited']
                visited.append(state.cpu.PC)
                context['visited'] = visited
        '''
        assert default in (list, dict, set)
        with self._lock:
            if key is None:
                yield self._shared_context
            else:
                sub_context = self._shared_context.get(key, None)
                if sub_context is None:
                    sub_context = default()
                yield sub_context
                self._shared_context[key] = sub_context

    def _register_state_callbacks(self, state, state_id):
        '''
            Install forwarding callbacks in state so the events can go up.
            Going up, we prepend state in the arguments.
        '''
        # Forward all state signals
        self.forward_events_from(state, True)

    def enqueue(self, state):
        '''
            Enqueue state.
            Save state on storage, assigns an id to it, then add it to the
            priority queue
        '''
        # save the state to secondary storage
        state_id = self._workspace.save_state(state)
        self.put(state_id)
        self._publish('did_enqueue_state', state_id, state)
        return state_id

    def load_workspace(self):
        # Browse and load states in a workspace in case we are trying to
        # continue from paused run
        loaded_state_ids = self._workspace.try_loading_workspace()
        if not loaded_state_ids:
            return False

        for id in loaded_state_ids:
            self._states.append(id)

        return True

    ###############################################
    # Synchronization helpers
    @sync
    def _notify_start_run(self):
        # notify siblings we are about to start a run()
        self._running.value += 1

    @sync
    def _notify_stop_run(self):
        # notify siblings we are about to stop this run()
        self._running.value -= 1
        if self._running is None or self._running.value < 0:
            raise SystemExit
        self._lock.notify_all()

    ################################################
    # Public API
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

        # A shutdown has been requested
        if self.is_shutdown():
            return None

        # if not more states in the queue, let's wait for some forks
        while len(self._states) == 0:
            # if no worker is running, bail out
            if self.running == 0:
                return None
            # if a shutdown has been requested, bail out
            if self.is_shutdown():
                return None
            # if there ares actually some workers running, wait for state forks
            logger.debug("Waiting for available states")
            self._lock.wait()

        state_id = self._policy.choice(list(self._states))
        if state_id is None:
            return None
        del self._states[self._states.index(state_id)]
        return state_id

    def list(self):
        ''' Returns the list of states ids currently queued '''
        return list(self._states)

    def generate_testcase(self, state, message='Testcase generated'):
        '''
        Simply announce that we're going to generate a testcase. Actual generation
        should be handled by the driver class (such as :class:`~manticore.Manticore`)

        :param state: The state to generate information about
        :param message: Accompanying message
        '''

        # broadcast test generation. This is the time for other modules
        # to output whatever helps to understand this testcase
        self._publish('will_generate_testcase', state, 'test', message)

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
            setstate = lambda x, y: None

        # Find a set of solutions for expression
        solutions = state.concretize(expression, policy)

        if not solutions:
            raise ExecutorError("Forking on unfeasible constraint set")

        if len(solutions) == 1:
            setstate(state, solutions[0])
            return state

        logger.info("Forking. Policy: %s. Values: %s",
                    policy,
                    ', '.join(f'0x{sol:x}' for sol in solutions))

        self._publish('will_fork_state', state, expression, solutions, policy)

        # Build and enqueue a state for each solution
        children = []
        for new_value in solutions:
            with state as new_state:
                new_state.constrain(expression == new_value)

                # and set the PC of the new state to the concrete pc-dest
                #(or other register or memory address to concrete)
                setstate(new_state, new_value)

                self._publish('did_fork_state', new_state, expression, new_value, policy)

                # enqueue new_state
                state_id = self.enqueue(new_state)
                # maintain a list of children for logging purpose
                children.append(state_id)

        logger.info("Forking current state into states %r", children)
        return None

    def run(self):
        '''
        Entry point of the Executor; called by workers to start analysis.
        '''
        # policy_order=self.policy_order
        # policy=self.policy
        current_state = None
        current_state_id = None

        with WithKeyboardInterruptAs(self.shutdown):
            # notify siblings we are about to start a run
            self._notify_start_run()

            logger.debug("Starting Manticore Symbolic Emulator Worker (pid %d).", os.getpid())
            solver = Z3Solver()
            while not self.is_shutdown():
                try:  # handle fatal errors: exceptions in Manticore
                    try:  # handle external (e.g. solver) errors, and executor control exceptions
                        # select a suitable state to analyze
                        if current_state is None:
                            with self._lock:
                                # notify siblings we are about to stop this run
                                self._notify_stop_run()
                                try:
                                    # Select a single state_id
                                    current_state_id = self.get()
                                    # load selected state from secondary storage
                                    if current_state_id is not None:
                                        self._publish('will_load_state', current_state_id)
                                        current_state = self._workspace.load_state(current_state_id)
                                        self.forward_events_from(current_state, True)
                                        self._publish('did_load_state', current_state, current_state_id)
                                        logger.info("load state %r", current_state_id)
                                    # notify siblings we have a state to play with
                                finally:
                                    self._notify_start_run()

                        # If current_state is still None. We are done.
                        if current_state is None:
                            logger.debug("No more states in the queue, byte bye!")
                            break

                        assert current_state is not None
                        assert current_state.constraints is current_state.platform.constraints

                        # Allows to terminate manticore worker on user request
                        while not self.is_shutdown():
                            if not current_state.execute():
                                break
                        else:
                            # Notify this worker is done
                            self._publish('will_terminate_state', current_state, current_state_id, TerminateState('Shutdown'))
                            current_state = None

                    # Handling Forking and terminating exceptions
                    except Concretize as e:
                        # expression
                        # policy
                        # setstate()
                        logger.debug("Generic state fork on condition")
                        current_state = self.fork(current_state, e.expression, e.policy, e.setstate)

                    except TerminateState as e:
                        # Notify this worker is done
                        self._publish('will_terminate_state', current_state, current_state_id, e)

                        logger.debug("Generic terminate state")
                        if e.testcase:
                            self.generate_testcase(current_state, str(e))
                        current_state = None

                    except SolverError as e:
                        # raise
                        import traceback
                        trace = traceback.format_exc()
                        logger.error("Exception: %s\n%s", str(e), trace)

                        # Notify this state is done
                        self._publish('will_terminate_state', current_state, current_state_id, e)

                        if solver.check(current_state.constraints):
                            self.generate_testcase(current_state, "Solver failed" + str(e))
                        current_state = None

                except (Exception, AssertionError) as e:
                    # raise
                    import traceback
                    trace = traceback.format_exc()
                    logger.error("Exception: %s\n%s", str(e), trace)
                    # Notify this worker is done
                    self._publish('will_terminate_state', current_state, current_state_id, e)
                    current_state = None
                    logger.setState(None)

            assert current_state is None or self.is_shutdown()

            # notify siblings we are about to stop this run
            self._notify_stop_run()
