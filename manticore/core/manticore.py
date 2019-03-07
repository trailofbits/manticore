import cProfile
import itertools
import logging
import os
import pstats
import sys
import time
import random
from contextlib import contextmanager

import functools
import shlex

from ..core.plugin import Plugin
from ..core.smtlib import Expression
from ..core.state import TerminateState, StateBase
from ..core.workspace import ManticoreOutput
from ..utils import config
from ..utils import log
from ..utils.event import Eventful
from ..utils.helpers import PickleSerializer
from ..utils.nointerrupt import WithKeyboardInterruptAs
from .workspace import Workspace
from .state import Concretize, TerminateState

from multiprocessing.managers import SyncManager, threading, MakeProxyType, BaseListProxy, ListProxy, ArrayProxy, DictProxy
from multiprocessing import Process
from threading import Timer, Thread
import ctypes
import signal

logger = logging.getLogger(__name__)

consts = config.get_group('core')
consts.add('timeout', default=0, description='Timeout, in seconds, for Manticore invocation')
consts.add('cluster', default=False, description='If True enables to run workers over the network UNIMPLEMENTED')
consts.add('profile', default=False, description='Enable worker profiling mode')
consts.add('procs', default=10, description='Number of parallel processes to spawn')
consts.add('mprocessing', default='single', description='single: No multiprocessing at all. Single process.\n')

# Add on to Multiprocessing. Hack. ThinkMe
SetBaseProxy = MakeProxyType('SetBaseProxy', (
    '__contains__', 'add', 'clear', 'copy', 'difference',
    'difference_update', 'discard', 'intersection', 'intersection_update',
    'isdisjoint', 'issubset', 'issuperset', 'pop', 'remove',
    'symmetric_difference', 'symmetric_difference_update', 'union', 'update'
))
class SetProxy(SetBaseProxy):
    def __iadd__(self, value):
        self._callmethod('extend', (value,))
        return self
    def __imul__(self, value):
        self._callmethod('__imul__', (value,))
        return self
    def add(self, value):
        self._callmethod('add', (value,))
        return self


SyncManager.register('set', set, SetProxy)


# Workers
# There are 4 types of Workers
# WorkerSingle: run over main process and will not provide any concurrency
# WorkerThread: runs on a different thread
# WorkerProcess: runs on a different process - Full multiprocessing

class Worker:
    """
        A Manticore Worker.
        This will run forever potentially in a different process. Normally it
        will be spawned at Manticore constructor and will stay alive until killed.
        A Worker can be in 3 phases: STANDBY, RUNNING, KILLED. And will react to
        different events: start, stop, kill.
        The events are transmitted via 2 conditional variable: m._killed and
        m._started.

            STANDBY:   Waiting for the start event
            RUNNING:   Exploring and spawning states until no more READY states or
                       the cancel event is received
            KIlLED:    This is the end. No more manticoring in this worker process

                         +---------+     +---------+
                    +--->+ STANDBY +<--->+ RUNNING |
                         +-+-------+     +-------+-+
                           |                     |
                           |      +--------+     |
                           +----->+ KILLED <-----+
                                  +----+---+
                                       |
                                       #
    """

    def __init__(self, *, id, manticore, single=False):
        self.manticore = manticore
        self.id = id
        self.single = single

    def start(self):
        raise NotImplementedError

    def join(self):
        raise NotImplementedError

    def run(self, *args):
        # This controls the main symbolic execution loop and it is one of the 
        # most critical manticore code. Please 
        logger.debug("Starting Manticore Symbolic Emulator Worker. Pid %d Tid %d).", os.getpid(), threading.get_ident())
        m = self.manticore
        current_state = None
        # If CTRL+C is received at any worker lets abort exploration via m.kill()
        # kill will set m._killed flag to true and the each worker needs to slowly
        # get out of its mainloop and quit.
        with WithKeyboardInterruptAs(m.kill):

            # The worker runs until the manticore is killed
            while True:

                # STARTED - Will try to consume states until a STOP event is received
                # Outter loop, Keep getting states until someone request us to STOP
                try:  # handle fatal errors even exceptions in the exception handlers
                    # Iff a kill or stop was received and we have a state in
                    # the works lets dump it to storage and revive it
                    # Not that kill is only one way though the stop/start can flicker
                    if current_state is not None and (not m._started.value or m._killed.value):
                        # On going execution was stopped or killed. Lets 
                        # save any progress on the current state
                        m._save(current_state)
                        m._revive(current_state.id)
                        current_state = None

                    # If at STANDBY wait for any change
                    with m._lock:
                        i = 0
                        while not m._started.value and not m._killed.value:
                            i += 1
                            logger.info("[%r] StandBy", self.id)
                            m._lock.wait()  # Wait until something changes

                    # Check for user request cancellation
                    if m._killed.value:
                        logger.info("[%r] Cancelled", self.id)
                        break

                    try:  # handle Concretize and TerminateState

                        # At RUNNING
                        # The START has been requested, we operate with under the assumption
                        # that manticore we will let us stay at this phase for a _while_
                        # Requests to STOP will we honored ASAP (i.e. Not immediatelly)

                        # if no state then select a suitable state to analyze
                        if current_state is None:
                            # Select a single state
                            # wait for other worker to add states to the READY list
                            # This momentarilly get the main lock and then releases 
                            # it while waiting for changes
                            # Raises an Exception if manticore gets cancelled
                            # while waiting or if there are no more potential states
                            logger.info("[%r] Waiting for states", self.id)
                            current_state = m._get_state(wait=True)

                            # there are no more states to proccess lets STOP
                            if current_state is None:
                                logger.info("[%r] No more states", self.id)
                                m.stop()
                                if self.single:
                                    break
                                else:
                                    continue

                        # assert current_state is not None
                        # Allows to terminate manticore worker on user request
                        # even in the middle of an execution
                        logger.info("[%r] Running", self.id)
                        while m._started.value and not m._killed.value:
                            current_state.execute()
                        else:
                            logger.info("[%r] Stopped or Cancelled", self.id)

                    # Handling Forking and terminating exceptions
                    except Concretize as exc:
                        logger.info("[%r] Debug %r", self.id, exc)
                        # The fork() method can decides which state to keep
                        # exploring. For example when the fork results in a 
                        # single state it is better to just keep going. 
                        # Though, normally fork() saves the spawned childs,
                        # returns a None and let _get_state choose what to explore
                        # next
                        current_state = m._fork(current_state, exc.expression, exc.policy, exc.setstate)
                        # here: likely current_state is None

                    except TerminateState as exc:
                        logger.info("[%r] Debug State %r %r", self.id, current_state, exc)
                        # Notify this state is done
                        m._publish('will_terminate_state', current_state, exc)
                        # Update the stored version of the current state 
                        m._save(current_state)
                        # Add the state to the terminated state list
                        m._terminate(current_state.id)
                        m._publish('did_terminate_state', current_state, exc)

                        current_state = None

                except (Exception, AssertionError) as exc:
                    logger.error("[%r] Exception %r. Current State %r", self.id, exc, current_state)
                    #import traceback; traceback.print_exc()
                    # Internal Exception. 
                    # Add the state to the terminated state list
                    if current_state is not None:
                        # Drop any work on this state in case it is inconsistent
                        with m._lock:
                            m._busy_states.remove(current_state.id)
                            m._killed_states.append(current_state.id)
                        current_state = None
                    break

            # Getting out.
            # At KILLED
            logger.info("[%r] Getting out of the mainloop %r %r", self.id, m._started.value, m._killed.value)


class WorkerSingle(Worker):
    """ A single worker that will run in the current process and current thread.
        As this will not provide any concurrency is normally only used for
        profiling underlying arch emulation and debugging."""
    def __init__(self, *args, **kwargs):
        super().__init__(*args, single=True, **kwargs)

    def start(self):
        pass

    def join(self):
        pass

class WorkerThread(Worker):
    """ A worker thread """
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._t = Thread(target=self.run)

    def start(self):
        self._t.start()

    def join(self):
        self._t.join()

class WorkerProcess(Worker):
    """ A worker process """
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._p = Process(target=self.run)

    def start(self):
        self._p.start()

    def join(self):
        self._p.join()


class ManticoreBase(Eventful):
    '''
    Base class for the central analysis object.
    '''

    # Decorators added first for convenience.
    def sync(func):
        """Synchronization decorator"""

        @functools.wraps(func)
        def newFunction(self, *args, **kw):
            with self._lock:
                return func(self, *args, **kw)

        return newFunction

    def at_running(func):
        """Allows the decorated method to run only when manticore is actively
           exploring states
        """

        @functools.wraps(func)
        def newFunction(self, *args, **kw):
            if not self.is_running():
                raise Exception(f"{func.__name__} only allowed while exploring states")
            return func(self, *args, **kw)

        return newFunction

    def at_not_running(func):
        """Allows the decorated method to run only when manticore is NOT 
           exploring states
        """

        @functools.wraps(func)
        def newFunction(self, *args, **kw):
            if self.is_running():
                raise Exception(f"{func.__name__} only allowed while not exploring states")
            return func(self, *args, **kw)

        return newFunction

    def at_standby(func):
        """Allows the decorated method to run only when manticore is at STANDBY """

        @functools.wraps(func)
        def newFunction(self, *args, **kw):
            if not self.is_standby():
                raise Exception(f"{func.__name__} only allowed at standby")
            return func(self, *args, **kw)

        return newFunction

    _published_events = {'start_run', 'finish_run', 'generate_testcase', 'enqueue_state', 'fork_state', 'load_state',
                         'terminate_state', 'internal_generate_testcase', 'execute_instruction'}

    def __init__(self, initial_state, workspace_url=None, policy='random', **kwargs):
        """

                   Manticore symbolically explores program states.


        Manticore phases
        ****************

        Manticore has multiprocessing capabilities. Several worker processes 
        could be registered to do concurrent exploration of the READY states.
        Manticore can be itself at different phases: STANDBY, RUNNING, KILLED.

                      +---------+               +---------+
                ----->| STANDBY +<------------->+ RUNNING |
                      +---------+               +----+----+
                                                     |
                                                     V
                                               +-----------+
                                               | KILLED |
                                               +-----------+

        = Phase STANDBY =
        Manticore starts at STANDBY with a single initial state. Here the user 
        can inspect, modify and generate testcases for the different states. The
        workers are paused and not doing any work. Actions: start(), cancel()


        = Phase RUNNING =
        At RUNNING the workers consume states from the READY state list and 
        potentially fork new states or terminate states. A RUNNING manticore can
        be stopped back to STANDBY or cancelled to KILLED. Actions: stop(), 
        cancel()


        = Phase KILLED =
        Manticore moves to KILLED on a timeout or when the user requests 
        termination via CTRL+C. At KILLED the workers are stoped and killed
        and the outstanding states are moved to a specific "KILLED" list. 
        Actions: none
        


        States and state lists
        **********************

        A state contains all the information of the running program at a given 
        moment. State snapshots are saved to the workspace often. Internally 
        Manticore associates a fresh id with each saved state. The memory copy 
        of the state is then changed by the emulation of the specific arch. 
        Stored snapshots are periodically updated using: _save() and _load().

                      _save     +-------------+  _load
            State  +----------> |  WORKSPACE  +----------> State
                                +-------------+

        During exploration Manticore spawns a number of temporary states that are
        maintained in different lists:

                Initial
                State
                  |   +-+---{fork}-----+
                  |   | |              |
                  V   V V              |
                +---------+        +---+----+      +------------+
                |  READY  +------->|  BUSY  +----->| TERMINATED |
                +---------+        +---+----+      +------------+
                     |
                     |                             +----------+
                     +---------------------------->| KILLED |
                                                   +----------+

        At any given time a state must be at the READY, BUSY, TERMINATED or 
        KILLED list.

        State list: READY
        =================
        The READY list holds all the runnable states. Internally a state is 
        added to the READY list via method `_put_state(state)`. Workers take
        states from the READY list via the `_get_state(wait=True|False)` method.
        A worker mainloop will consume states from the READY list and mark them
        as BUSYwhile working on them. States in the READY list can go to BUSY or
        KILLED


        State list: BUSY
        =================
        When a state is selected for exploration from the READY list it is 
        marked as busy and put in the BUSY list. States being explored will be 
        constantly modified  and only saved back to storage when moved out of 
        the BUSY list. Hence, when at BUSY the stored copy of the state will be 
        potentially outdated. States in the BUSY list can go to TERMINATED, 
        KILLED or they can be {forked} back to READY. The forking process 
        could involve generating new child states and removing the parent 
        from all the lists.


        State list: TERMINATED
        ======================
        TERMINATED contains states that have reached a final condition and raised
        TerminateState. Workers mainloop simpliy move the states that requested 
        termination to the TERMINATED list. This is a final list.

        ```An inherited Manticore class like ManticoreEVM could internally revive 
        the states in TERMINATED that pass some condition and move them back to 
        READY so the user can apply a following transaction. ```

        State list: KILLED
        ======================
        KILLED contains all the READY and BUSY states found at a cancel event.
        Manticore supports interactive analysis and has a prominetnt event system
        A useror ui can stop or cancel the exploration at any time. The unfinnished
        states cought at this situation are simply moved to its own list for
        further user action. This is a final list.



        :param initial_state: the initial root `State` object
        :type state: State
        :param workspace_url: workspace folder name
        :param policy: scheduling policy
        :param kwargs: other kwargs, e.g.
        """
        super().__init__()

        # FIXME better Metaprogramming?
        if any(not hasattr(self, x) for x in ( '_worker_type', '_lock', '_started', '_killed', '_ready_states', '_terminated_states', '_killed_states',
        '_busy_states', '_shared_context', '_context_value_types')):
            raise Exception('Need to instantiate one of: ManticoreNative, ManticoreThreads..')

        # The workspace
        # Manticore will use the workspace to save and share temporary states 
        # and it will save the final reports there (if any)
        # Check type, default to fs:
        if isinstance(workspace_url, str):
            if ':' not in workspace_url:
                workspace_url = f'fs:{workspace_url}'
        else:
            if workspace_url is not None:
                raise TypeError(f'Invalid workspace type: {type(workspace_url).__name__}')
        self._workspace = Workspace(self._lock, workspace_url)
        self._output = ManticoreOutput(workspace_url)

        # The set of registered plugins
        # The callback methos defined in the plugin object will be called when 
        # the different type of events occur over an exploration.
        # Note that each callback will run in a worker process and that some
        # careful use of the shared context is needed.
        self.plugins = set()

        # Set initial root state
        if not isinstance(initial_state, StateBase):
            raise TypeError(f'Invalid initial_state type: {type(initial_state).__name__}')
        self._put_state(initial_state)


        # Workers will use manticore __dict__ So lets spawn them last
        self._workers = [self._worker_type(id=i, manticore=self) for i in range(consts.procs)]
        '''
        # FIXME move the following to a plugin
        self.subscribe('did_finish_run', self._did_finish_run_callback)
        self.subscribe('internal_generate_testcase', self._publish_generate_testcase)
        last_run_stats = {}
        '''

    def _fork(self, state, expression, policy='ALL', setstate=None):
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
            raise ManticoreError("Forking on unfeasible constraint set")

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
                # (or other register or memory address to concrete)
                setstate(new_state, new_value)

                # enqueue new_state
                new_state_id = self._save(new_state)
                with self._lock:
                    self._ready_states.append(new_state_id)
                    self._lock.notify_all()  # Must notify one!

                self._publish('did_fork_state', new_state, expression, new_value, policy)
                # maintain a list of children for logging purpose
                children.append(new_state_id)

        with self._lock:
            self._busy_states.remove(state.id)
            self._remove(state.id)
            self._lock.notify_all()

        logger.info("Forking current state %r into states %r", state.id, children)
        return None

    # State storage
    def _save(self, state):
        """ Store or update a state in secondary storage under state.id.
            Use a fresh state.id is None is provided.

            :param state: A manticore State
            :param state_id: if not None force state_id (overwrite)
            :type state_id: int or None
            :returns: the state id used
        """
        state_id = self._workspace.save_state(state, state_id=getattr(state, 'id', None))
        state.id = state_id
        return state_id

    def _load(self, state_id):
        """ Load the state from the secondary storage

            :param state_id: a estate id 
            :type state_id: int
            :returns: the state id used
        """
        self._publish('will_load_state', state_id)
        state = self._workspace.load_state(state_id, delete=False)
        state.id = state_id
        self.forward_events_from(state, True)
        self._publish('did_load_state', state, state_id)
        return state

    def _remove(self, state_id):
        """ Remove a state from secondary storage

            :param state_id: a estate id 
            :type state_id: int
        """
        self._workspace.rm_state(state_id)

    # Internal support for state lists
    def _put_state(self, state):
        """ This enqueues the state for exploration.

            Serialize and store the state with a fresh state_id. Then add it to
            the shared READY states list

                          +-------+
            State +----- >+ READY |
                          +-------+

        """
        state_id = self._save(state)
        with self._lock:
            # Enqueue it in the ready state list for processing 
            self._ready_states.append(state_id)
            self._lock.notify_all()
        return state_id

    def _get_state(self, wait=False):
        """ Dequeue a state form the READY list and add it to the BUSY list """
        with self._lock:
            # If wait is true do the conditional wait for states
            if wait:
                # if not more states in the queue, let's wait for some forks
                while not self._ready_states:
                    # if a shutdown has been requested then bail
                    if self.is_killed():
                        return None  # Cancelled operation
                    # If there are no more READY states and no more BUSY states
                    # there is no chance we will get any new state so raise
                    if not self._busy_states:
                        self.stop()  # A stopping point
                        return None  # There are not states

                    # if there ares actually some workers ready, wait for state forks
                    logger.debug("Waiting for available states")
                    self._lock.wait()

            # at this point we know there is at least one element
            # and we have exclusive access
            assert self._ready_states

            # make the choice under exclusive access to the shared ready list
            # state_id = self._policy.choice(list(self._ready_states)[0])
            state_id = random.choice(list(self._ready_states))

            # Move from READY to BUSY
            del self._ready_states[self._ready_states.index(state_id)]
            self._busy_states.append(state_id)
            self._lock.notify_all()

        return self._load(state_id)

    @sync
    def _revive(self, state_id):
        ''' Send a BUSY state back to READY list 

            +--------+        +------+
            | READY  +<-------+ BUSY |
            +---+----+        +------+

        '''
        # Move from BUSY to READY
        self._busy_states.remove(state_id)
        self._ready_states.append(state_id)
        self._lock.notify_all()

    @sync
    def _terminate(self, state_id, delete=False):
        ''' Send a BUSY state to the TERMINATED list or trash it if delete is True 

            +------+        +------------+
            | BUSY +------->+ TERMINATED |
            +---+--+        +------------+
                |
                v
               ###
               ###

        '''
        # wait for a state id to be added to the ready list and remove it
        if state_id not in self._busy_states:
            raise Exception("Can not terminate. State is not being analyzed")
        del self._busy_states[self._busy_states.index(state_id)]

        if delete:
            self._remove(state_id)
        else:
            # add the state_id to the terminated list
            self._terminated_states.append(state_id)
        self._lock.notify_all()

    @property
    @sync
    def ready_states(self):
        """
        Iterator over ready states. 
        It supports state changes. State changes will be saved back at each iteration.

        The state data change must be done in a loop, e.g. `for state in ready_states: ...`
        as we re-save the state when the generator comes back to the function.

        This means it is not possible to change the state used by Manticore with `states = list(m.ready_states)`.
        """
        for state_id in self._ready_states:
            state = self._load(state_id)
            yield state
            # Re-save the state in case the user changed its data
            self._save(state)

    @property
    @sync
    def terminated_states(self):
        """
        Iterates over the terminated states.

        See also `ready_states`.
        """
        for state_id in self._terminated_states:
            state = self._load(state_id)
            yield state
            # Re-save the state in case the user changed its data
            self._save(state, state_id=state_id)

    @property
    @sync
    def cancelled_states(self):
        """
        Iterates over the cancelled states.

        See also `ready_states`.
        """
        for state_id in self._killed_states:
            state = self._load(state_id)
            yield state
            # Re-save the state in case the user changed its data
            self._save(state, state_id=state_id)

    @property
    @sync
    @at_not_running
    def _all_states(self):
        ''' Only allowed at not running. 
            (At running we can have states at busy)
        '''
        return tuple(self._ready_states) + tuple(self._terminated_states) + tuple(self._killed_states)

    @property
    @sync
    def all_states(self):
        """
        Iterates over the all states (ready and terminated and cancelled)
        It holds a lock so no changes state lists are allowed

        See also `ready_states`.
        """
        for state_id in self._all_states:
            state = self._load(state_id)
            yield state
            # Re-save the state in case the user changed its data
            self._save(state, state_id=state_id)

    @sync
    def count_states(self):
        """ Total states count """
        return len(self._all_states)

    @sync
    def count_ready_states(self):
        """ Ready states count """
        return len(self._ready_states)

    @sync
    def count_busy_states(self):
        """ Busy states count """
        return len(self._busy_states)

    @sync
    def count_killed_states(self):
        """ Cancelled states count """
        return len(self._killed_states)

    @sync
    def count_terminated_states(self):
        """ Terminated states count """
        return len(self._terminated_states)

    def generate_testcase(self, state, message='test'):
        testcase = self._output.testcase(prefix='test')
        # self._publish('will_generate_testcase', state, testcase, message)
        with testcase.open_stream('pkl', binary=True) as statef:
            PickleSerializer().serialize(state, statef)
        logger.info(f'Generated testcase No. %d - %s', testcase.num, message)
        return testcase

    @at_standby
    def register_plugin(self, plugin):
        # Global enumeration of valid events
        assert isinstance(plugin, Plugin)
        assert plugin not in self.plugins, "Plugin instance already registered"
        assert plugin.manticore is None, "Plugin instance already owned"

        plugin.manticore = self
        self.plugins.add(plugin)

        events = Eventful.all_events()
        prefix = Eventful.prefixes
        all_events = [x + y for x, y in itertools.product(prefix, events)]
        for event_name in all_events:
            callback_name = f'{event_name}_callback'
            callback = getattr(plugin, callback_name, None)
            if callback is not None:
                self.subscribe(event_name, callback)

        # Safety checks
        for callback_name in dir(plugin):
            if callback_name.endswith('_callback'):
                event_name = callback_name[:-9]
                if event_name not in all_events:
                    logger.warning("There is no event named %s for callback on plugin %s", event_name,
                                   type(plugin).__name__)

        for event_name in all_events:
            for plugin_method_name in dir(plugin):
                if event_name in plugin_method_name:
                    if not plugin_method_name.endswith('_callback'):
                        if plugin_method_name.startswith('on_') or \
                                plugin_method_name.startswith('will_') or \
                                plugin_method_name.startswith('did_'):
                            logger.warning("Plugin methods named '%s()' should end with '_callback' on plugin %s",
                                           plugin_method_name, type(plugin).__name__)
                    if plugin_method_name.endswith('_callback') and \
                            not plugin_method_name.startswith('on_') and \
                            not plugin_method_name.startswith('will_') and \
                            not plugin_method_name.startswith('did_'):
                        logger.warning(
                            "Plugin methods named '%s()' should start with 'on_', 'will_' or 'did_' on plugin %s",
                            plugin_method_name, type(plugin).__name__)

        plugin.on_register()

    @at_not_running
    def unregister_plugin(self, plugin):
        """ Removes a plugin from manticore.
            No events should be sent to it after
        """
        assert plugin in self.plugins, "Plugin instance not registered"
        plugin.on_unregister()
        self.plugins.remove(plugin)
        plugin.manticore = None

    def subscribe(self, name, callback):
        from types import MethodType
        if not isinstance(callback, MethodType):
            callback = MethodType(callback, self)
        super().subscribe(name, callback)

    @property
    @at_standby
    def context(self):
        ''' Convenient access to shared context. We maintain a local copy of the
            share context during the time manticore is not running. 
            This local context is copied to the shared context when a run starts
            and copied back when a run finishes
        '''
        return self._shared_context

    @contextmanager
    @sync
    def locked_context(self, key=None, value_type=list):
        """
        A context manager that provides safe parallel access to the global 
        Manticore context. This should be used to access the global Manticore 
        context when parallel analysis is activated. Code within the `with` block
        is executed atomically, so access of shared variables should occur within.

        Example use::

            with m.locked_context() as context:
                visited['visited'].append(state.cpu.PC)

        Optionally, parameters can specify a key and type for the object paired to this key.::

            with m.locked_context('feature_list', list) as feature_list:
                feature_list.append(1)

        Note: If standard (non-proxy) list or dict objects are contained in a 
        referent, modifications to those mutable values will not be propagated 
        through the manager because the proxy has no way of knowing when the 
        values contained within are modified. However, storing a value in a 
        container proxy (which triggers a __setitem__ on the proxy object) does
        propagate through the manager and so to effectively modify such an item,
        one could re-assign the modified value to the container proxy:

        :param object key: Storage key
        :param value_type: type of value associated with key
        :type value_type: list or dict or set
        """

        if key is None:
            # If no key is provided we yield the raw shared context under a lock
            ctx = self._shared_context
        else:
            # if a key is provided we yield the specific value or a fresh one
            value_type = self._context_value_types[value_type]
            context = self._shared_context
            if key in context:
                ctx = context[key]
            else:
                ctx = value_type()
                context[key] = ctx
        yield ctx


    def _produce_profiling_data(self):
        class PstatsFormatted:
            def __init__(self, d):
                self.stats = dict(d)

            def create_stats(self):
                pass

        with self.locked_context('profiling_stats') as profiling_stats:
            with self._output.save_stream('profiling.bin', binary=True) as s:
                ps = None
                for item in profiling_stats:
                    try:
                        stat = PstatsFormatted(item)
                        if ps is None:
                            ps = pstats.Stats(stat, stream=s)
                        else:
                            ps.add(stat)
                    except TypeError:
                        logger.info("Incorrectly formatted profiling information in _stats, skipping")

                if ps is None:
                    logger.info("Profiling failed")
                else:
                    # XXX(yan): pstats does not support dumping to a file stream, only to a file
                    # name. Below is essentially the implementation of pstats.dump_stats() without
                    # the extra open().
                    import marshal
                    marshal.dump(ps.stats, s)

    def get_profiling_stats(self):
        """
        Returns a pstat.Stats instance with profiling results if `run` was called with `should_profile=True`.
        Otherwise, returns `None`.
        """
        profile_file_path = os.path.join(self.workspace, 'profiling.bin')
        try:
            return pstats.Stats(profile_file_path)
        except Exception as e:
            logger.debug(f'Failed to get profiling stats: {e}')
            return None

    ############################################################################
    # Public API

    @sync
    def wait(self, condition):
        """ Waits for the condition callable to return True """
        self._lock.wait_for(condition)

    @sync
    def start(self):
        ''' This will send a start event to all registered workers.
            STANDBY -> RUNNING
        '''
        self._started.value = True
        self._lock.notify_all()

    @sync
    def stop(self):
        ''' This will send a stop event to all workers.
            Workers must go to STANDBY state.
            Manticore.run() will return
            RUNNING -> STANDBY
        '''
        self._started.value = False
        self._lock.notify_all()

    @sync
    def kill(self):
        """ Attempt to cancel and kill all the workers.
            Workers must terminate
            RUNNING, STANDBY -> KILLED
        """
        self._killed.value = True
        self._lock.notify_all()

    @sync
    def is_standby(self):
        ''' True if workers are standing by.'''
        return not self._started.value and not self._killed.value and not self._busy_states

    @sync
    def is_running(self):
        ''' True if workers are exploring BUSY states or waiting for READY states '''
        # If there are still states in the BUSY list then the STOP/KILL event 
        # was not yet answered
        # We know that BUSY states can only decrease after a stop is request
        return (self._started.value and not self._killed.value) or self._busy_states

    @sync
    def is_killed(self):
        ''' True if workers are killed. It is safe to join them '''
        # If there are still states in the BUSY list then the STOP/KILL event 
        # was not yet answered
        # We know that BUSY states can only decrease after a kill is requested
        return self._killed.value and not self._busy_states

    @property
    def workspace(self):
        return self._output.store.uri

    @contextmanager
    def kill_timeout(self, timeout=None):
        ''' A convenient context manager that will kill a manticore run after 
            timeout seconds
        '''
        if timeout is None:
            timeout = consts.timeout

        # Run forever is timeout is negative
        if timeout <= 0:
            yield
            return

        # THINKME kill grabs the lock. Is npt this a deadlock hazard?
        timer = Timer(timeout, self.kill)
        timer.start()

        try:
            yield
        finally:
            timer.cancel()

    @at_standby
    def run(self, timeout=None, should_profile=False):
        '''
        Runs analysis.
        :param timeout: Analysis timeout, in seconds
        '''

        # Lazy process start. At the first run() the workers are not forked.
        # This actually starts the worker procs/threads
        if self.subscribe:
            for w in self._workers:
                w.start()
            # User subscription to events is disabled from now on
            self.subscribe = None

        self._publish('will_run')

        with WithKeyboardInterruptAs(self.kill):

            with self.kill_timeout(timeout):
                assert not self._busy_states
                self.start()
                assert self._started.value
                with self._lock:
                    while self._started.value and not self._killed.value or self._busy_states:
                        self._lock.wait()
                    # It has been killed or stopped

        with self._lock:
            assert not self._busy_states
            assert not self._started.value or self._killed.value

            if self.is_killed():
                # move all READY to KILLED:
                while self._ready_states:
                    self._killed_states.append(self._ready_states.pop())

            self._publish('did_run')

    ############################################################################
    ############################################################################
    ############################################################################
    ############################################################################
    ############################################################################
    ############################################################################
    def _did_finish_run_callback(self):
        self._save_run_data()

    def _save_run_data(self):
        with self._output.save_stream('command.sh') as f:
            f.write(' '.join(map(shlex.quote, sys.argv)))

        with self._output.save_stream('manticore.yml') as f:
            config.save(f)
            time_ended = time.time()

        # time_elapsed = time_ended - self._last_run_stats['time_started']

        logger.info('Results in %s', self._output.store.uri)
        # logger.info('Total time: %s', time_elapsed)

        # self._last_run_stats['time_ended'] = time_ended
        # self._last_run_stats['time_elapsed'] = time_elapsed

    @staticmethod
    def verbosity(level):
        """Convenience interface for setting logging verbosity to one of
        several predefined logging presets. Valid values: 0-5.

        FIXME refator. This will affect all manticre instances.
        """
        log.set_verbosity(level)
        logger.info(f'Verbosity set to {level}.')


class ManticoreSingle(ManticoreBase):
    _worker_type = WorkerSingle

    def __init__(self, *args, **kwargs):
        class FakeLock():
            def _nothing(self, *args, **kwargs):
                pass

            acquire = _nothing
            release = _nothing
            __enter__ = _nothing
            __exit__ = _nothing
            notify_all = _nothing
            wait = _nothing

            def wait_for(self, condition, *args, **kwargs):
                if not condition():
                    raise Exception("Deadlock: Waiting for CTRL+C")

        self._lock = FakeLock()
        self._started = ctypes.c_bool(False)
        self._killed = ctypes.c_bool(False)

        self._ready_states = []
        self._terminated_states = []
        self._busy_states = []
        self._killed_states = []

        self._shared_context = {}
        self._context_value_types = {list: list,
                                     dict: dict,
                                     set: set,
                                     }
        super().__init__(*args, **kwargs)

    def start(self, wait=True):
        # Fake start action will run the single worker in place
        # The wait value is ignored as there is no async/councurrency here
        super().start()
        self._workers[0].run()


class ManticoreThreading(ManticoreBase):
    _worker_type = WorkerThread
    def __init__(self, *args, **kwargs):
        self._lock = threading.Condition()
        self._started = ctypes.c_bool(False)
        self._killed = ctypes.c_bool(False)

        self._ready_states = []
        self._terminated_states = []
        self._busy_states = []
        self._killed_states = []

        self._shared_context = {}
        self._context_value_types = {list: list,
                                     dict: dict,
                                     set: set,
                                     }
        super().__init__(*args, **kwargs)


class ManticoreMultiprocessing(ManticoreBase):
    _worker_type = WorkerProcess
    def __init__(self, *args, **kwargs):
        # This is the global manager that will handle all shared memory access
        # See. https://docs.python.org/3/library/multiprocessing.html#multiprocessing.managers.SyncManager
        self._manager = SyncManager()
        self._manager.start(
            lambda: signal.signal(signal.SIGINT, signal.SIG_IGN))
        # The main manticore lock. Acquire this for accessing shared objects
        # THINKME: we use the same lock to access states lists and shared contexts
        self._lock = self._manager.Condition()
        self._started = self._manager.Value(bool, False)
        self._killed = self._manager.Value(bool, False)

        # List of state ids of States on storage
        self._ready_states = self._manager.list()
        self._terminated_states = self._manager.list()
        self._busy_states = self._manager.list()
        self._killed_states = self._manager.list()
        self._shared_context = self._manager.dict()
        self._context_value_types = {list: self._manager.list,
                                     dict: self._manager.dict,
                                     set: self._manager.set,
                                     }
        super().__init__(*args, **kwargs)


    def start(self):
        super().start()

    ###########################################################################
    # Workers                                                                 #
    ###########################################################################
    def _fork_workers(self, procs=1, profiling=False):
        """ Spawns a new worker """
        if profiling:
            def profile_this(func):
                @functools.wraps(func)
                def wrapper(*args, **kwargs):
                    profile = cProfile.Profile()
                    profile.enable()
                    result = func(*args, **kwargs)
                    profile.disable()
                    profile.create_stats()
                    with self.locked_context('profiling_stats', list) as profiling_stats:
                        profiling_stats.append(profile.stats.items())
                    return result

                return wrapper

            target = profile_this(self._mainloop)
        else:
            target = self._mainloop

        workers = self._workers
        for _ in range(procs):
            worker = Process(target=target)
            worker.start()
            workers.append(worker)

    def _join_workers(self):
        """ Join all workers process """
        workers = self._workers
        while len(workers) > 0:
            workers.pop().join()

#ManticoreBase=ManticoreSingle
#ManticoreBase=ManticoreThreading
ManticoreBase=ManticoreMultiprocessing
