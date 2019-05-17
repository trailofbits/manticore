import itertools
import logging
import sys
import time
import random
import weakref

from contextlib import contextmanager

import functools
import shlex

from ..core.plugin import Plugin
from ..core.smtlib import Expression
from ..core.state import StateBase
from ..core.workspace import ManticoreOutput
from ..utils import config
from ..utils.log import set_verbosity
from ..utils.event import Eventful
from ..utils.helpers import PickleSerializer
from ..utils.nointerrupt import WithKeyboardInterruptAs
from .workspace import Workspace
from .worker import WorkerSingle, WorkerThread, WorkerProcess

from multiprocessing.managers import SyncManager
import threading
import ctypes
import signal
from enum import Enum


class MProcessingType(Enum):
    """Used as configuration constant for choosing multiprocessing flavor"""

    multiprocessing = "multiprocessing"
    single = "single"
    threading = "threading"

    def title(self):
        return self._name_.title()

    @classmethod
    def from_string(cls, name):
        return cls.__members__[name]

    def to_class(self):
        return globals()[f"Manticore{self.title()}"]


logger = logging.getLogger(__name__)

consts = config.get_group("core")
consts.add("timeout", default=0, description="Timeout, in seconds, for Manticore invocation")
consts.add(
    "cluster",
    default=False,
    description="If True enables to run workers over the network UNIMPLEMENTED",
)
consts.add("procs", default=10, description="Number of parallel processes to spawn")
consts.add(
    "mprocessing",
    default=MProcessingType.multiprocessing,
    description="single: No multiprocessing at all. Single process.\n threading: use threads\m multiprocessing: use forked processes",
)


class ManticoreBase(Eventful):
    def __new__(cls, *args, **kwargs):
        if cls in (ManticoreBase, ManticoreSingle, ManticoreThreading, ManticoreMultiprocessing):
            raise Exception("Should not instantiate this")

        cl = consts.mprocessing.to_class()
        if cl not in cls.__bases__:
            # change ManticoreBase for the more specific class
            idx = cls.__bases__.index(ManticoreBase)
            bases = list(cls.__bases__)
            bases[idx] = cl
            cls.__bases__ = tuple(bases)

        return super().__new__(cls)

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
                raise Exception(f"{func.__name__} only allowed while NOT exploring states")
            return func(self, *args, **kw)

        return newFunction

    _published_events = {
        "run",
        "start_worker",
        "terminate_worker",
        "enqueue_state",
        "fork_state",
        "load_state",
        "terminate_state",
        "kill_state",
        "execute_instruction",
    }

    def __init__(self, initial_state, workspace_url=None, policy="random", **kwargs):
        """
        :param initial_state: State to start from.

               Manticore symbolically explores program states.


        Manticore phases
        ****************

        Manticore has multiprocessing capabilities. Several worker processes
        could be registered to do concurrent exploration of the READY states.
        Manticore can be itself at different phases: STANDBY, RUNNING.

                      +---------+               +---------+
                ----->| STANDBY +<------------->+ RUNNING |
                      +---------+               +----+----+

        = Phase STANDBY =
        Manticore starts at STANDBY with a single initial state. Here the user
        can inspect, modify and generate testcases for the different states. The
        workers are paused and not doing any work. Actions: run()


        = Phase RUNNING =
        At RUNNING the workers consume states from the READY state list and
        potentially fork new states or terminate states. A RUNNING manticore can
        be stopped back to STANDBY. Actions: stop()


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
                     |                             +--------+
                     +---------------------------->| KILLED |
                                                   +--------+

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
        READY so the user can apply a following transaction.```

        State list: KILLED
        ==================
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

        if any(
            not hasattr(self, x)
            for x in (
                "_worker_type",
                "_lock",
                "_running",
                "_killed",
                "_ready_states",
                "_terminated_states",
                "_killed_states",
                "_busy_states",
                "_shared_context",
            )
        ):
            raise Exception("Need to instantiate one of: ManticoreNative, ManticoreThreads..")

        # The workspace and the output
        # Manticore will use the workspace to save and share temporary states.
        # Manticore will use the output to save the final reports.
        # By default the output folder and the workspace folder are the same.
        # Check type, default to fs:
        if isinstance(workspace_url, str):
            if ":" not in workspace_url:
                workspace_url = f"fs:{workspace_url}"
        else:
            if workspace_url is not None:
                raise TypeError(f"Invalid workspace type: {type(workspace_url).__name__}")
        self._workspace = Workspace(workspace_url)
        # reuse the same workspace if not specified
        if workspace_url is None:
            workspace_url = f"fs:{self._workspace.uri}"
        self._output = ManticoreOutput(workspace_url)

        # The set of registered plugins
        # The callback methods defined in the plugin object will be called when
        # the different type of events occur over an exploration.
        # Note that each callback will run in a worker process and that some
        # careful use of the shared context is needed.
        self.plugins = set()

        # Set initial root state
        if not isinstance(initial_state, StateBase):
            raise TypeError(f"Invalid initial_state type: {type(initial_state).__name__}")
        self._put_state(initial_state)

        # Workers will use manticore __dict__ So lets spawn them last
        self._workers = [self._worker_type(id=i, manticore=self) for i in range(consts.procs)]
        self._is_main = True

    def __str__(self):
        return f"<{str(type(self))[8:-2]}| Alive States: {self.count_ready_states()}; Running States: {self.count_busy_states()} Terminated States: {self.count_terminated_states()} Killed States: {self.count_killed_states()} Started: {self._running.value} Killed: {self._killed.value}>"

    def _fork(self, state, expression, policy="ALL", setstate=None):
        """
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

        Parent state is removed from the busy list and tht child states are added
        to the ready list.

        """
        assert isinstance(expression, Expression)

        if setstate is None:

            def setstate(x, y):
                pass

        # Find a set of solutions for expression
        solutions = state.concretize(expression, policy)

        if not solutions:
            raise ManticoreError("Forking on unfeasible constraint set")

        logger.debug(
            "Forking. Policy: %s. Values: %s", policy, ", ".join(f"0x{sol:x}" for sol in solutions)
        )

        self._publish("will_fork_state", state, expression, solutions, policy)

        # Build and enqueue a state for each solution
        children = []
        for new_value in solutions:
            with state as new_state:
                new_state.constrain(expression == new_value)

                # and set the PC of the new state to the concrete pc-dest
                # (or other register or memory address to concrete)
                setstate(new_state, new_value)

                # enqueue new_state, assign new state id
                new_state_id = self._save(new_state, state_id=None)
                with self._lock:
                    self._ready_states.append(new_state_id)
                    self._lock.notify_all()  # Must notify one!

                self._publish("did_fork_state", new_state, expression, new_value, policy)
                # maintain a list of children for logging purpose
                children.append(new_state_id)

        with self._lock:
            self._busy_states.remove(state.id)
            self._remove(state.id)
            state._id = None
            self._lock.notify_all()

        logger.debug("Forking current state %r into states %r", state.id, children)

    @staticmethod
    def verbosity(level):
        """ Sets global vervosity level.
            This will activate different logging profiles globally depending
            on the provided numeric value
        """
        logger.info("Deprecated!")
        set_verbosity(level)

    # State storage
    def _save(self, state, state_id=None):
        """ Store or update a state in secondary storage under state_id.
            Use a fresh id is None is provided.

            :param state: A manticore State
            :param state_id: if not None force state_id (overwrite)
            :type state_id: int or None
            :returns: the state id used
        """
        state._id = self._workspace.save_state(state, state_id=state_id)
        return state.id

    def _load(self, state_id):
        """ Load the state from the secondary storage

            :param state_id: a estate id
            :type state_id: int
            :returns: the state id used
        """

        if not hasattr(self, "stcache"):
            self.stcache = weakref.WeakValueDictionary()
        if state_id in self.stcache:
            return self.stcache[state_id]
        self._publish("will_load_state", state_id)
        state = self._workspace.load_state(state_id, delete=False)
        state._id = state_id
        self.forward_events_from(state, True)
        self._publish("did_load_state", state, state_id)
        self.stcache[state_id] = state
        return state

    def _remove(self, state_id):
        """ Remove a state from secondary storage

            :param state_id: a estate id
            :type state_id: int
        """
        if not hasattr(self, "stcache"):
            self.stcache = weakref.WeakValueDictionary()
        if state_id in self.stcache:
            del self.stcache[state_id]

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
        state_id = self._save(state, state_id=state.id)
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
                while not self._ready_states and not self._killed.value:
                    # if a shutdown has been requested then bail
                    if self.is_killed():
                        return None  # Cancelled operation
                    # If there are no more READY states and no more BUSY states
                    # there is no chance we will get any new state so raise
                    if not self._busy_states:
                        return None  # There are not states

                    # if there ares actually some workers ready, wait for state forks
                    logger.debug("Waiting for available states")
                    self._lock.wait()

            if self._killed.value:
                return None

            # at this point we know there is at least one element
            # and we have exclusive access
            assert self._ready_states

            # make the choice under exclusive access to the shared ready list
            # state_id = self._policy.choice(list(self._ready_states)[0])
            state_id = random.choice(list(self._ready_states))

            # Move from READY to BUSY
            self._ready_states.remove(state_id)
            self._busy_states.append(state_id)
            self._lock.notify_all()

        return self._load(state_id)

    @sync
    def _revive_state(self, state_id):
        """ Send a BUSY state back to READY list

            +--------+        +------+
            | READY  +<-------+ BUSY |
            +---+----+        +------+

        """
        # Move from BUSY to READY
        self._busy_states.remove(state_id)
        self._ready_states.append(state_id)
        self._lock.notify_all()

    @sync
    def _terminate_state(self, state_id, delete=False):
        """ Send a BUSY state to the TERMINATED list or trash it if delete is True

            +------+        +------------+
            | BUSY +------->+ TERMINATED |
            +---+--+        +------------+
                |
                v
               ###
               ###

        """
        # wait for a state id to be added to the ready list and remove it
        if state_id not in self._busy_states:
            raise Exception("Can not terminate. State is not being analyzed")
        self._busy_states.remove(state_id)

        if delete:
            self._remove(state_id)
        else:
            # add the state_id to the terminated list
            self._terminated_states.append(state_id)

        # wake up everyone waiting for a change in the state lists
        self._lock.notify_all()

    @sync
    def _kill_state(self, state_id, delete=False):
        """ Send a BUSY state to the KILLED list or trash it if delete is True

            +------+        +--------+
            | BUSY +------->+ KILLED |
            +---+--+        +--------+
                |
                v
               ###
               ###

        """
        # wait for a state id to be added to the ready list and remove it
        if state_id not in self._busy_states:
            raise Exception("Can not even kill it. State is not being analyzed")
        self._busy_states.remove(state_id)

        if delete:
            self._remove(state_id)
        else:
            # add the state_id to the terminated list
            self._killed_states.append(state_id)

        # wake up everyone waiting for a change in the state lists
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
            self._save(state, state_id=state_id)

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
    @at_not_running
    def killed_states(self):
        """
        Iterates over the cancelled/killed states.

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
        """ Only allowed at not running.
            (At running we can have states at busy)
        """
        return (
            tuple(self._ready_states) + tuple(self._terminated_states) + tuple(self._killed_states)
        )

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

    def generate_testcase(self, state, message="test", name="test"):
        testcase = self._output.testcase(prefix=name)
        with testcase.open_stream("pkl", binary=True) as statef:
            PickleSerializer().serialize(state, statef)

        # Let the plugins generate a state based report
        for p in self.plugins:
            p.generate_testcase(state, testcase, message)

        logger.info("Generated testcase No. %d - %s", testcase.num, message)
        return testcase

    @at_not_running
    def register_plugin(self, plugin):
        # Global enumeration of valid events
        assert isinstance(plugin, Plugin)
        assert plugin not in self.plugins, "Plugin instance already registered"
        assert getattr(plugin, "manticore", None) is None, "Plugin instance already owned"

        plugin.manticore = self
        self.plugins.add(plugin)

        events = Eventful.all_events()
        prefix = Eventful.prefixes
        all_events = [x + y for x, y in itertools.product(prefix, events)]
        for event_name in all_events:
            callback_name = f"{event_name}_callback"
            callback = getattr(plugin, callback_name, None)
            if callback is not None:
                self.subscribe(event_name, callback)

        # Safety checks
        for callback_name in dir(plugin):
            if callback_name.endswith("_callback"):
                event_name = callback_name[:-9]
                if event_name not in all_events:
                    logger.warning(
                        "There is no event named %s for callback on plugin %s",
                        event_name,
                        type(plugin).__name__,
                    )

        for event_name in all_events:
            for plugin_method_name in dir(plugin):
                if event_name in plugin_method_name:
                    if not plugin_method_name.endswith("_callback"):
                        if (
                            plugin_method_name.startswith("on_")
                            or plugin_method_name.startswith("will_")
                            or plugin_method_name.startswith("did_")
                        ):
                            logger.warning(
                                "Plugin methods named '%s()' should end with '_callback' on plugin %s",
                                plugin_method_name,
                                type(plugin).__name__,
                            )
                    if (
                        plugin_method_name.endswith("_callback")
                        and not plugin_method_name.startswith("on_")
                        and not plugin_method_name.startswith("will_")
                        and not plugin_method_name.startswith("did_")
                    ):
                        logger.warning(
                            "Plugin methods named '%s()' should start with 'on_', 'will_' or 'did_' on plugin %s",
                            plugin_method_name,
                            type(plugin).__name__,
                        )

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
        """ Register a callback to an event"""
        from types import MethodType

        if not isinstance(callback, MethodType):
            callback = MethodType(callback, self)
        super().subscribe(name, callback)

    @property
    @at_not_running
    def context(self):
        """ Convenient access to shared context. We maintain a local copy of the
            share context during the time manticore is not running.
            This local context is copied to the shared context when a run starts
            and copied back when a run finishes
        """
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
            yield self._shared_context
        else:
            # if a key is provided we yield the specific value or a fresh one
            if value_type not in (list, dict):
                raise TypeError("Type must be list or dict")
            if hasattr(self, "_context_value_types"):
                value_type = self._context_value_types[value_type]
            context = self._shared_context
            if key not in context:
                context[key] = value_type()
            yield context[key]

    ############################################################################
    # Public API

    @sync
    def wait(self, condition):
        """ Waits for the condition callable to return True """
        self._lock.wait_for(condition)

    @sync
    def kill(self):
        """ Attempt to cancel and kill all the workers.
            Workers must terminate
            RUNNING, STANDBY -> KILLED
        """
        self._killed.value = True
        self._lock.notify_all()

    @sync
    def is_running(self):
        """ True if workers are exploring BUSY states or waiting for READY states """
        # If there are still states in the BUSY list then the STOP/KILL event
        # was not yet answered
        # We know that BUSY states can only decrease after a stop is requested
        return self._running.value

    @sync
    def is_killed(self):
        """ True if workers are killed. It is safe to join them """
        # If there are still states in the BUSY list then the STOP/KILL event
        # was not yet answered
        # We know that BUSY states can only decrease after a kill is requested
        return self._killed.value

    @property
    def workspace(self):
        return self._output.store.uri

    @contextmanager
    def kill_timeout(self, timeout=None):
        """ A convenient context manager that will kill a manticore run after
            timeout seconds
        """
        if timeout is None:
            timeout = consts.timeout

        # Run forever is timeout is negative
        if timeout <= 0:
            try:
                yield
            finally:
                return

        # THINKME kill grabs the lock. Is npt this a deadlock hazard?
        timer = threading.Timer(timeout, self.kill)
        timer.start()

        try:
            yield
        finally:
            timer.cancel()

    @at_not_running
    def run(self, timeout=None):
        """
        Runs analysis.
        :param timeout: Analysis timeout, in seconds
        """
        # Delete state cache
        # The cached version of a state may get out of sync if a worker in a
        # different process modifies the state
        self.stcache = weakref.WeakValueDictionary()

        # Lazy process start. At the first run() the workers are not forked.
        # This actually starts the worker procs/threads
        if self.subscribe:
            # User subscription to events is disabled from now on
            self.subscribe = None

        self._publish("will_run", self.ready_states)
        self._running.value = True
        # start all the workers!
        for w in self._workers:
            w.start()

        # Main process. Lets just wait and capture CTRL+C at main
        with WithKeyboardInterruptAs(self.kill):
            with self._lock:
                while (self._busy_states or self._ready_states) and not self._killed.value:
                    self._lock.wait()

        # Join all the workers!
        for w in self._workers:
            w.join()

        with self._lock:
            assert not self._busy_states and not self._ready_states or self._killed.value

            if self.is_killed():
                logger.debug("Killed. Moving all remaining ready states to killed list")
                # move all READY to KILLED:
                while self._ready_states:
                    self._killed_states.append(self._ready_states.pop())

        self._running.value = False
        self._publish("did_run")
        assert not self.is_running()

    @sync
    @at_not_running
    def remove_all(self):
        """
            Deletes all streams from storage and clean state lists
        """
        for state_id in self._all_states:
            self._remove(state_id)

        del self._ready_states[:]
        del self._busy_states[:]
        del self._terminated_states[:]
        del self._killed_states[:]

    def finalize(self):
        """
        Generate a report testcase for every state in the system and remove
        all temporary files/streams from the workspace
        """
        self.kill()
        for state in self.all_states:
            self.generate_testcase(state)
        self.remove_all()

    ############################################################################
    ############################################################################
    ############################################################################
    ############################################################################
    ############################################################################
    ############################################################################

    def save_run_data(self):
        with self._output.save_stream("command.sh") as f:
            f.write(" ".join(map(shlex.quote, sys.argv)))

        with self._output.save_stream("manticore.yml") as f:
            config.save(f)

        logger.info("Results in %s", self._output.store.uri)


class ManticoreSingle(ManticoreBase):
    _worker_type = WorkerSingle

    def __init__(self, *args, **kwargs):
        class FakeLock:
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
        self._killed = ctypes.c_bool(False)
        self._running = ctypes.c_bool(False)

        self._ready_states = []
        self._terminated_states = []
        self._busy_states = []
        self._killed_states = []

        self._shared_context = {}
        super().__init__(*args, **kwargs)


class ManticoreThreading(ManticoreBase):
    _worker_type = WorkerThread

    def __init__(self, *args, **kwargs):
        self._lock = threading.Condition()
        self._killed = ctypes.c_bool(False)
        self._running = ctypes.c_bool(False)

        self._ready_states = []
        self._terminated_states = []
        self._busy_states = []
        self._killed_states = []

        self._shared_context = {}

        super().__init__(*args, **kwargs)


class ManticoreMultiprocessing(ManticoreBase):
    _worker_type = WorkerProcess

    def __init__(self, *args, **kwargs):
        # This is the global manager that will handle all shared memory access
        # See. https://docs.python.org/3/library/multiprocessing.html#multiprocessing.managers.SyncManager
        self._manager = SyncManager()
        self._manager.start(lambda: signal.signal(signal.SIGINT, signal.SIG_IGN))
        # The main manticore lock. Acquire this for accessing shared objects
        # THINKME: we use the same lock to access states lists and shared contexts
        self._lock = self._manager.Condition()
        self._killed = self._manager.Value(bool, False)
        self._running = self._manager.Value(bool, False)

        # List of state ids of States on storage
        self._ready_states = self._manager.list()
        self._terminated_states = self._manager.list()
        self._busy_states = self._manager.list()
        self._killed_states = self._manager.list()
        self._shared_context = self._manager.dict()
        self._context_value_types = {list: self._manager.list, dict: self._manager.dict}

        super().__init__(*args, **kwargs)
