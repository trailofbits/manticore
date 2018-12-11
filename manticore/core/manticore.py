import cProfile
import itertools
import logging
import os
import pstats
import sys
import time
from contextlib import contextmanager
from multiprocessing import Process
from threading import Timer

import functools
import shlex
import types

from ..core.executor import Executor
from ..core.plugin import Plugin
from ..core.smtlib import solver
from ..core.state import TerminateState, StateBase
from ..core.workspace import ManticoreOutput
from ..utils import config
from ..utils import log
from ..utils.event import Eventful
from ..utils.helpers import issymbolic
from ..utils.nointerrupt import WithKeyboardInterruptAs

logger = logging.getLogger(__name__)
log.init_logging()


class ManticoreBase(Eventful):
    '''
    Base class for the central analysis object.

    :param path_or_state: Path to a binary to analyze (**deprecated**) or `State` object
    :type path_or_state: str or State
    :param argv: Arguments to provide to binary (**deprecated**)
    :type argv: list[str]
    :ivar dict context: Global context for arbitrary data storage
    '''

    _published_events = {'start_run', 'finish_run'}

    def __init__(self, initial_state, workspace_url=None, policy='random', **kwargs):
        """

        :param initial_state: State to start from.
        :param workspace_url: workspace folder name
        :param policy: scheduling policy
        :param kwargs: other kwargs, e.g.
        """
        super().__init__()

        if isinstance(workspace_url, str):
            if ':' not in workspace_url:
                ws_path = f'fs:{workspace_url}'
            else:
                ws_path = workspace_url
        else:
            if workspace_url is not None:
                raise TypeError(f'Invalid workspace type: {type(workspace_url).__name__}')
            ws_path = None

        self._output = ManticoreOutput(ws_path)
        self._context = {}

        # sugar for 'will_execute_instruction"
        self._hooks = {}
        self._executor = Executor(store=self._output.store, policy=policy)
        self._workers = []

        self.plugins = set()

        # Link Executor events to default callbacks in manticore object
        self.forward_events_from(self._executor)

        if not isinstance(initial_state, StateBase):
            raise TypeError(f'Invalid initial_state type: {type(initial_state).__name__}')

        self._initial_state = initial_state
        self._executor.forward_events_from(self._initial_state, True)

        # Move the following into a linux plugin

        self._assertions = {}
        self._coverage_file = None
        self.trace = None

        # FIXME move the following to a plugin
        self.subscribe('will_generate_testcase', self._generate_testcase_callback)
        self.subscribe('did_finish_run', self._did_finish_run_callback)

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
                    logger.warning("There is no event named %s for callback on plugin %s", event_name, type(plugin).__name__)

        for event_name in all_events:
            for plugin_method_name in dir(plugin):
                if event_name in plugin_method_name:
                    if not plugin_method_name.endswith('_callback'):
                        if plugin_method_name.startswith('on_') or \
                           plugin_method_name.startswith('will_') or \
                           plugin_method_name.startswith('did_'):
                            logger.warning("Plugin methods named '%s()' should end with '_callback' on plugin %s", plugin_method_name, type(plugin).__name__)
                    if plugin_method_name.endswith('_callback') and \
                            not plugin_method_name.startswith('on_') and \
                            not plugin_method_name.startswith('will_') and \
                            not plugin_method_name.startswith('did_'):
                        logger.warning("Plugin methods named '%s()' should start with 'on_', 'will_' or 'did_' on plugin %s",
                                       plugin_method_name, type(plugin).__name__)

        plugin.on_register()

    def unregister_plugin(self, plugin):
        assert plugin in self.plugins, "Plugin instance not registered"
        plugin.on_unregister()
        self.plugins.remove(plugin)
        plugin.manticore = None

    def __del__(self):
        # If an exception is thrown in a child/inherited class's __init__ before calling super().__init__
        # the self.plugins is not assigned
        # because of that, we need to use a `getattr` here, otherwise we might get two exceptions
        # (and the one from here is irrelevant and confusing)
        plugins = getattr(self, 'plugins', [])

        # A `list` cast is needed, otherwise we delete items from the `self.plugins` set while iterating over it
        for plugin in list(plugins):
            self.unregister_plugin(plugin)

    @property
    def initial_state(self):
        return self._initial_state

    def subscribe(self, name, callback):
        from types import MethodType
        if not isinstance(callback, MethodType):
            callback = MethodType(callback, self)
        super().subscribe(name, callback)

    @property
    def context(self):
        ''' Convenient access to shared context '''
        if self._context is not None:
            return self._context
        else:
            logger.warning("Using shared context without a lock")
            return self._executor._shared_context

    @contextmanager
    def locked_context(self, key=None, value_type=list):
        """
        A context manager that provides safe parallel access to the global Manticore context.
        This should be used to access the global Manticore context
        when parallel analysis is activated. Code within the `with` block is executed
        atomically, so access of shared variables should occur within.

        Example use::

            with m.locked_context() as context:
                visited = context['visited']
                visited.append(state.cpu.PC)
                context['visited'] = visited

        Optionally, parameters can specify a key and type for the object paired to this key.::

            with m.locked_context('feature_list', list) as feature_list:
                feature_list.append(1)

        :param object key: Storage key
        :param value_type: type of value associated with key
        :type value_type: list or dict or set
        """

        @contextmanager
        def _real_context():
            if self._context is not None:
                yield self._context
            else:
                with self._executor.locked_context() as context:
                    yield context

        with _real_context() as context:
            if key is None:
                yield context
            else:
                assert value_type in (list, dict, set)
                ctx = context.get(key, value_type())
                yield ctx
                context[key] = ctx

    @contextmanager
    def shutdown_timeout(self, timeout):
        if timeout <= 0:
            yield
            return

        timer = Timer(timeout, self.shutdown)
        timer.start()

        try:
            yield
        finally:
            timer.cancel()

    @staticmethod
    def verbosity(level):
        """Convenience interface for setting logging verbosity to one of
        several predefined logging presets. Valid values: 0-5.
        """
        log.set_verbosity(level)
        logger.info(f'Verbosity set to {level}.')

    @property
    def running(self):
        return self._executor.running

    def enqueue(self, state):
        ''' Dynamically enqueue states. Users should typically not need to do this '''
        assert not self.running, "Can't add state when running, can we?"
        self._executor.enqueue(state)

    ###########################################################################
    # Workers                                                                 #
    ###########################################################################
    def _start_workers(self, num_processes, profiling=False):
        assert num_processes > 0, "Must have more than 0 worker processes"

        logger.debug("Starting %d processes.", num_processes)

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

            target = profile_this(self._executor.run)
        else:
            target = self._executor.run

        if num_processes == 1:
            target()
        else:
            for _ in range(num_processes):
                p = Process(target=target, args=())
                self._workers.append(p)
                p.start()

    def _join_workers(self):
        with WithKeyboardInterruptAs(self._executor.shutdown):
            while len(self._workers) > 0:
                self._workers.pop().join()

    ############################################################################
    # Common hooks + callback
    ############################################################################

    def init(self, f):
        '''
        A decorator used to register a hook function to run before analysis begins. Hook
        function takes one :class:`~manticore.core.state.State` argument.
        '''
        def callback(manticore_obj, state):
            f(state)
        self.subscribe('will_start_run', types.MethodType(callback, self))
        return f

    def hook(self, pc):
        '''
        A decorator used to register a hook function for a given instruction address.
        Equivalent to calling :func:`~add_hook`.

        :param pc: Address of instruction to hook
        :type pc: int or None
        '''
        def decorator(f):
            self.add_hook(pc, f)
            return f
        return decorator

    def add_hook(self, pc, callback):
        '''
        Add a callback to be invoked on executing a program counter. Pass `None`
        for pc to invoke callback on every instruction. `callback` should be a callable
        that takes one :class:`~manticore.core.state.State` argument.

        :param pc: Address of instruction to hook
        :type pc: int or None
        :param callable callback: Hook function
        '''
        if not (isinstance(pc, int) or pc is None):
            raise TypeError(f"pc must be either an int or None, not {pc.__class__.__name__}")
        else:
            self._hooks.setdefault(pc, set()).add(callback)
            if self._hooks:
                self._executor.subscribe('will_execute_instruction', self._hook_callback)

    def _hook_callback(self, state, pc, instruction):
        'Invoke all registered generic hooks'

        # Ignore symbolic pc.
        # TODO(yan): Should we ask the solver if any of the hooks are possible,
        # and execute those that are?

        if issymbolic(pc):
            return

        # Invoke all pc-specific hooks
        for cb in self._hooks.get(pc, []):
            cb(state)

        # Invoke all pc-agnostic hooks
        for cb in self._hooks.get(None, []):
            cb(state)

    ############################################################################
    # Model hooks + callback
    ############################################################################

    def apply_model_hooks(self, path):
        # TODO(yan): Simplify the partial function application

        # Imported straight from __main__.py; this will be re-written once the new
        # event code is in place.
        import importlib
        from manticore import platforms

        with open(path, 'r') as fnames:
            for line in fnames.readlines():
                address, cc_name, name = line.strip().split(' ')
                fmodel = platforms
                name_parts = name.split('.')
                importlib.import_module(f".platforms.{name_parts[0]}", 'manticore')
                for n in name_parts:
                    fmodel = getattr(fmodel, n)
                assert fmodel != platforms

                def cb_function(state):
                    state.platform.invoke_model(fmodel, prefix_args=(state.platform,))
                self._model_hooks.setdefault(int(address, 0), set()).add(cb_function)
                self._executor.subscribe('will_execute_instruction', self._model_hook_callback)

    def _model_hook_callback(self, state, instruction):
        pc = state.cpu.PC
        if pc not in self._model_hooks:
            return

        for cb in self._model_hooks[pc]:
            cb(state)

    ############################################################################
    # Assertion hooks + callback
    ############################################################################

    def load_assertions(self, path):
        with open(path, 'r') as f:
            for line in f.readlines():
                pc = int(line.split(' ')[0], 16)
                if pc in self._assertions:
                    logger.debug("Repeated PC in assertions file %s", path)
                self._assertions[pc] = ' '.join(line.split(' ')[1:])
                self.subscribe('will_execute_instruction', self._assertions_callback)

    def _assertions_callback(self, state, pc, instruction):
        if pc not in self._assertions:
            return

        from .parser.parser import parse

        program = self._assertions[pc]

        # This will interpret the buffer specification written in INTEL ASM.
        # (It may dereference pointers)
        assertion = parse(program, state.cpu.read_int, state.cpu.read_register)
        if not solver.can_be_true(state.constraints, assertion):
            logger.info(str(state.cpu))
            logger.info("Assertion %x -> {%s} does not hold. Aborting state.",
                        state.cpu.pc, program)
            raise TerminateState()

        # Everything is good add it.
        state.constraints.add(assertion)

    ############################################################################
    # Some are placeholders Remove FIXME
    # Any platform specific callback should go to a plugin

    def _generate_testcase_callback(self, state, name, message):
        '''
        Create a serialized description of a given state.
        :param state: The state to generate information about
        :param message: Accompanying message
        '''
        testcase_id = self._output.save_testcase(state, name, message)
        logger.info(f"Generated testcase No. {testcase_id} - {message}")

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

    def _start_run(self):
        assert not self.running and self._context is not None
        self._publish('will_start_run', self._initial_state)

        if self._initial_state is not None:
            self.enqueue(self._initial_state)
            self._initial_state = None

        # Copy the local main context to the shared context
        self._executor._shared_context.update(self._context)
        self._context = None

    def _finish_run(self, profiling=False):
        assert not self.running
        if profiling:
            self._produce_profiling_data()

        # Copy back the shared context
        self._context = dict(self._executor._shared_context)

        self._publish('did_finish_run')

    def run(self, procs=1, timeout=0, should_profile=False):
        '''
        Runs analysis.

        :param int procs: Number of parallel worker processes
        :param timeout: Analysis timeout, in seconds
        '''
        assert not self.running, "Manticore is already running."
        self._start_run()

        self._time_started = time.time()
        with self.shutdown_timeout(timeout):
            self._start_workers(procs, profiling=should_profile)

            self._join_workers()
        self._finish_run(profiling=should_profile)

    #Fixme remove. terminate is used to TerminateState. May be confusing
    def terminate(self):
        '''
        Gracefully terminate the currently-executing run. Typically called from within
        a :func:`~hook`.
        '''
        self._executor.shutdown()

    def shutdown(self):
        '''
        Gracefully terminate the currently-executing run. Typically called from within
        a :func:`~hook`.
        '''
        self._executor.shutdown()

    def is_shutdown(self):
        ''' Returns True if shutdown was requested '''
        return self._executor.is_shutdown()

    @property
    def coverage_file(self):
        return self._coverage_file

    @property
    def workspace(self):
        return self._output.store.uri

    @coverage_file.setter
    def coverage_file(self, path):
        assert not self.running, "Can't set coverage file if Manticore is running."
        self._coverage_file = path

    def _did_finish_run_callback(self):
        self._save_run_data()

    def _save_run_data(self):
        with self._output.save_stream('command.sh') as f:
            f.write(' '.join(map(shlex.quote, sys.argv)))

        with self._output.save_stream('manticore.yml') as f:
            config.save(f)

        elapsed = time.time() - self._time_started
        logger.info('Results in %s', self._output.store.uri)
        logger.info('Total time: %s', elapsed)
