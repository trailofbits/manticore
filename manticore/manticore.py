from __future__ import absolute_import
import os
import sys
import time
import types
import functools
import cProfile
import pstats
import itertools
from multiprocessing import Process
from contextlib import contextmanager

from threading import Timer

# FIXME: remove this three
import elftools
from elftools.elf.elffile import ELFFile
from elftools.elf.sections import SymbolTableSection

from .core.executor import Executor
from .core.state import State, TerminateState
from .core.smtlib import solver, ConstraintSet
from .core.workspace import ManticoreOutput
from .platforms import linux, decree, evm
from .utils.helpers import issymbolic, is_binja_disassembler
from .utils.nointerrupt import WithKeyboardInterruptAs
from .utils.event import Eventful
from .core.plugin import Plugin, InstructionCounter, RecordSymbolicBranches, Visited, Tracer
import logging
from .utils import log

logger = logging.getLogger(__name__)
log.init_logging()


class ManticoreError(Exception):
    """
    Top level Exception object for custom exception hierarchy
    """
    pass


def make_binja(program, disasm, argv, env, symbolic_files, concrete_start=''):
    def _check_disassembler_present(disasm):
        if is_binja_disassembler(disasm):
            try:
                import binaryninja  # noqa
            except ImportError:
                err = ("BinaryNinja not found! You MUST own a BinaryNinja version"
                       " that supports GUI-less processing for this option"
                       " to work. Please configure your PYTHONPATH appropriately or"
                       " select a different disassembler")
                raise SystemExit(err)
    _check_disassembler_present(disasm)
    constraints = ConstraintSet()
    logger.info('Loading binary ninja IL from %s', program)
    platform = linux.SLinux(program,
                            argv=argv,
                            envp=env,
                            symbolic_files=symbolic_files,
                            disasm=disasm)
    initial_state = State(constraints, platform)
    return initial_state


def make_decree(program, concrete_start='', **kwargs):
    constraints = ConstraintSet()
    platform = decree.SDecree(constraints, program)
    initial_state = State(constraints, platform)
    logger.info('Loading program %s', program)

    if concrete_start != '':
        logger.info('Starting with concrete input: {}'.format(concrete_start))
    platform.input.transmit(concrete_start)
    platform.input.transmit(initial_state.symbolicate_buffer('+' * 14, label='RECEIVE'))
    return initial_state


def make_linux(program, argv=None, env=None, entry_symbol=None, symbolic_files=None, concrete_start=''):
    env = {} if env is None else env
    argv = [] if argv is None else argv
    env = ['%s=%s' % (k, v) for k, v in env.items()]

    logger.info('Loading program %s', program)

    constraints = ConstraintSet()
    platform = linux.SLinux(program, argv=argv, envp=env,
                            symbolic_files=symbolic_files)
    if entry_symbol is not None:
        entry_pc = platform._find_symbol(entry_symbol)
        if entry_pc is None:
            logger.error("No symbol for '%s' in %s", entry_symbol, program)
            raise Exception("Symbol not found")
        else:
            logger.info("Found symbol '%s' (%x)", entry_symbol, entry_pc)
            #TODO: use argv as arguments for function
            platform.set_entry(entry_pc)

    initial_state = State(constraints, platform)

    if concrete_start != '':
        logger.info('Starting with concrete input: %s', concrete_start)

    for i, arg in enumerate(argv):
        argv[i] = initial_state.symbolicate_buffer(arg, label='ARGV%d' % (i + 1))

    for i, evar in enumerate(env):
        env[i] = initial_state.symbolicate_buffer(evar, label='ENV%d' % (i + 1))

    # If any of the arguments or environment refer to symbolic values, re-
    # initialize the stack
    if any(issymbolic(x) for val in argv + env for x in val):
        platform.setup_stack([program] + argv, env)

    platform.input.write(concrete_start)

    # set stdin input...
    platform.input.write(initial_state.symbolicate_buffer('+' * 256,
                                                          label='STDIN'))
    return initial_state


def make_initial_state(binary_path, **kwargs):
    if 'disasm' in kwargs:
        if kwargs.get('disasm') == "binja-il":
            return make_binja(binary_path, **kwargs)
        else:
            del kwargs['disasm']
    magic = file(binary_path).read(4)
    if magic == '\x7fELF':
        # Linux
        state = make_linux(binary_path, **kwargs)
    elif magic == '\x7fCGC':
        # Decree
        state = make_decree(binary_path, **kwargs)
    elif magic == '#EVM':
        state = make_evm(binary_path, **kwargs)
    else:
        raise NotImplementedError("Binary {} not supported.".format(binary_path))
    return state


class Manticore(Eventful):
    '''
    The central analysis object.

    This should generally not be invoked directly; the various
    class method constructors should be preferred:
    :meth:`~manticore.Manticore.linux`,
    :meth:`~manticore.Manticore.decree`,
    :meth:`~manticore.Manticore.evm`.

    :param path_or_state: Path to a binary to analyze (**deprecated**) or `State` object
    :type path_or_state: str or State
    :param argv: Arguments to provide to binary (**deprecated**)
    :type argv: list[str]
    :ivar dict context: Global context for arbitrary data storage
    '''

    _published_events = {'start_run', 'finish_run'}

    def __init__(self, path_or_state, argv=None, workspace_url=None, policy='random', **kwargs):
        super(Manticore, self).__init__()

        if isinstance(workspace_url, str):
            if ':' not in workspace_url:
                ws_path = 'fs:' + workspace_url
            else:
                ws_path = workspace_url
        else:
            if workspace_url is not None:
                raise Exception('Invalid workspace')
            ws_path = None

        self._output = ManticoreOutput(ws_path)
        self._context = {}

        # sugar for 'will_execute_instruction"
        self._hooks = {}
        self._executor = Executor(store=self._output.store, policy=policy)
        self._workers = []

        # Link Executor events to default callbacks in manticore object
        self.forward_events_from(self._executor)

        if isinstance(path_or_state, str):
            if not os.path.isfile(path_or_state):
                raise Exception('{} is not an existing regular file'.format(path_or_state))
            self._initial_state = make_initial_state(path_or_state, argv=argv, **kwargs)
        elif isinstance(path_or_state, State):
            self._initial_state = path_or_state
        else:
            raise TypeError('path_or_state must be either a str or State, not {}'.format(type(path_or_state).__name__))

        if not isinstance(self._initial_state, State):
            raise TypeError("Manticore must be intialized with either a State or a path to a binary")

        self.plugins = set()

        # Move the folowing into a plugin
        self._assertions = {}
        self._coverage_file = None
        self.trace = None

        # FIXME move the folowing to aplugin
        self.subscribe('will_generate_testcase', self._generate_testcase_callback)
        self.subscribe('did_finish_run', self._did_finish_run_callback)

        # Default plugins for now.. FIXME REMOVE!
        self.register_plugin(InstructionCounter())
        self.register_plugin(Visited())
        self.register_plugin(Tracer())
        self.register_plugin(RecordSymbolicBranches())

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
            callback_name = '{}_callback'.format(event_name)
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

    def unregister_plugin(self, plugin):
        assert plugin in self.plugins, "Plugin instance not registered"
        self.plugins.remove(plugin)
        plugin.manticore = None

    @classmethod
    def linux(cls, path, argv=None, envp=None, entry_symbol=None, symbolic_files=None, concrete_start='', **kwargs):
        """
        Constructor for Linux binary analysis.

        :param str path: Path to binary to analyze
        :param argv: Arguments to provide to the binary
        :type argv: list[str]
        :param envp: Environment to provide to the binary
        :type envp: dict[str, str]
        :param entry_symbol: Entry symbol to resolve to start execution
        :type envp: str
        :param symbolic_files: Filenames to mark as having symbolic input
        :type symbolic_files: list[str]
        :param str concrete_start: Concrete stdin to use before symbolic inputt
        :param kwargs: Forwarded to the Manticore constructor
        :return: Manticore instance, initialized with a Linux State
        :rtype: Manticore
        """
        try:
            return cls(make_linux(path, argv, envp, entry_symbol, symbolic_files, concrete_start), **kwargs)
        except elftools.common.exceptions.ELFError:
            raise Exception('Invalid binary: {}'.format(path))

    @classmethod
    def decree(cls, path, concrete_start='', **kwargs):
        """
        Constructor for Decree binary analysis.

        :param str path: Path to binary to analyze
        :param str concrete_start: Concrete stdin to use before symbolic inputt
        :param kwargs: Forwarded to the Manticore constructor
        :return: Manticore instance, initialized with a Decree State
        :rtype: Manticore
        """
        try:
            return cls(make_decree(path, concrete_start), **kwargs)
        except KeyError:  # FIXME(mark) magic parsing for DECREE should raise better error
            raise Exception('Invalid binary: {}'.format(path))

    @classmethod
    def evm(cls, **kwargs):
        """
        Constructor for Ethereum virtual machine bytecode analysis.

        :param kwargs: Forwarded to the Manticore constructor
        :return: Manticore instance, initialized with a EVM State
        :rtype: Manticore
        """
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)
        return cls(State(constraints, world), **kwargs)

    @property
    def initial_state(self):
        return self._initial_state

    def subscribe(self, name, callback):
        from types import MethodType
        if not isinstance(callback, MethodType):
            callback = MethodType(callback, self)
        super(Manticore, self).subscribe(name, callback)

    @property
    def context(self):
        ''' Convenient access to shared context '''
        if not self.running:
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
            if not self.running:
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

    @staticmethod
    def verbosity(level):
        """Convenience interface for setting logging verbosity to one of
        several predefined logging presets. Valid values: 0-5.
        """
        log.set_verbosity(level)

    @property
    def running(self):
        return self._executor.running

    def enqueue(self, state):
        ''' Dynamically enqueue states. Users should typically not need to do this '''
        assert not self.running, "Can't add state where running. Can we?"
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
        if not (isinstance(pc, (int, long)) or pc is None):
            raise TypeError("pc must be either an int or None, not {}".format(pc.__class__.__name__))
        else:
            self._hooks.setdefault(pc, set()).add(callback)
            if self._hooks:
                self._executor.subscribe('will_execute_instruction', self._hook_callback)

    def _hook_callback(self, state, pc, instruction):
        'Invoke all registered generic hooks'

        # Ignore symbolic pc.
        # TODO(yan): Should we ask the solver if any of the hooks are possible,
        # and execute those that are?
        if not isinstance(pc, (int, long)):
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
        from . import platforms

        with open(path, 'r') as fnames:
            for line in fnames.readlines():
                address, cc_name, name = line.strip().split(' ')
                fmodel = platforms
                name_parts = name.split('.')
                importlib.import_module(".platforms.{}".format(name_parts[0]), 'manticore')
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

        from .core.parser.parser import parse

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

    ##########################################################################
    # Some are placeholders Remove FIXME
    # Any platform specific callback should go to a plugin

    def _generate_testcase_callback(self, state, name, message):
        '''
        Create a serialized description of a given state.
        :param state: The state to generate information about
        :param message: Accompanying message
        '''
        testcase_id = self._output.save_testcase(state, name, message)
        logger.info("Generated testcase No. {} - {}".format(testcase_id, message))

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

    def _start_run(self):
        assert not self.running
        self._publish('will_start_run', self._initial_state)

        if self._initial_state is not None:
            self.enqueue(self._initial_state)
            self._initial_state = None

        # Copy the local main context to the shared conext
        self._executor._shared_context.update(self._context)

    def _finish_run(self, profiling=False):
        assert not self.running
        # Copy back the shared context
        self._context = dict(self._executor._shared_context)

        if profiling:
            self._produce_profiling_data()

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
        if timeout > 0:
            t = Timer(timeout, self.terminate)
            t.start()
        try:
            self._start_workers(procs, profiling=should_profile)

            self._join_workers()
        finally:
            if timeout > 0:
                t.cancel()
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

    #############################################################################
    #############################################################################
    #############################################################################
    # Move all the following elsewhere Not all manticores have this
    def _get_symbol_address(self, symbol):
        '''
        Return the address of |symbol| within the binary
        '''

        # XXX(yan) This is a bit obtuse; once PE support is updated this should
        # be refactored out
        if self._binary_type == 'ELF':
            self._binary_obj = ELFFile(file(self._binary))

        if self._binary_obj is None:
            return NotImplementedError("Symbols aren't supported")

        for section in self._binary_obj.iter_sections():
            if not isinstance(section, SymbolTableSection):
                continue

            symbols = section.get_symbol_by_name(symbol)
            if not symbols:
                continue

            return symbols[0].entry['st_value']

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
        with self._output.save_stream('command.sh') as f:
            f.write(' '.join(sys.argv))

        elapsed = time.time() - self._time_started
        logger.info('Results in %s', self._output.store.uri)
        logger.info('Total time: %s', elapsed)
