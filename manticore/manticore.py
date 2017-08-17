import os
import sys
import time
import types
import logging
import binascii
import functools
import cProfile
import pstats

from multiprocessing import Process
from contextlib import contextmanager

from threading import Timer

from elftools.elf.elffile import ELFFile
from elftools.elf.sections import SymbolTableSection

from .core.executor import Executor
from .core.parser import parse
from .core.state import State, TerminateState
from .core.smtlib import solver, ConstraintSet
from .core.workspace import ManticoreOutput
from .platforms import linux, decree, windows
from .utils.helpers import issymbolic, is_binja_disassembler
from .utils.nointerrupt import WithKeyboardInterruptAs
from .utils import log

logger = logging.getLogger('MANTICORE')

def makeBinja(program, disasm, argv, env, symbolic_files, concrete_start=''):
    constraints = ConstraintSet()
    logger.info('Loading binary ninja IL from %s', program)
    platform = linux.SLinux(program,
                            argv=argv,
                            envp=env,
                            symbolic_files=symbolic_files,
                            disasm=disasm)
    initial_state = State(constraints, platform)
    return initial_state

def makeDecree(program, concrete_data=''):
    constraints = ConstraintSet()
    platform = decree.SDecree(constraints, program)
    initial_state = State(constraints, platform)
    logger.info('Loading program %s', program)

    if concrete_data != '':
        logger.info('Starting with concrete input: {}'.format(concrete_data))
    platform.input.transmit(concrete_data)
    platform.input.transmit(initial_state.symbolicate_buffer('+'*14, label='RECEIVE'))
    return initial_state

def makeLinux(program, disasm, argv, env, symbolic_files, concrete_start=''):
    logger.info('Loading program %s (platform: Linux)', program)

    constraints = ConstraintSet()

    platform = linux.SLinux(program,
                            argv=argv,
                            envp=env,
                            symbolic_files=symbolic_files,
                            disasm=disasm)
    initial_state = State(constraints, platform)

    if concrete_start != '':
        logger.info('Starting with concrete input: %s', concrete_start)

    for i, arg in enumerate(argv):
        argv[i] = initial_state.symbolicate_buffer(arg, label='ARGV%d' % (i+1))

    for i, evar in enumerate(env):
        env[i] = initial_state.symbolicate_buffer(evar, label='ENV%d' % (i+1))

    # If any of the arguments or environment refer to symbolic values, re-
    # initialize the stack
    if any(issymbolic(x) for val in argv + env for x in val):
        platform.setup_stack([program] + argv, env)

    platform.input.write(concrete_start)

    #set stdin input...
    platform.input.write(initial_state.symbolicate_buffer('+' * 256,
                                                          label='STDIN'))

    return initial_state


def makeWindows(args):
    assert args.size is not None, "Need to specify buffer size"
    assert args.buffer is not None, "Need to specify buffer base address"
    logger.debug('Loading program %s (platform: Windows)', args.programs)
    additional_context = None
    if args.context:
        with open(args.context, "r") as addl_context_file:
            additional_context = cPickle.loads(addl_context_file.read())
            logger.debug('Additional context loaded with contents {}'.format(additional_context)) #DEBUG

    constraints = ConstraintSet()
    platform = windows.SWindows(constraints, args.programs[0], additional_context, snapshot_folder=args.workspace)

    #This will interpret the buffer specification written in INTEL ASM. (It may dereference pointers)
    data_size = parse(args.size, platform.current.read_bytes, platform.current.read_register)
    data_ptr  = parse(args.buffer, platform.current.read_bytes, platform.current.read_register)

    logger.debug('Buffer at %x size %d bytes)', data_ptr, data_size)
    buf_str = "".join(platform.current.read_bytes(data_ptr, data_size))
    logger.debug('Original buffer: %s', buf_str.encode('hex'))

    offset = args.offset
    concrete_data = args.data.decode('hex')
    assert data_size >= offset + len(concrete_data)
    size = min(args.maxsymb, data_size - offset - len(concrete_data))
    symb = constraints.new_array(name='RAWMSG', index_max=size)

    platform.current.write_bytes(data_ptr + offset, concrete_data)
    platform.current.write_bytes(data_ptr + offset + len(concrete_data), [symb[i] for i in xrange(size)] )

    logger.debug('First %d bytes are left concrete', offset)
    logger.debug('followed by %d bytes of concrete start', len(concrete_data))
    hex_head = "".join(platform.current.read_bytes(data_ptr, offset+len(concrete_data)))
    logger.debug('Hexdump head: %s', hex_head.encode('hex'))
    logger.debug('Total symbolic characters inserted: %d', size)
    logger.debug('followed by %d bytes of unmodified concrete bytes at end.', (data_size-offset-len(concrete_data))-size )
    hex_tail = "".join(map(chr, platform.current.read_bytes(data_ptr+offset+len(concrete_data)+size, data_size-(offset+len(concrete_data)+size))))
    logger.debug('Hexdump tail: %s', hex_tail.encode('hex'))
    logger.info("Starting PC is: {:08x}".format(platform.current.PC))

    return State(constraints, platform)

def binary_type(path):
    '''
    Given a path to a binary, return a string representation of its type.
      i.e. ELF, PE, DECREE, QNX
    '''
    magic = None
    with open(path) as f:
        magic = f.read(4)

    if magic == '\x7fELF':
        return 'ELF'
    elif magic == 'MDMP':
        return 'PE'
    elif magic == '\x7fCGC':
        return 'DECREE'
    else:
        raise NotImplementedError("Binary {} not supported. Magic bytes: 0x{}".format(path, binascii.hexlify(magic)))


class Manticore(object):
    '''
    The central analysis object.

    :param str binary_path: Path to binary to analyze
    :param args: Arguments to provide to binary
    :type args: list[str]
    :ivar dict context: Global context for arbitrary data storage
    '''
    def __init__(self, binary_path, args=None, disasm='capstone'):
        assert os.path.isfile(binary_path)

        args = [] if args is None else args

        self._check_disassembler_present(disasm)
        self._disasm = disasm
        self._binary = binary_path
        self._binary_type = binary_type(binary_path)
        # yan's comment
        self._argv = args # args.programs[1:]
        self._env = {}
        # Will be set to a temporary directory if not set before running start()
        self._policy = 'random'
        self._coverage_file = None
        self._memory_errors = None
        self._should_profile = False
        self._workers = []
        # XXX(yan) '_args' will be removed soon; exists currently to ease porting
        self._args = args
        self._time_started = 0
        self._begun_trace = False
        self._assertions = {}
        self._model_hooks = {}
        self._hooks = {}
        self._running = False
        self._arch = None
        self._concrete_data = ''
        self._dumpafter = 0
        self._maxstates = 0
        self._maxstorage = 0
        self._symbolic_files = [] # list of string
        self._executor = None
        #Executor wide shared context
        self._context = {}

        # XXX(yan) This is a bit obtuse; once PE support is updated this should
        # be refactored out
        if self._binary_type == 'ELF':
            self._binary_obj = ELFFile(file(self._binary))

        log.init_logging()

    @property
    def context(self):
        ''' Convenient access to shared context '''
        if self._executor is None:
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
            if self._executor is None:
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

    # XXX(yan): args is a temporary hack to include while we continue moving
    # non-Linux platforms to new-style arg handling.
    @property
    def args(self):
        return self._args

    @args.setter
    def args(self, args):
        self._args = args

    @property
    def should_profile(self):
        return self._should_profile

    @should_profile.setter
    def should_profile(self, enable_profiling):
        self._should_profile = enable_profiling

    @property
    def concrete_data(self):
        return self._concrete_data

    @concrete_data.setter
    def concrete_data(self, data):
        self._concrete_data = data

    @property
    def maxstates(self):
        return self._maxstates

    @maxstates.setter
    def maxstates(self, max_states):
        self._maxstates = max_states

    @property
    def dumpafter(self):
        return self._dumpafter

    @dumpafter.setter
    def dumpafter(self, dump_after):
        self._dumpafter = dump_after

    @property
    def maxstorage(self):
        return self._maxstorage

    @property
    def verbosity(self):
        """Convenience interface for setting logging verbosity to one of
        several predefined logging presets. Valid values: 0-5.
        """
        return log.manticore_verbosity

    @verbosity.setter
    def verbosity(self, setting):
        """A call used to modify the level of output verbosity
        :param int setting: the level of verbosity to be used
        """
        log.set_verbosity(setting)

    @maxstorage.setter
    def maxstorage(self, max_storage):
        self._maxstorage = max_storage

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

    def add_symbolic_file(self, symbolic_file):
        '''
        Add a symbolic file. Each '+' in the file will be considered
        as symbolic, other char are concretized.
        Symbolic files must have been defined before the call to `run()`.

        :param str symbolic_file: the name of the symbolic file
        '''
        self._symbolic_files.append(symbolic_file)

    def _get_symbol_address(self, symbol):
        '''
        Return the address of |symbol| within the binary
        '''
        if self._binary_obj is None:
            return NotImplementedError("Symbols aren't supported")

        for section in self._binary_obj.iter_sections():
            if not isinstance(section, SymbolTableSection):
                continue

            symbols = section.get_symbol_by_name(symbol)
            if len(symbols) == 0:
                continue

            return symbols[0].entry['st_value']

    def _make_state(self, path):
        if self._binary_type == 'BinaryNinjaIL' or self._disasm == "binja-il":
            # Binary Ninja
            env = ['%s=%s' % (k, v) for k, v in self._env.items()]
            state = makeBinja(self._binary, self._disasm, self._argv, env,
                              self._symbolic_files, self._concrete_data)
        elif self._binary_type == 'ELF':
            # Linux
            env = ['%s=%s' % (k, v) for k, v in self._env.items()]
            state = makeLinux(self._binary, self._disasm, self._argv, env,
                              self._symbolic_files, self._concrete_data)
        elif self._binary_type == 'PE':
            # Windows
            state = makeWindows(self._args)
        elif self._binary_type == 'DECREE':
            # Decree
            state = makeDecree(self._binary, self._concrete_data)
        else:
            raise NotImplementedError("Binary {} not supported.".format(path))

        return state

    @property
    def policy(self):
        return self._policy

    @policy.setter
    def policy(self, policy):
        assert not self._running, "Can't set policy if Manticore is running."
        self._policy = policy

    @property
    def coverage_file(self):
        return self._coverage_file

    @coverage_file.setter
    def coverage_file(self, path):
        assert not self._running, "Can't set coverage file if Manticore is running."
        self._coverage_file = path

    @property
    def memory_errors_file(self):
        return self._memory_errors

    @memory_errors_file.setter
    def memory_errors_file(self, path):
        assert not self._running, "Can't set memory errors if Manticore is running."
        self._memory_errors = path

    @property
    def env(self):
        return self._env

    @env.setter
    def env(self, env):
        '''
        Update environment variables from |env|. Use repeated '+' chars for
        symbolic values.
        '''
        assert isinstance(env, dict)
        assert not self._running, "Can't set process env if Manticore is running."

        self._env.update(env)
        return self._env

    def env_add(self, key, value, overwrite=True):
        if key in self._env:
            if overwrite:
                self._env[key] = value
        else:
            self._env[key] = value

    @property
    def arch(self):
        assert self._binary is not None

        if self._arch is not None:
            return self._arch

        arch = self._binary_obj.get_machine_arch()
        if   arch == 'x86': self._arch = 'i386'
        elif arch == 'x64': self._arch = 'x86_64'
        elif arch == 'ARM': self._arch = 'arm'
        else: raise "Unsupported architecture: %s"%(arch, )

        return self._arch


    def _start_workers(self, num_processes, profiling=False):
        assert num_processes > 0, "Must have more than 0 worker processes"

        logger.info("Starting %d processes.", num_processes)

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

        if self._disasm == 'binja-il':
            target()
        else:
            for _ in range(num_processes):
                p = Process(target=target, args=())
                self._workers.append(p)
                p.start()

    def _join_workers(self):
        with WithKeyboardInterruptAs(self._executor.shutdown):
            while len(self._workers) > 0:
                w = self._workers.pop().join()


    ############################################################################
    # Model hooks + callback
    ############################################################################

    def apply_model_hooks(self, path):
        #TODO(yan): Simplify the partial function application

        # Imported straight from __main__.py; this will be re-written once the new
        # event code is in place.
        import core.cpu
        import importlib
        import platforms

        with open(path, 'r') as fnames:
            for line in fnames.readlines():
                address, cc_name, name = line.strip().split(' ')
                fmodel = platforms
                name_parts = name.split('.')
                importlib.import_module(".platforms.{}".format(name_parts[0]), 'manticore')
                for n in name_parts:
                    fmodel = getattr(fmodel,n)
                assert fmodel != platforms
                def cb_function(state):
                    state.platform.invoke_model(fmodel, prefix_args=(state.platform,))
                self._model_hooks.setdefault(int(address,0), set()).add(cb_function)

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

    def _store_state_callback(self, state, state_id):
        logger.debug("store state %r", state_id)

    def _load_state_callback(self, state, state_id):
        logger.debug("load state %r", state_id)

    def _terminate_state_callback(self, state, state_id, ex):
        #aggregates state statistics into exceutor statistics. FIXME split
        logger.debug("Terminate state %r %r ", state, state_id)
        if state is None:
            return
        state_visited = state.context.get('visited_since_last_fork', set())
        state_instructions_count = state.context.get('instructions_count', 0)
        with self.locked_context() as manticore_context:
            manticore_visited = manticore_context.get('visited', set())
            manticore_context['visited'] = manticore_visited.union(state_visited)

            manticore_instructions_count = manticore_context.get('instructions_count', 0)
            manticore_context['instructions_count'] = manticore_instructions_count + state_instructions_count

    def _forking_state_callback(self, state, expression, value, policy):
        state.record_branch(value)

    def _fork_state_callback(self, state, expression, values, policy):
        state_visited = state.context.get('visited_since_last_fork', set())
        with self.locked_context() as manticore_context:
            manticore_visited = manticore_context.get('visited', set())
            manticore_context['visited'] = manticore_visited.union(state_visited)
        state.context['visited_since_last_fork'] = set()

    def _read_register_callback(self, state, reg_name, value):
        logger.debug("Read Register %r %r", reg_name, value)

    def _write_register_callback(self, state, reg_name, value):
        logger.debug("Write Register %r %r", reg_name, value)

    def _read_memory_callback(self, state,  address, value, size):
        logger.debug("Read Memory %r %r %r", address, value, size)

    def _write_memory_callback(self, state, address, value, size):
        logger.debug("Write Memory %r %r %r", address, value, size)

    def _decode_instruction_callback(self, state, pc):
        logger.debug("Decoding stuff instruction not available")

    def _emulate_instruction_callback(self, state, instruction):
        logger.debug("About to emulate instruction")

    def _did_execute_instruction_callback(self, state, instruction):
        logger.debug("Did execute an instruction")

    def _execute_instruction_callback(self, state, instruction):
        address = state.cpu.PC
        if not issymbolic(address):
            state.context.setdefault('trace', list()).append(address)
            state.context.setdefault('visited_since_last_fork', set()).add(address)
            state.context.setdefault('visited', set()).add(address)
            count = state.context.get('instructions_count', 0)
            state.context['instructions_count'] = count + 1


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


    def finish_run(self):
        if self.should_profile:
            self._produce_profiling_data()

        _shared_context = self.context
        executor_visited = _shared_context.get('visited', set())

        #Fixme this is duplicated?
        if self.coverage_file is not None:
            with self._output.save_stream(self.coverage_file) as f:
                fmt = "0x{:016x}\n"
                for m in executor_visited:
                    f.write(fmt.format(m[1]))

        with self._output.save_stream('visited.txt') as f:
            for entry in sorted(executor_visited):
                f.write('0:{:08x}\n'.format(entry))

        with self._output.save_stream('command.sh') as f:
            f.write(' '.join(sys.argv))

        instructions_count = _shared_context.get('instructions_count', 0)
        elapsed = time.time() - self._time_started
        logger.info('Results in %s', self._output.uri)
        logger.info('Instructions executed: %d', instructions_count)
        logger.info('Coverage: %d different instructions executed', len(executor_visited))
        #logger.info('Number of paths covered %r', State.state_count())
        logger.info('Total time: %s', elapsed)
        logger.info('IPS: %d', instructions_count/elapsed)


    def run(self, procs=1, timeout=0):
        '''
        Runs analysis.

        :param int procs: Number of parallel worker processes
        :param timeout: Analysis timeout, in seconds
        '''
        assert not self._running, "Manticore is already running."
        args = self._args

        replay = None
        if hasattr(args, 'replay') and args.replay is not None:
            with open(args.replay, 'r') as freplay:
                replay = map(lambda x: int(x, 16), freplay.readlines())

        initial_state = self._make_state(self._binary)

        if args is not None and hasattr(args, 'workspace') and isinstance(args.workspace, str):
            if ':' not in args.workspace:
                ws_path = 'fs:' + args.workspace
            else:
                ws_path = args.workspace
        else:
            ws_path = None

        self._output = ManticoreOutput(ws_path)
        self._executor = Executor(initial_state,
                                  workspace=self._output.descriptor,
                                  policy=self._policy,
                                  context=self.context)



        #Link Executor events to default callbacks in manticore object
        self._executor.subscribe('did_read_register', self._read_register_callback)
        self._executor.subscribe('will_write_register', self._write_register_callback)
        self._executor.subscribe('did_read_memory', self._read_memory_callback)
        self._executor.subscribe('will_write_memory', self._write_memory_callback)
        self._executor.subscribe('will_execute_instruction', self._execute_instruction_callback)
        self._executor.subscribe('will_decode_instruction', self._decode_instruction_callback)
        self._executor.subscribe('will_store_state', self._store_state_callback)
        self._executor.subscribe('will_load_state', self._load_state_callback)
        self._executor.subscribe('will_fork_state', self._fork_state_callback)
        self._executor.subscribe('forking_state', self._forking_state_callback)
        self._executor.subscribe('will_terminate_state', self._terminate_state_callback)
        self._executor.subscribe('will_generate_testcase', self._generate_testcase_callback)

        if self._hooks:
            self._executor.subscribe('will_execute_instruction', self._hook_callback)

        if self._model_hooks:
            self._executor.subscribe('will_execute_instruction', self._model_hook_callback)

        if self._assertions:
            self._executor.subscribe('will_execute_instruction', self._assertions_callback)

        self._time_started = time.time()

        self._running = True

        if timeout > 0:
            t = Timer(timeout, self.terminate)
            t.start()
        try:
            self._start_workers(procs, profiling=self.should_profile)

            self._join_workers()
        finally:
            self._running = False
            if timeout > 0:
                t.cancel()
        #Copy back the shared conext
        self._context = dict(self._executor._shared_context)
        self._executor = None
        self.finish_run()


    def terminate(self):
        '''
        Gracefully terminate the currently-executing run. Typically called from within
        a :func:`~hook`.
        '''
        self._executor.shutdown()

    def _assertions_callback(self, state, instruction):
        pc = state.cpu.PC
        if pc not in self._assertions:
            return

        from core.parser import parse

        program = self._assertions[pc]

        #This will interpret the buffer specification written in INTEL ASM.
        # (It may dereference pointers)
        assertion = parse(program, state.cpu.read_int, state.cpu.read_register)
        if not solver.can_be_true(state.constraints, assertion):
            logger.info(str(state.cpu))
            logger.info("Assertion %x -> {%s} does not hold. Aborting state.",
                    state.cpu.pc, program)
            raise TerminateState()

        #Everything is good add it.
        state.constraints.add(assertion)

    def _hook_callback(self, state, instruction):
        pc = state.cpu.PC
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

    def _check_disassembler_present(self, disasm):
        if is_binja_disassembler(disasm):
            try:
                import binaryninja
            except ImportError:
                err = ("BinaryNinja not found! You MUST own a BinaryNinja version"
                       " that supports GUI-less processing for this option"
                       " to work. Please configure your PYTHONPATH appropriately or"
                       " select a different disassembler")
                raise SystemExit(err)
