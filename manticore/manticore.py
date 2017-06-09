import os
import sys
import time
import types
import logging
import binascii
import tempfile
import functools

from multiprocessing import Manager, Pool
from multiprocessing import Process

from threading import Timer

from elftools.elf.elffile import ELFFile
from elftools.elf.sections import SymbolTableSection

from .core.executor import Executor
from .core.state import State, AbandonState
from .core.parser import parse
from .core.smtlib import solver, Expression, Operators, SolverException, Array, ConstraintSet
from core.smtlib import BitVec, Bool
from .platforms import linux, decree, windows
from .utils.helpers import issymbolic

logger = logging.getLogger('MANTICORE')

def makeDecree(args):
    constraints = ConstraintSet()
    platform = decree.SDecree(constraints, ','.join(args.programs))
    initial_state = State(constraints, platform)
    logger.info('Loading program %s', args.programs)

    #if args.data != '':
    #    logger.info('Starting with concrete input: {}'.format(args.data))
    platform.input.transmit(args.data)
    platform.input.transmit(initial_state.symbolicate_buffer('+'*14, label='RECEIVE'))
    return initial_state

def makeLinux(program, argv, env, symbolic_files, concrete_start = ''):
    logger.info('Loading program %s', program)

    constraints = ConstraintSet()

    platform = linux.SLinux(program, argv=argv, envp=env,
                            symbolic_files=symbolic_files)
    initial_state = State(constraints, platform)

    if concrete_start != '':
        logger.info('Starting with concrete input: {}'.format(concrete_start))

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
    platform.input.write(initial_state.symbolicate_buffer('+'*256, label='STDIN'))

    return initial_state 


def makeWindows(args):
    assert args.size is not None, "Need to specify buffer size"
    assert args.buffer is not None, "Need to specify buffer base address"
    logger.debug('Loading program %s', args.programs)
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
    :ivar context: SyncManager managed `dict` shared between Manticore worker processes
    '''


    def __init__(self, binary_path, args=None):
        assert os.path.isfile(binary_path)

        args = [] if args is None else args

        self._binary = binary_path
        self._binary_type = binary_type(binary_path)
        self._argv = args # args.programs[1:]
        self._env = {}
        # Will be set to a temporary directory if not set before running start()
        self._workspace_path = None
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
        self._verbosity = 0
        self._symbolic_files = [] # list of string

        manager = Manager()

        self.context = manager.dict()

        # XXX(yan) This is a bit obtuse; once PE support is updated this should
        # be refactored out
        if self._binary_type == 'ELF':
            self._binary_obj = ELFFile(file(self._binary))

        self._init_logging()

    def _init_logging(self): 

        def loggerSetState(logger, stateid):
            logger.filters[0].stateid = stateid

        class ContextFilter(logging.Filter):
            '''
            This is a filter which injects contextual information into the log.
            '''
            def filter(self, record):
                if hasattr(self, 'stateid') and isinstance(self.stateid, int):
                    record.stateid = '[%d]' % self.stateid
                else:
                    record.stateid = ''
                return True

        ctxfilter = ContextFilter()

        logging.basicConfig(format='%(asctime)s: [%(process)d]%(stateid)s %(name)s:%(levelname)s: %(message)s', stream=sys.stdout)

        for loggername in ['VISITOR', 'EXECUTOR', 'CPU', 'REGISTERS', 'SMT', 'MEMORY', 'MAIN', 'PLATFORM']:
            logging.getLogger(loggername).addFilter(ctxfilter)
            logging.getLogger(loggername).setState = types.MethodType(loggerSetState, logging.getLogger(loggername))
        
        logging.getLogger('SMT').setLevel(logging.INFO)
        logging.getLogger('MEMORY').setLevel(logging.INFO)
        logging.getLogger('LIBC').setLevel(logging.INFO)

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

    @maxstorage.setter
    def maxstorage(self, max_storage):
        self._maxstorage = max_storage

    @property
    def verbosity(self):
        '''
        Convenience interface for setting logging verbosity to one of several predefined
        logging presets. Valid values: 0-5
        '''
        return self._verbosity

    @verbosity.setter
    def verbosity(self, setting):
        levels = [[],
                  [('MAIN', logging.INFO), ('EXECUTOR', logging.INFO)],
                  [('PLATFORM', logging.DEBUG)],
                  [('MEMORY', logging.DEBUG), ('CPU', logging.DEBUG)],
                  [('REGISTERS', logging.DEBUG)],
                  [('SMT', logging.DEBUG)]]
        # Takes a value and ensures it's in a certain range
        def clamp(val, minimum, maximum):
            return sorted((minimum, val, maximum))[1]

        clamped = clamp(setting, 0, len(levels) - 1)
        if clamped != setting:
            logger.debug("%s not between 0 and %d, forcing to %d", setting, len(levels) - 1, clamped)
        for level in range(clamped + 1):
            for log_type, log_level in levels[level]:
                logging.getLogger(log_type).setLevel(log_level)
        self._verbosity = clamped

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
        if self._binary_type == 'ELF':
            # Linux
            env = ['%s=%s'%(k,v) for k,v in self._env.items()]
            state = makeLinux(self._binary, self._argv, env, self._symbolic_files, self._concrete_data)
        elif self._binary_type == 'PE':
            # Windows
            state = makeWindows(self._args)
        elif self._binary_type == 'DECREE':
            # Decree
            state = makeDecree(self._args)
        else:
            raise NotImplementedError("Binary {} not supported.".format(path))

        return state
        
    @property
    def workspace(self):
        if self._workspace_path is None:
            self._workspace_path = self._make_workspace()

        return self._workspace_path

    @workspace.setter
    def workspace(self, path):
        assert not self._running, "Can't set workspace if Manticore is running."

        if os.path.exists(path):
            assert os.path.isdir(path)
        else:
            os.mkdir(path)

        self._workspace_path = os.path.abspath(path)

    def _make_workspace(self):
        ''' Make working directory '''
        return os.path.abspath(tempfile.mkdtemp(prefix="mcore_", dir='./'))

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
        

    def _start_workers(self, num_processes):
        assert num_processes > 0, "Must have more than 0 worker processes"

        logger.info("Starting %d processes.", num_processes)

        for _ in range(num_processes):
            p = Process(target=self._executor.run, args=())
            self._workers.append(p)
            p.start()

    def _join_workers(self):
        while len(self._workers) > 0:
            w = self._workers.pop()
            try:
                w.join()
            except KeyboardInterrupt, e:
                self._executor.shutdown()
                # multiprocessing.dummy.Process does not support terminate
                if hasattr(w, 'terminate'):
                    w.terminate()

                self._workers.append(w)


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

    def _model_hook_callback(self, state):
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


    def run(self, procs=1, timeout=0):
        '''
        Runs analysis.

        :param int procs: Number of parallel worker processes
        :param timeout: Analysis timeout, in seconds
        '''
        assert not self._running, "Manticore is already running."
        args = self._args

        replay=None
        if hasattr(args, 'replay') and args.replay is not None:
            with open(args.replay, 'r') as freplay:
                replay = map(lambda x: int(x, 16), freplay.readlines())

        state = self._make_state(self._binary)

        self._executor = Executor(state,
                                  workspace=self.workspace, 
                                  policy=self._policy, 
                                  dumpafter=self.dumpafter, 
                                  maxstates=self.maxstates,
                                  maxstorage=self.maxstorage,
                                  replay=replay,
                                  dumpstats=self.should_profile)
        

        if self._hooks:
            self._executor.will_execute_pc += self._hook_callback

        if self._model_hooks:
            self._executor.will_execute_pc += self._model_hook_callback

        if self._assertions:
            self._executor.will_execute_pc += self._assertions_callback

        self._time_started = time.time()

        self._running = True


        if timeout > 0:
            t = Timer(timeout, self.terminate)
            t.start()
        try:
            self._start_workers(procs)

            self._join_workers()
        finally:
            self._running = False
            if timeout > 0:
                t.cancel()

    def terminate(self):
        '''
        Gracefully terminate the currently-executing run. Typically called from within
        a :func:`~hook`.
        '''
        self._executor.shutdown()

    def _assertions_callback(self, state):
        pc = state.cpu.PC
        if pc not in self._assertions:
            return

        from core.parser import parse

        program = self._assertions[pc]

        #This will interpret the buffer specification written in INTEL ASM.
        # (It may dereference pointers)
        assertion = parse(program, state.cpu.read, state.cpu.read_register)
        if not solver.can_be_true(state.constraints, assertion):
            logger.info(str(state.cpu))
            logger.info("Assertion %x -> {%s} does not hold. Aborting state.",
                    state.cpu.PC, program)
            raise AbandonState()

        #Everything is good add it.
        state.constraints.add(assertion)

    def _hook_callback(self, state):
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

    def dump_stats(self):
        if self.coverage_file is not None:
            with open(self.coverage_file, "w") as f:
                fmt = "0x{:016x}\n"
                for m in self._executor.visited:
                    f.write(fmt.format(m[1]))
                    
        if self.memory_errors_file is not None:
            with open(self._args.errorfile, "w") as f:
                fmt = "0x{:016x}\n"
                for m in self._executor.errors:
                    f.write(fmt.format(m))

        self._executor.dump_stats()

        logger.info('Results dumped in %s', self.workspace)
        logger.info('Instructions executed: %d', self._executor.count)
        logger.info('Coverage: %d different instructions executed', len(self._executor.visited))
        logger.info('Number of paths covered %r', State.state_count())
        logger.info('Total time: %s', time.time()-self._time_started)
        logger.info('IPS: %d', self._executor.count/(time.time()-self._time_started))

        visited = ['%d:%08x'%site for site in self._executor.visited]
        with file(os.path.join(self.workspace,'visited.txt'),'w') as f:
            for entry in sorted(visited):
                f.write(entry + '\n')

        with file(os.path.join(self.workspace,'command.sh'),'w') as f:
            f.write(' '.join(sys.argv))
