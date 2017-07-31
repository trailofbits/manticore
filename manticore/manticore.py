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

from .core.workspace import ManticoreOutput
from .core.executor import Executor
from .core.state import State, TerminateState
from .core.parser import parse
from .core.smtlib import solver, ConstraintSet
from core.smtlib import BitVec, Bool
from .platforms import linux, decree, windows, evm
from .utils.helpers import issymbolic
from .utils.nointerrupt import WithKeyboardInterruptAs

logger = logging.getLogger('MANTICORE')

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

logging.basicConfig(format='%(asctime)s: [%(process)d]%(stateid)s %(name)s:%(levelname)s: %(message)s', stream=sys.stdout, level=logging.ERROR)
loggers = ['MANTICORE', 'VISITOR', 'EXECUTOR', 'CPU', 'REGISTERS', 'SMT', 'MEMORY', 'PLATFORM']

manticore_verbosity=''

def set_verbosity(setting):
    global manticore_verbosity
    global loggers

    logging.basicConfig(format='%(asctime)s: [%(process)d]%(stateid)s %(name)s:%(levelname)s: %(message)s', stream=sys.stdout, level=logging.ERROR)
    if isinstance(setting, (int, long)):
        #10             20            30               40             50
        #logging.DEBUG, logging.INFO, logging.WARNING, logging.ERROR, logging.CRITICAL
        levels = ['',
                  'MMMEEE',
                  'MMMEEEPPPP',
                  'MMMMEEECCCCPPPP',
                  'MMMMEEECCCCRRRRPPPP',
                  'MMMMEEEECCCCRRRRSSSSPPPP',]
        # Takes a value and ensures it's in a certain range
        def clamp(val, minimum, maximum):
            return sorted((minimum, val, maximum))[1]

        clamped = clamp(setting, 0, len(levels) - 1)
        if clamped != setting:
            logger.debug("%s not between 0 and %d, forcing to %d", setting, len(levels) - 1, clamped)

        setting = levels[clamped]

    assert isinstance(setting, str)
    initials = dict([ (x[0],x) for x in loggers])
    assert all( c in initials.keys() for c in setting )

    #Reset loggers to high (40)
    for loggername in loggers:
        logging.getLogger(loggername).addFilter(ctxfilter)
        logging.getLogger(loggername).setState = types.MethodType(loggerSetState, logging.getLogger(loggername))
        logging.getLogger(loggername).setLevel(logging.CRITICAL)

    for c in setting:
        loggername = initials[c]
        level = logging.getLogger(loggername).getEffectiveLevel() -10
        level = logging.DEBUG if level < logging.DEBUG else level
        print loggername, level
        logging.getLogger(loggername).setLevel(level)
    
    manticore_verbosity = setting

def make_evm(args):
    constraints = ConstraintSet()
    import ast
    contract = {}
    for l in open(args.programs[0]).readlines():
        l = l.strip()
        if l.startswith('#') or not '=' in l :
            continue
        name,value = l.split('=')
        name = name.strip().lower()
        contract[name]=ast.literal_eval(value)

    contract['data'] = contract.get('data', '+'*256)

    #attack, constraints, address, origin, price, data, sender, value, bytecode, header, depth):
    bytecode=contract['bytecode'].decode('hex')
    address=contract['address']
    origin=contract['sender']
    sender=contract['sender']
    value=contract['value']
    header=contract['header']
    price=contract['price']
    data = constraints.new_array(256, name='DATA', index_max=256)

    platform = evm.EVMWorld(constraints)
    user_account = platform.create_account(address=None, balance=1000)
    contract_account = platform.create_contract(origin=user_account, price=0, address=None, balance=0, init=bytecode)
    print platform
    print platform.current.address
    
    platform.run()
    kj
    initial_state = State(constraints, platform)
    initial_state.input_symbols.append(data)
    platform.data = contract['data']
    print '[+] Loading EVM program\n' # %s'% platform.disassemble()

    return initial_state


def make_decree(program, concrete_data='', **kwargs):
    constraints = ConstraintSet()
    platform = decree.SDecree(constraints, program)
    initial_state = State(constraints, platform)
    logger.info('Loading program %s', program)

    if concrete_data != '':
        logger.info('Starting with concrete input: {}'.format(concrete_data))
    platform.input.transmit(concrete_data)
    platform.input.transmit(initial_state.symbolicate_buffer('+'*14, label='RECEIVE'))
    return initial_state

def make_linux(program, argv=None, env=None, symbolic_files=None, concrete_start = ''):
    env = {} if env is None else env
    argv = [] if argv is None else argv
    env = ['%s=%s'%(k,v) for k,v in env.items()]

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


def make_windows(args, programs, context, data, offset, maxsymb, workspace, size=None, buffer=None, **kwargs):
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

def make_initial_state(binary_path, *args, **kwargs):
    magic = file(binary_path).read(4)
    if magic == '\x7fELF':
        # Linux
        state = make_linux(binary_path, *args, **kwargs)
    elif magic == 'MDMP':
        # Windows
        raise NotImplementedError("Binary {} not supported.".format(binary_path))
        state = make_windows(binary_path, *args, **kwargs)
    elif magic == '\x7fCGC':
        # Decree
        state = make_decree(binary_path, *args, **kwargs)
    elif magic == '#EVM':
        state = make_evm(binary_path, *args, **kwargs)
    else:
        raise NotImplementedError("Binary {} not supported.".format(binary_path))

    return state
        

class Manticore(object):
    '''
    The central analysis object.

    :param str binary_path: Path to binary to analyze
    :param args: Arguments to provide to binary
    :type args: list[str]
    :ivar dict context: Global context for arbitrary data storage
    '''


    def __init__(self, binary_path=None, *args, **kwargs):
        
        workspace_url = kwargs.get( 'workspace')
        if isinstance(workspace_url, str):
            if ':' not in workspace_url:
                ws_path = 'fs:' + workspace_url
            else:
                ws_path = workspace_url
        else:
            ws_path = None

        self._output = ManticoreOutput(ws_path)
        self._context = {}

        # Will be set to a temporary directory if not set before running start()
        self._coverage_file = None
        self._should_profile = False
        self._workers = []
        self._assertions = {}
        self._model_hooks = {}
        self._hooks = {} 
        self._executor = Executor(workspace=ws_path)
        
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
        self._executor.subscribe('will_terminate_state', self._terminate_state_callback)
        self._executor.subscribe('will_generate_testcase', self._generate_testcase_callback)

        if binary_path is not None:
            initial_state = make_initial_state(binary_path, *args, **kwargs)
            self.add(initial_state)

    def subscribe(self, name, callback):
        from types import MethodType
        self._executor.subscribe(name, MethodType(callback, self))


    @property
    def context(self):
        ''' Convenient access to shared context '''
        if not self.running:
            return self._context
        else:
            logger.warning("Using shared context without a lock")
            return self._executor._shared_context
        

    @contextmanager
    def locked_context(self, key=None, default=list):
        ''' It refers to the manticore shared context 
            It needs a lock. Its used like this:

            with m.context() as context:
                vsited = context['visited']
                visited.append(state.cpu.PC)
                context['visited'] = visited
        '''
        @contextmanager
        def _real_context():
            if not self.running :
                yield self._context
            else:
                with self._executor.locked_context() as context:
                    yield context

        with _real_context() as context:
            if key is None:
                yield context
            else:
                assert default in (list, dict, set)
                ctx = context.get(key, default())
                yield ctx
                context[key] = ctx

    @property
    def should_profile(self):
        return self._should_profile

    @should_profile.setter
    def should_profile(self, enable_profiling):
        self._should_profile = enable_profiling

    @property
    def coverage_file(self):
        return self._coverage_file

    @coverage_file.setter
    def coverage_file(self, path):
        assert not self.running, "Can't set coverage file if Manticore is running."
        self._coverage_file = path



    @property
    def running(self):
        return self._executor._running.value

    
    @property
    def policy(self):
        return self._policy

    @policy.setter
    def policy(self, policy):
        assert not self.running, "Can't set policy if Manticore is running."
        self._policy = policy

    def add(self, state):
        self._executor.add(state)

    ###########################################################################
    # Workers                                                                 #
    ###########################################################################
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

        for _ in range(num_processes):
            p = Process(target=target, args=())
            self._workers.append(p)
            p.start()

    def _join_workers(self):
        with WithKeyboardInterruptAs(self._executor.shutdown):    
            while len(self._workers) > 0:
                w = self._workers.pop().join()

    ############################################################################
    # Common hooks + callback
    ############################################################################
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
                self._executor.subscribe('will_execute_instruction', self._assertions_callback)

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



    ##########################################################################
    #Some are Place holders Remove 

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

    def _fork_state_callback(self, state, expression, values, policy):
        state_visited = state.context.get('visited_since_last_fork', set())
        with self.locked_context() as manticore_context:
            manticore_visited = manticore_context.get('visited', set())
            manticore_context['visited'] = manticore_visited.union(state_visited)
        state.context['visited_since_last_fork'] = set()

        logger.debug("About to store state %r %r %r", state, expression, values, policy)

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
            state.context.setdefault('visited_since_last_fork', set()).add(address)
            state.context.setdefault('visited', set()).add(address)
            count = state.context.get('instructions_count', 0)
            state.context['instructions_count'] = count + 1


    def _generate_testcase_callback(self, state, message = 'Testcase generated'):
        '''
        Create a serialized description of a given state.
        :param state: The state to generate information about
        :param message: Accompanying message
        '''
        testcase_id = self._output.save_testcase(state, message)
        logger.debug("Generated testcase No. %d - %s", testcase_id, message)

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
        #Copy the local main context to the shared conext
        self._executor._shared_context.update(self._context)

    def _finish_run(self):
        assert not self.running
        #Copy back the shared context
        self._context = dict(self._executor._shared_context)

        if self.should_profile:
            self._produce_profiling_data()

        executor_visited = self.context.get('visited', set())

        #Fixme this is duplicated?
        if self.coverage_file is not None:
            with self._output.save_stream(self.coverage_file) as f:
                fmt = "0x{:016x}\n"
                for m in executor_visited:
                    f.write(fmt.format(m[1]))

        with self._output.save_stream('visited.txt') as f:
            for entry in sorted(executor_visited):
                f.write('0:{:08x}\n'.format(entry))

        #if self.coverage_file is not None:
        #    import shutil
        #    shutil.copyfile('visited.txt', self.coverage_file)

        with self._output.save_stream('command.sh') as f:
            f.write(' '.join(sys.argv))

        instructions_count = self.context.get('instructions_count',0)
        elapsed = time.time()-self._time_started
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
        assert not self.running, "Manticore is already running."
        self._start_run()
        self._time_started = time.time()
        if timeout > 0:
            t = Timer(timeout, self.terminate)
            t.start()
        try:
            self._start_workers(procs, profiling=self.should_profile)

            self._join_workers()
        finally:
            if timeout > 0:
                t.cancel()
        self._finish_run()


    def terminate(self):
        '''
        Gracefully terminate the currently-executing run. Typically called from within
        a :func:`~hook`.
        '''
        self._executor.shutdown()


    #############################################################################
    #############################################################################
    #############################################################################
    # MOve all the following elsewhere
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
            if len(symbols) == 0:
                continue

            return symbols[0].entry['st_value']
