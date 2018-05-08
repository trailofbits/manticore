import logging

from capstone import CS_GRP_JUMP

from ..utils.helpers import issymbolic
from contextlib import contextmanager

logger = logging.getLogger(__name__)


class Plugin(object):
    @contextmanager
    def locked_context(self, key=None, value_type=list):
        """
        A context manager that provides safe parallel access to the global Manticore context.
        This should be used to access the global Manticore context
        when parallel analysis is activated. Code within the `with` block is executed
        atomically, so access of shared variables should occur within.
        """
        plugin_context_name = str(type(self))
        with self.manticore.locked_context(plugin_context_name, dict) as context:
            assert value_type in (list, dict, set)
            ctx = context.get(key, value_type())
            yield ctx
            context[key] = ctx

    @property
    def context(self):
        ''' Convenient access to shared context '''
        plugin_context_name = str(type(self))
        if plugin_context_name not in self.manticore.context:
            self.manticore.context[plugin_context_name] = {}
        return self.manticore.context[plugin_context_name]

    def __init__(self):
        self.manticore = None
        self.last_reg_state = {}


def _dict_diff(d1, d2):
    '''
    Produce a dict that includes all the keys in d2 that represent different values in d1, as well as values that
    aren't in d1.

    :param dict d1: First dict
    :param dict d2: Dict to compare with
    :rtype: dict
    '''
    d = {}
    for key in set(d1).intersection(set(d2)):
        if d2[key] != d1[key]:
            d[key] = d2[key]
    for key in set(d2).difference(set(d1)):
        d[key] = d2[key]
    return d


class Tracer(Plugin):
    def will_start_run_callback(self, state):
        state.context['trace'] = []

    def did_execute_instruction_callback(self, state, pc, target_pc, instruction):
        state.context['trace'].append(pc)


class ExtendedTracer(Plugin):
    def __init__(self):
        '''
        Record a detailed execution trace
        '''
        super(ExtendedTracer, self).__init__()
        self.last_dict = {}
        self.current_pc = None
        self.context_key = 'e_trace'

    def will_start_run_callback(self, state):
        state.context[self.context_key] = []

    def register_state_to_dict(self, cpu):
        d = {}
        for reg in cpu.canonical_registers:
            val = cpu.read_register(reg)
            d[reg] = val if not issymbolic(val) else '<sym>'
        return d

    def will_execute_instruction_callback(self, state, pc, instruction):
        self.current_pc = pc

    def did_execute_instruction_callback(self, state, pc, target_pc, instruction):
        reg_state = self.register_state_to_dict(state.cpu)
        entry = {
            'type': 'regs',
            'values': _dict_diff(self.last_dict, reg_state)
        }
        self.last_dict = reg_state
        state.context[self.context_key].append(entry)

    def will_read_memory_callback(self, state, where, size):
        if self.current_pc == where:
            return

        #print 'will_read_memory %x %r, current_pc %x'%(where, size, self.current_pc)

    def did_read_memory_callback(self, state, where, value, size):
        if self.current_pc == where:
            return

        #print 'did_read_memory %x %r %r, current_pc %x'%(where, value, size, self.current_pc)

    def will_write_memory_callback(self, state, where, value, size):
        if self.current_pc == where:
            return

        #print 'will_write_memory %x %r %r, current_pc %x'%(where, value, size, self.current_pc)

    def did_write_memory_callback(self, state, where, value, size):
        if self.current_pc == where:
            raise Exception
            return

        entry = {
            'type': 'mem_write',
            'where': where,
            'value': value,
            'size': size
        }
        state.context[self.context_key].append(entry)


class Follower(Plugin):
    def __init__(self, trace):
        self.index = 0
        self.trace = trace
        self.last_instruction = None
        self.symbolic_ranges = []
        self.active = True
        super(self.__class__, self).__init__()

    def add_symbolic_range(self, pc_start, pc_end):
        self.symbolic_ranges.append((pc_start, pc_end))

    def get_next(self, type):
        event = self.trace[self.index]
        assert event['type'] == type
        self.index += 1
        return event

    def did_write_memory_callback(self, state, where, value, size):
        if not self.active:
            return
        write = self.get_next('mem_write')

        if not issymbolic(value):
            return

        assert write['where'] == where and write['size'] == size
        # state.constrain(value == write['value'])

    def did_execute_instruction_callback(self, state, last_pc, pc, insn):
        if not self.active:
            return
        event = self.get_next('regs')
        self.last_instruction = event['values']
        if issymbolic(pc):
            state.constrain(state.cpu.RIP == self.last_instruction['RIP'])
        else:
            for start, stop in self.symbolic_ranges:
                if start <= pc <= stop:
                    self.active = False


class RecordSymbolicBranches(Plugin):
    def will_start_run_callback(self, state):
        state.context['branches'] = {}

    def did_execute_instruction_callback(self, state, last_pc, target_pc, instruction):
        if state.context.get('forking_pc', False):
            branches = state.context['branches']
            branch = (last_pc, target_pc)
            if branch in branches:
                branches[branch] += 1
            else:
                branches[branch] = 1
            state.context['forking_pc'] = False

        if issymbolic(target_pc):
            state.context['forking_pc'] = True


class InstructionCounter(Plugin):

    def will_terminate_state_callback(self, state, state_id, ex):
        if state is None:  # FIXME Can it be None?
            return
        state_instructions_count = state.context.get('instructions_count', 0)

        with self.manticore.locked_context() as manticore_context:
            manticore_instructions_count = manticore_context.get('instructions_count', 0)
            manticore_context['instructions_count'] = manticore_instructions_count + state_instructions_count

    def did_execute_instruction_callback(self, state, prev_pc, target_pc, instruction):
        address = prev_pc
        if not issymbolic(address):
            count = state.context.get('instructions_count', 0)
            state.context['instructions_count'] = count + 1

    def did_finish_run_callback(self):
        _shared_context = self.manticore.context
        instructions_count = _shared_context.get('instructions_count', 0)
        logger.info('Instructions executed: %d', instructions_count)


class Visited(Plugin):
    def __init__(self, coverage_file='visited.txt'):
        super(Visited, self).__init__()
        self.coverage_file = coverage_file

    def will_terminate_state_callback(self, state, state_id, ex):
        if state is None:
            return
        state_visited = state.context.get('visited_since_last_fork', set())
        with self.manticore.locked_context() as manticore_context:
            manticore_visited = manticore_context.get('visited', set())
            manticore_context['visited'] = manticore_visited.union(state_visited)

    def will_fork_state_callback(self, state, expression, values, policy):
        state_visited = state.context.get('visited_since_last_fork', set())
        with self.manticore.locked_context() as manticore_context:
            manticore_visited = manticore_context.get('visited', set())
            manticore_context['visited'] = manticore_visited.union(state_visited)
        state.context['visited_since_last_fork'] = set()

    def did_execute_instruction_callback(self, state, prev_pc, target_pc, instruction):
        state.context.setdefault('visited_since_last_fork', set()).add(prev_pc)
        state.context.setdefault('visited', set()).add(prev_pc)

    def did_finish_run_callback(self):
        _shared_context = self.manticore.context
        executor_visited = _shared_context.get('visited', set())
        # Fixme this is duplicated?
        if self.coverage_file is not None:
            with self.manticore._output.save_stream(self.coverage_file) as f:
                fmt = "0x{:016x}\n"
                for m in executor_visited:
                    f.write(fmt.format(m))
        logger.info('Coverage: %d different instructions executed', len(executor_visited))


class ConcreteTraceFollower(Plugin):
    def __init__(self, source=None):
        '''
        :param iterable source: Iterator producing instruction pointers to be followed
        '''
        super(ConcreteTraceFollower, self).__init__()
        self.source = source

    def will_start_run_callback(self, state):
        self.saved_flags = None

    def will_execute_instruction_callback(self, state, pc, instruction):
        if not instruction.group(CS_GRP_JUMP):
            self.saved_flags = None
            return

        # Likely unconditional
        if not instruction.regs_read:
            self.saved_flags = None
            return

        self.saved_flags = state.cpu.RFLAGS
        state.cpu.RFLAGS = state.new_symbolic_value(state.cpu.address_bit_size)

    def did_execute_instruction_callback(self, state, pc, target_pc, instruction):
        # Should direct execution via trace
        if self.saved_flags:
            state.cpu.RFLAGS = self.saved_flags

# TODO document all callbacks


class ExamplePlugin(Plugin):
    def will_decode_instruction_callback(self, state, pc):
        logger.info('will_decode_instruction', state, pc)

    def will_execute_instruction_callback(self, state, pc, instruction):
        logger.info('will_execute_instruction', state, pc, instruction)

    def did_execute_instruction_callback(self, state, pc, target_pc, instruction):
        logger.info('did_execute_instruction', state, pc, target_pc, instruction)

    def will_start_run_callback(self, state):
        ''' Called once at the begining of the run.
            state is the initial root state
        '''
        logger.info('will_start_run')

    def did_finish_run_callback(self):
        logger.info('did_finish_run')

    def did_enqueue_state_callback(self, state_id, state):
        ''' state was just got enqueued in the executor procesing list'''
        logger.info('did_enqueue_state %r %r', state_id, state)

    def will_fork_state_callback(self, parent_state, expression, solutions, policy):
        logger.info('will_fork_state %r %r %r %r', parent_state, expression, solutions, policy)

    def did_fork_state_callback(self, child_state, expression, new_value, policy):
        logger.info('did_fork_state %r %r %r %r', child_state, expression, new_value, policy)

    def did_load_state_callback(self, state, state_id):
        logger.info('did_load_state %r %r', state, state_id)

    def did_enqueue_state_callback(self, state, state_id):
        logger.info('did_enqueue_state %r %r', state, state_id)

    def will_terminate_state_callback(self, state, state_id, exception):
        logger.info('will_terminate_state %r %r %r', state, state_id, exception)

    def will_generate_testcase_callback(self, state, testcase_id, message):
        logger.info('will_generate_testcase %r %r %r', state, testcase_id, message)

    def will_read_memory_callback(self, state, where, size):
        logger.info('will_read_memory %r %r %r', state, where, size)

    def did_read_memory_callback(self, state, where, value, size):
        logger.info('did_read_memory %r %r %r %r', state, where, value, size)

    def will_write_memory_callback(self, state, where, value, size):
        logger.info('will_write_memory %r %r %r', state, where, value, size)

    def did_write_memory_callback(self, state, where, value, size):
        logger.info('did_write_memory %r %r %r %r', state, where, value, size)

    def will_read_register_callback(self, state, register):
        logger.info('will_read_register %r %r', state, register)

    def did_read_register_callback(self, state, register, value):
        logger.info('did_read_register %r %r %r', state, register, value)

    def will_write_register_callback(self, state, register, value):
        logger.info('will_write_register %r %r %r', state, register, value)

    def did_write_register_callback(self, state, register, value):
        logger.info('did_write_register %r %r %r', state, register, value)
