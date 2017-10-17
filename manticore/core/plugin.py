import logging
from ..utils.helpers import issymbolic
from ..utils.event import Eventful
logger = logging.getLogger('MANTICORE')


class Plugin(object):
    def __init__(self): 
        self.manticore = None

class Tracer(Plugin):
    def will_start_run_callback(self, state):
        state.context['trace'] = []

    def did_execute_instruction_callback(self, state, pc, target_pc, instruction):
        state.context['trace'].append(pc)

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
        if state is None: #FIXME Can it be None?
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
        #Fixme this is duplicated?
        if self.coverage_file is not None:
            with self.manticore._output.save_stream(self.coverage_file) as f:
                fmt = "0x{:016x}\n"
                for m in executor_visited:
                    f.write(fmt.format(m))
        logger.info('Coverage: %d different instructions executed', len(executor_visited))



#TODO document all callbacks
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
        logger.info('will_fork_state %r %r %r %r',parent_state, expression, solutions, policy)
    def did_fork_state_callback(self, child_state, expression, new_value, policy):
        logger.info('did_fork_state %r %r %r %r', child_state, expression, new_value, policy)
    def did_load_state_callback(self, state, state_id):
        logger.info('did_load_state %r %r', state, state_id)
    def did_enqueue_state_callback(self, state, state_id):
        logger.info('did_enqueue_state %r %r', state, state_id)
    def will_terminate_state_callback(self, state, state_id, exception):
        logger.info('will_terminate_state %r %r %r', state, state_id, exception)
    def will_generate_testcase_callback(self,  state, testcase_id, message):
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


