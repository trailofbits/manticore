from ..core.plugin import Plugin, logger


class ExamplePlugin(Plugin):
    def will_decode_instruction_callback(self, state, pc):
        logger.info('will_decode_instruction %r %r', state, pc)

    def will_execute_instruction_callback(self, state, pc, instruction):
        logger.info('will_execute_instruction %r %r %r', state, pc, instruction)

    def did_execute_instruction_callback(self, state, pc, target_pc, instruction):
        logger.info('did_execute_instruction %r %r %r %r', state, pc, target_pc, instruction)

    def will_start_run_callback(self, state):
        ''' Called once at the beginning of the run.
            state is the initial root state
        '''
        logger.info('will_start_run')

    def did_finish_run_callback(self):
        logger.info('did_finish_run')

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

    def will_generate_testcase_callback(self, state, testcase, message):
        logger.info('will_generate_testcase %r %r %r', state, testcase, message)

    def will_read_memory_callback(self, state, where, size):
        logger.info('will_read_memory %r %r %r', state, where, size)

    def did_read_memory_callback(self, state, where, value, size):
        logger.info('did_read_memory %r %r %r %r', state, where, value, size)

    def will_write_memory_callback(self, state, where, value, size):
        logger.info('will_write_memory %r %r %r %r', state, where, value, size)

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
