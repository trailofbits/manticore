from ..core.plugin import Plugin
from .state_merging import merge_constraints, is_merge_possible, merge
import logging

logger = logging.getLogger(__name__)


class Merger(Plugin):
    def on_register(self):
        p = self.manticore._publish
        self.manticore._publish = lambda *args, **kwargs: None
        for state in self.manticore.ready_states:
            self.did_fork_state_callback(state, None, None, None)

        self.manticore._publish = p

    def load_state(self, state_id, delete=False):
        """
        Loads a state in Manticore with state-id = `state_id` by using the corresponding API in Executor
        :param state_id: state-id for state that is being loaded
        :param delete: If set to True, deletes the state with state-id = `state_id`
        :return: None
        """
        state = self.manticore._workspace.load_state(state_id, delete=delete)
        return state

    def delete_state(self, state_id):
        """
        Deletes a state in Manticore with state-id = `state_id` by using the corresponding API in Executor
        :param state_id: state-id for state that is being deleted
        :return: None
        """
        with self.manticore._lock:
            self.manticore._ready_states.remove(state_id)
            self.manticore._remove(state_id)

    def replace_state(self, state_id, state):
        """
        Replaces a state in Manticore with state-id = `state_id` by using the corresponding API in Executor
        :param state_id: state-id for state that is being replaced
        :param state: State object that is replacing the existing state with `state_id`
        :return: None
        """
        return self.manticore._save(state, state_id=state_id)

    def did_fork_state_callback(self, state, expression, new_value, policy):
        state_id = state.id
        """That means no one else has to offer one Message Input

        Maintains a `cpu_stateid_dict` in context that keeps maps program counter values to a list of state-id values
        for states that will execute the instruction that that program counter as the next instruction
        :param state_id: id for state that was just enqueued
        :param state: State object that was just enqueued
        :return: None
        """
        # when a new state is addded to the list we save it so we do not have
        # to repload all states when try to merges last PC
        with self.locked_context("cpu_stateid_dict", dict) as cpu_stateid_dict:
            # as we may be running in a different process we need to access this
            # on a lock and over shared memory like this
            state_id_list = cpu_stateid_dict.get(state.cpu.PC, list())
            state_id_list.append(state_id)
            cpu_stateid_dict[state.cpu.PC] = state_id_list

    def will_load_state_callback(self, current_state_id):
        """
        Checks if the state to be loaded (referenced by `current_state_id` can be merged with another currently enqueued
        state and replaced by the merged state
        :param current_state_id: state about to be loaded
        :return: None
        """
        # When a state is loaded for exploration lets check if we can find it a
        # mate for merging
        with self.locked_context("cpu_stateid_dict", dict) as cpu_stateid_dict:
            # we get the lock and get a copy of the shared context
            merged_state = self.load_state(current_state_id)
            states_at_pc = cpu_stateid_dict.get(merged_state.cpu.PC, [])

            # lets remove ourself from the list of waiting states
            # assert current_state_id in states_at_pc #???
            if current_state_id in states_at_pc:
                states_at_pc.remove(current_state_id)

            # Iterate over all remaining states that are waiting for exploration
            # at the same PC
            merged_ids = []
            for new_state_id in states_at_pc:
                new_state = self.load_state(new_state_id)
                (exp_merged_state, exp_new_state, merged_constraint) = merge_constraints(
                    merged_state.constraints, new_state.constraints
                )
                is_mergeable, reason = is_merge_possible(merged_state, new_state, merged_constraint)

                if is_mergeable:
                    # Ok we'll merge it!
                    merged_state = merge(
                        merged_state, new_state, exp_merged_state, merged_constraint
                    )

                    # lets remove the vestigial links to the old state
                    self.delete_state(new_state_id)

                    merged_ids.append(new_state_id)
                    is_mergeable = "succeeded"
                else:
                    is_mergeable = "failed because of " + reason
                debug_string = (
                    "at PC = "
                    + hex(merged_state.cpu.PC)
                    + ", merge "
                    + is_mergeable
                    + " for state id = "
                    + str(current_state_id)
                    + " and "
                    + str(new_state_id)
                )
                logger.debug(debug_string)

            for i in merged_ids:
                states_at_pc.remove(i)

            cpu_stateid_dict[merged_state.cpu.PC] = states_at_pc

            # Ok so we have merged current_state_id with {merged_ids}
            # And removed all merged_ids from everywhere

            # UGLY we are replacing a state_id. This may be breaking caches in
            # the future
            self.replace_state(current_state_id, merged_state)
