import sys

from functools import reduce

import re

from ..core.plugin import Plugin
from ..core.smtlib import Operators


class FilterFunctions(Plugin):
    def __init__(
        self, regexp=r".*", mutability="both", depth="both", fallback=False, include=True, **kwargs
    ):
        """
            Constrain input based on function metadata. Include or avoid functions selected by the specified criteria.

            Examples:
            #Do not explore any human transactions that end up calling a constant function
            no_human_constant = FilterFunctions(depth='human', mutability='constant', include=False)

            #At human tx depth only accept synthetic check functions
            only_tests = FilterFunctions(regexp=r'mcore_.*', depth='human', include=False)

            :param regexp: a regular expression over the name of the function '.*' will match all functions
            :param mutability: mutable, constant or both will match functions declared in the abi to be of such class
            :param depth: match functions in internal transactions, in human initiated transactions or in both types
            :param fallback: if True include the fallback function. Hash will be 00000000 for it
            :param include: if False exclude the selected functions, if True include them
        """
        super().__init__(**kwargs)
        depth = depth.lower()
        if depth not in ("human", "internal", "both"):
            raise ValueError
        mutability = mutability.lower()
        if mutability not in ("mutable", "constant", "both"):
            raise ValueError

        # fixme better names for member variables
        self._regexp = regexp
        self._mutability = mutability
        self._depth = depth
        self._fallback = fallback
        self._include = include

    def will_open_transaction_callback(self, state, tx):
        world = state.platform
        tx_cnt = len(world.all_transactions)
        # Constrain input only once per tx, per plugin
        if state.context.get("constrained%d" % id(self), 0) != tx_cnt:
            state.context["constrained%d" % id(self)] = tx_cnt

            if self._depth == "human" and not tx.is_human:
                return
            if self._depth == "internal" and tx.is_human:
                return

            # Get metadata if any for the target address of current tx
            md = self.manticore.get_metadata(tx.address)
            if md is None:
                return
            # Let's compile  the list of interesting hashes
            selected_functions = []

            for func_hsh in md.function_selectors:
                abi = md.get_abi(func_hsh)
                if abi["type"] == "fallback":
                    continue
                if self._mutability == "constant" and not abi.get("constant", False):
                    continue
                if self._mutability == "mutable" and abi.get("constant", False):
                    continue
                if not re.match(self._regexp, abi["name"]):
                    continue
                selected_functions.append(func_hsh)

            if self._fallback and md.has_non_default_fallback_function:
                selected_functions.append(md.fallback_function_selector)

            if self._include:
                # constrain the input so it can take only the interesting values
                constraint = reduce(Operators.OR, (tx.data[:4] == x for x in selected_functions))
                state.constrain(constraint)
            else:
                # Avoid all not selected hashes
                for func_hsh in md.function_selectors:
                    if func_hsh in selected_functions:
                        constraint = tx.data[:4] != func_hsh
                        state.constrain(constraint)


class LoopDepthLimiter(Plugin):
    """ This just aborts explorations that are too deep """

    def __init__(self, loop_count_threshold=5, **kwargs):
        super().__init__(**kwargs)
        self.loop_count_threshold = loop_count_threshold

    def will_start_run_callback(self, *args):
        with self.manticore.locked_context("seen_rep", dict) as reps:
            reps.clear()

    def will_execute_instruction_callback(self, state, pc, insn):
        world = state.platform
        with self.manticore.locked_context("seen_rep", dict) as reps:
            item = (
                world.current_transaction.sort == "CREATE",
                world.current_transaction.address,
                pc,
            )
            if item not in reps:
                reps[item] = 0
            reps[item] += 1
            if reps[item] > self.loop_count_threshold:
                state.abandon()


class VerboseTrace(Plugin):
    """
    Generates a verbose trace of EVM execution and saves in workspace into `state<id>.trace`.

    Example output can be seen in test_eth_plugins.
    """

    def will_evm_execute_instruction_callback(self, state, instruction, arguments):
        current_vm = state.platform.current_vm
        state.context.setdefault("str_trace", []).append(str(current_vm))

    def generate_testcase(self, state, testcase, message):
        trace = state.context.get("str_trace", [])

        with testcase.open_stream("verbose_trace") as vt:
            for t in trace:
                vt.write(t + "\n")


class VerboseTraceStdout(Plugin):
    """
    Same as VerboseTrace but prints to stdout. Note that you should use it only if Manticore
    is run with procs=1 as otherwise, the output will be clobbered.
    """

    def will_evm_execute_instruction_callback(self, state, instruction, arguments):
        print(state.platform.current_vm)


class TXStorageChanged(Plugin):
    ''' TODO: reword
        This state will ignore states that are the result of executing a
        transaction that did not write to the storage.

        When this plugin is enabled transactions that wont write to the storage
        are considered not to change the evm world state and hence ignored as a
        starting point for the following human transaction.
    '''

    def did_open_transaction_callback(self, state, tx, *args):
        ''' We need a stack. Each tx (internal or not) starts with a "False" flag
            denoting that it did not write anything to the storage
        '''
        state.context['written'].append(False)

    def did_close_transaction_callback(self, state, tx, *args):
        ''' When a tx (internal or not) is closed a value is popped out from the
        flag stack. Depending on the result if the storage is not rolled back the
        next flag in the stack is updated. Not that if the a tx is reverted the
        changes it may have done on the storage will not affect the final result.

        '''
        flag = state.context['written'].pop()
        if tx.result in {"RETURN", "STOP"}:
            flag = flag or ((tx.result == "RETURN") and (tx.sort == 'CREATE'))
            state.context['written'][-1] = state.context['written'][-1] or flag

    def did_evm_write_storage_callback(self, state, *args):
        ''' Turn on the corresponding flag is the storage has been modified.
        Note: subject to change if the current transaction is reverted'''
        state.context['written'][-1] = True

    def will_run_callback(self, *args):
        '''Initialize the flag stack at each human tx/run()'''
        for st in self.manticore.ready_states:
            st.context['written'] = [False]

    def did_run_callback(self):
        '''When  human tx/run just ended remove the states that have not changed
         the storage'''
        with self.manticore.locked_context("ethereum.saved_states", list) as saved_states:
            for state_id in list(saved_states):
                st = self.manticore._load(state_id)
                if not st.context['written'][-1]:
                    if st.id in _ready_states:
                        self._terminated_states.append(st.id)
                        self._ready_states.remove(st.id)
                        saved_states.remove(st.id)

    def generate_testcase(self, state, testcase, message):
        with testcase.open_stream("summary") as stream:
            if not state.context.get("written", (False,))[-1]:
                stream.write("State was removed from ready list because the last tx did not write to the storage")