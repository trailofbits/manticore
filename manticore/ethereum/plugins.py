import logging
from functools import reduce

import re

from ..core.plugin import Plugin
from ..core.smtlib import Operators

logger = logging.getLogger(__name__)


class ExamplePlugin(Plugin):
    def on_register(self):
        """Called when manticore.register_plugin(...) is called"""
        pass

    def on_unregister(self):
        """Called when manticore.unregister_plugin(...) is called"""
        pass

    def will_start_run_callback(self, state):
        """
        Called at the beginning of each analysis run
        (so when a contract is created or when it's function is called from a script).

        The `state` argument holds the state before running the given analysis.

        As an example, having contracts:
            contract A { function a(B b) { b.b(); } }
            contract B { function b() {} }

        All of the lines below will end up calling this event exactly once:
            A = manticore.solidity_create_contract(..., contract_name='A')
            B = manticore.solidity_create_contract(..., contract_name='B')
            A.a(B)

        :type state: manticore.ethereum.State
        """
        pass

    def did_finish_run_callback(self):
        """
        Called at the end of each analysis run. For more see `will_start_run_callback`.
        """
        pass

    def will_open_transaction_callback(self, state, tx):
        """
        Called when a transaction is opened.

        So an example for such code:
            contract A { function a(B b) { b.b(); } }
            contract B { function b() {} }

        B.b() opens one transaction while A.a(B) opens two transactions.

        The `tx.is_human` can be used to determine if the transaction has been explicitly called by the user
        (from a manticore script) or if it is an internal transaction (e.g. b.b() called from A.a(B)).

        :type state: manticore.ethereum.State
        :type tx: manticore.ethereum.evm.Transaction
        """
        pass

    def will_close_transaction_callback(self, state, tx):
        """
        Called when a transaction is closed. See also `will_open_transaction_callback`.

        :type state: manticore.ethereum.State
        :type tx: manticore.ethereum.evm.Transaction
        """
        pass

    def will_execute_instruction_callback(self, state, instruction, arguments):
        """
        Called before an instruction is executed.

        The arguments may be symbolic.

        :type state: manticore.ethereum.State
        :type instruction: pyevmasm.Instruction
        :type arguments: list
        """
        pass

    def did_execute_instruction_callback(self, state, last_instruction, last_arguments, result):
        """
        Called after an instruction was executed.

        The last_arguments and result may be symbolic.

        :type state: manticore.ethereum.State
        :type last_instruction: pyevmasm.Instruction
        :type last_arguments: list
        :type result: typing.Union[int, manticore.core.smtlib.expression.Expression]
        """
        pass

    def will_fork_state_callback(self, parent_state, expression, solutions, policy):
        """
        :param expression: expression that we fork on
        :param solutions: tuple of solutions (values) that the state will fork to
        :param policy: fork policy string

        :type parent_state: manticore.ethereum.State
        :type expression: manticore.core.smtlib.expression.Expression
        :type solutions: Any
        :type policy: str
        """
        pass

    def did_fork_state_callback(self, child_state, expression, new_value, policy):
        """

        :type child_state: manticore.ethereum.State
        :type expression: manticore.core.smtlib.expression.
        :type new_value: TODO / FIXME
        :type policy: str
        """
        pass

    def did_enqueue_state_callback(self, state, state_id):
        """
        Called after the state has been enqueued (saved into workspace).

        :type state: manticore.ethereum.State
        :type state_id: int
        """
        pass

    def will_load_state_callback(self, state_id):
        """
        Called before loading a state with given id.

        :type state_id: int
        """
        pass

    def did_load_state_callback(self, state, state_id):
        """
        Called after the state has been loaded.

        :type state: manticore.ethereum.State
        :type state_id: int
        """
        pass

    def will_terminate_state_callback(self, state, state_id, exception):
        """
        Called when a state is terminated. This happens e.g. when:
        * state ended with RETURN instruction
        * during a shutdown (given timeout passed or user cancelled manticore)
        * we entered a state we cannot solve (e.g. no matching keccak256)
        * state tries to execute an unimplemented instruction

        :type state: manticore.ethereum.State
        :type state_id: int
        :type exception: manticore.core.state.TerminateState
        """
        pass

    def will_generate_testcase_callback(self, state, testcase, message):
        """
        Data shared between states should be saved in `self.context` dict.
        Data related to given state should be saved in `state.context` dict.

        :param testcase: let us save additional information about given state to the workspace e.g.:
            with testcase.open_stream('something') as f:
                f.write('some information')
        Will save a file called `state_XXXXXX.something` in the workspace.

        :param message: Message that was sent when generating testcase; usually a result of transaction (e.g. STOP)
        or user defined message.

        :type state: manticore.ethereum.State
        :type testcase: manticore.core.workspace.Testcase
        :type message: str
        """
        pass


class FilterFunctions(Plugin):
    def __init__(self, regexp=r'.*', mutability='both', depth='both', fallback=False, include=True, **kwargs):
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
        if depth not in ('human', 'internal', 'both'):
            raise ValueError
        mutability = mutability.lower()
        if mutability not in ('mutable', 'constant', 'both'):
            raise ValueError

        #fixme better names for member variables
        self._regexp = regexp
        self._mutability = mutability
        self._depth = depth
        self._fallback = fallback
        self._include = include

    def will_open_transaction_callback(self, state, tx):
        world = state.platform
        tx_cnt = len(world.all_transactions)
        # Constrain input only once per tx, per plugin
        if state.context.get('constrained%d' % id(self), 0) != tx_cnt:
            state.context['constrained%d' % id(self)] = tx_cnt

            if self._depth == 'human' and not tx.is_human:
                return
            if self._depth == 'internal' and tx.is_human:
                return

            # Get metadata if any for the target address of current tx
            md = self.manticore.get_metadata(tx.address)
            if md is None:
                return
            # Let's compile  the list of interesting hashes
            selected_functions = []

            for func_hsh in md.function_selectors:
                abi = md.get_abi(func_hsh)
                if abi['type'] == 'fallback':
                    continue
                if self._mutability == 'constant' and not abi.get('constant', False):
                    continue
                if self._mutability == 'mutable' and abi.get('constant', False):
                    continue
                if not re.match(self._regexp, abi['name']):
                    continue
                selected_functions.append(func_hsh)

            if self._fallback and md.has_non_default_fallback_function:
                selected_functions.append(md.fallback_function_selector)

            if self._include:
                # constrain the input so it can take only the interesting values
                constraint = reduce(Operators.OR, (tx.data[:4] == x for x in selected_functions))
                state.constrain(constraint)
            else:
                #Avoid all not selected hashes
                for func_hsh in md.function_selectors:
                    if func_hsh in selected_functions:
                        constraint = tx.data[:4] != func_hsh
                        state.constrain(constraint)


class LoopDepthLimiter(Plugin):
    """This just aborts explorations that are too deep"""

    def __init__(self, loop_count_threshold=5, **kwargs):
        super().__init__(**kwargs)
        self.loop_count_threshold = loop_count_threshold

    def will_start_run_callback(self, *args):
        with self.manticore.locked_context('seen_rep', dict) as reps:
            reps.clear()

    def will_execute_instruction_callback(self, state, pc, insn):
        world = state.platform
        with self.manticore.locked_context('seen_rep', dict) as reps:
            item = (world.current_transaction.sort == 'CREATE', world.current_transaction.address, pc)
            if item not in reps:
                reps[item] = 0
            reps[item] += 1
            if reps[item] > self.loop_count_threshold:
                state.abandon()


class VerboseTrace(Plugin):
    """
    Generates a verbose trace of EVM execution and saves in workspace into `state<id>.verbose_trace`.

    Example output can be seen in test_eth_plugins.
    """

    def will_execute_instruction_callback(self, state, instruction, arguments):
        current_vm = state.platform.current_vm
        state.context.setdefault('str_trace', []).append(str(current_vm))

    def will_generate_testcase_callback(self, state, testcase, message):
        trace = state.context.get('str_trace', [])

        with testcase.open_stream('verbose_trace') as vt:
            for t in trace:
                vt.write(t + '\n')
