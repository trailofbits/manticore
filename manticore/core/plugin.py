import logging
from contextlib import contextmanager
import cProfile
import pstats
import threading
import typing
from functools import wraps
from dataclasses import dataclass, field
from ..utils.enums import StateLists, StateStatus
from datetime import datetime

from .smtlib import issymbolic

logger = logging.getLogger(__name__)


class DecorateAllMeta(type):
    @staticmethod
    def _if_enabled(f):
        """ decorator used to guard callbacks """

        @wraps(f)
        def g(self, *args, **kwargs):
            if self.is_enabled():
                return f(self, *args, **kwargs)

        return g

    def __new__(cls, name, bases, local):
        for attr in local:
            value = local[attr]
            if attr.endswith("_callback") and callable(value):
                local[attr] = cls._if_enabled(value)
        return type.__new__(cls, name, bases, local)


class Plugin(metaclass=DecorateAllMeta):
    __slots__ = ("manticore", "_enabled_key", "_plugin_context_name")

    def __init__(self):
        self.manticore = None
        classname = str(type(self)).split("'")[1]
        self._enabled_key = f"{classname}_enabled_{hex(hash(self))}"
        self._plugin_context_name = f"{classname}_context_{hex(hash(self))}"

    def enable(self):
        """ Enable all callbacks """
        with self.manticore.locked_context() as context:
            context[self._enabled_key] = True

    def disable(self):
        """ Disable all callbacks """
        with self.manticore.locked_context() as context:
            context[self._enabled_key] = False

    def is_enabled(self):
        """ True if callbacks are enabled """
        with self.manticore.locked_context() as context:
            return context.get(self._enabled_key, True)

    @property
    def name(self) -> str:
        return str(self.__class__)

    @property
    def unique_name(self) -> str:
        return f"{self.name}_{id(self)}"

    @contextmanager
    def locked_context(self, key=None, value_type=list):
        """
        A context manager that provides safe parallel access to the global Manticore context.
        This should be used to access the global Manticore context
        when parallel analysis is activated. Code within the `with` block is executed
        atomically, so access of shared variables should occur within.
        """
        plugin_context_name = self._plugin_context_name
        with self.manticore.locked_context(plugin_context_name, dict) as context:
            if key is None:
                yield context
            else:
                ctx = context.get(key, value_type())
                yield ctx
                context[key] = ctx

    @property
    def context(self):
        """ Convenient access to shared context """
        plugin_context_name = self._plugin_context_name
        if plugin_context_name not in self.manticore.context:
            self.manticore.context[plugin_context_name] = {}
        return self.manticore.context[plugin_context_name]

    def on_register(self):
        """ Called by parent manticore on registration """
        pass

    def on_unregister(self):
        """ Called be parent manticore on un-registration """
        pass

    def generate_testcase(self, state, testcase, message):
        """Called so the plugin can attach some results to the testcase if the
        state needs it"""
        pass


def _dict_diff(d1, d2):
    """
    Produce a dict that includes all the keys in d2 that represent different values in d1, as well as values that
    aren't in d1.

    :param dict d1: First dict
    :param dict d2: Dict to compare with
    :rtype: dict
    """
    d = {}
    for key in set(d1).intersection(set(d2)):
        if d2[key] != d1[key]:
            d[key] = d2[key]
    for key in set(d2).difference(set(d1)):
        d[key] = d2[key]
    return d


class Tracer(Plugin):
    def did_execute_instruction_callback(self, state, pc, target_pc, instruction):
        state.context.setdefault("trace", []).append(pc)


class ExtendedTracer(Plugin):
    def __init__(self):
        """
        Record a detailed execution trace
        """
        super().__init__()
        self.last_dict = {}
        self.current_pc = None
        self.context_key = "e_trace"

    def get_trace(self, state):
        return state.context.get(self.context_key)

    def register_state_to_dict(self, cpu):
        d = {}
        for reg in cpu.canonical_registers:
            val = cpu.read_register(reg)
            d[reg] = val if not issymbolic(val) else "<sym>"
        return d

    def will_execute_instruction_callback(self, state, pc, instruction):
        self.current_pc = pc

    def did_execute_instruction_callback(self, state, pc, target_pc, instruction):
        reg_state = self.register_state_to_dict(state.cpu)
        entry = {"type": "regs", "values": _dict_diff(self.last_dict, reg_state)}
        self.last_dict = reg_state
        state.context.setdefault(self.context_key, []).append(entry)

    def will_read_memory_callback(self, state, where, size):
        if self.current_pc == where:
            return

    def did_read_memory_callback(self, state, where, value, size):
        if self.current_pc == where:
            return

    def will_write_memory_callback(self, state, where, value, size):
        if self.current_pc == where:
            return

    def did_write_memory_callback(self, state, where, value, size):
        if self.current_pc == where:
            raise Exception

        entry = {"type": "mem_write", "where": where, "value": value, "size": size}
        state.context.setdefault(self.context_key, []).append(entry)


class Follower(Plugin):
    def __init__(self, trace):
        self.index = 0
        self.trace = trace
        self.last_instruction = None
        self.symbolic_ranges = []
        self.active = True
        super().__init__()

    def add_symbolic_range(self, pc_start, pc_end):
        self.symbolic_ranges.append((pc_start, pc_end))

    def get_next(self, type):
        event = self.trace[self.index]
        assert event["type"] == type
        self.index += 1
        return event

    def did_write_memory_callback(self, state, where, value, size):
        if not self.active:
            return
        write = self.get_next("mem_write")

        if not issymbolic(value):
            return

        assert write["where"] == where and write["size"] == size
        # state.constrain(value == write['value'])

    def did_execute_instruction_callback(self, state, last_pc, pc, insn):
        if not self.active:
            return
        event = self.get_next("regs")
        self.last_instruction = event["values"]
        if issymbolic(pc):
            state.constrain(state.cpu.RIP == self.last_instruction["RIP"])
        else:
            for start, stop in self.symbolic_ranges:
                if start <= pc <= stop:
                    self.active = False


class RecordSymbolicBranches(Plugin):
    def did_execute_instruction_callback(self, state, last_pc, target_pc, instruction):
        if state.context.get("forking_pc", False):
            branches = state.context.setdefault("branches", {})
            branch = (last_pc, target_pc)
            if branch in branches:
                branches[branch] += 1
            else:
                branches[branch] = 1
            state.context["forking_pc"] = False

        if issymbolic(target_pc):
            state.context["forking_pc"] = True


class InstructionCounter(Plugin):
    def will_terminate_state_callback(self, state, ex):
        if state is None:  # FIXME Can it be None?
            return
        state_instructions_count = state.context.get("instructions_count", 0)

        with self.manticore.locked_context() as manticore_context:
            manticore_instructions_count = manticore_context.get("instructions_count", 0)
            manticore_context["instructions_count"] = (
                manticore_instructions_count + state_instructions_count
            )

    def did_execute_instruction_callback(self, state, prev_pc, target_pc, instruction):
        address = prev_pc
        if not issymbolic(address):
            count = state.context.get("instructions_count", 0)
            state.context["instructions_count"] = count + 1

    def did_run_callback(self):
        _shared_context = self.manticore.context
        instructions_count = _shared_context.get("instructions_count", 0)
        logger.info("Instructions executed: %d", instructions_count)


class Visited(Plugin):
    def __init__(self, coverage_file="visited.txt"):
        super().__init__()
        self.coverage_file = coverage_file

    def will_terminate_state_callback(self, state, ex):
        if state is None:
            return
        state_visited = state.context.get("visited_since_last_fork", set())
        with self.manticore.locked_context() as manticore_context:
            manticore_visited = manticore_context.get("visited", set())
            manticore_context["visited"] = manticore_visited.union(state_visited)

    def will_fork_state_callback(self, state, expression, values, policy):
        state_visited = state.context.get("visited_since_last_fork", set())
        with self.manticore.locked_context() as manticore_context:
            manticore_visited = manticore_context.get("visited", set())
            manticore_context["visited"] = manticore_visited.union(state_visited)
        state.context["visited_since_last_fork"] = set()

    def did_execute_instruction_callback(self, state, prev_pc, target_pc, instruction):
        state.context.setdefault("visited_since_last_fork", set()).add(prev_pc)
        state.context.setdefault("visited", set()).add(prev_pc)

    def did_run_callback(self):
        _shared_context = self.manticore.context
        executor_visited = _shared_context.get("visited", set())
        # Fixme this is duplicated?
        if self.coverage_file is not None:
            with self.manticore._output.save_stream(self.coverage_file) as f:
                for m in executor_visited:
                    f.write(f"0x{m:016x}\n")
        logger.info("Coverage: %d different instructions executed", len(executor_visited))


class Profiler(Plugin):
    data = threading.local()

    def will_start_worker_callback(self, id):
        self.data.profile = cProfile.Profile()
        self.data.profile.enable()

    def did_terminate_worker_callback(self, id):
        self.data.profile.disable()
        self.data.profile.create_stats()
        with self.manticore.locked_context("_profiling_stats", dict) as profiling_stats:
            profiling_stats[id] = self.data.profile.stats.items()

    def did_terminate_execution_callback(self, output):
        with output.save_stream("profiling.bin", binary=True) as f:
            self.save_profiling_data(f)

    def get_profiling_data(self):
        class PstatsFormatted:
            def __init__(self, d):
                self.stats = dict(d)

            def create_stats(self):
                pass

        with self.manticore.locked_context("_profiling_stats") as profiling_stats:
            ps = None
            for item in profiling_stats.values():
                try:
                    stat = PstatsFormatted(item)
                    if ps is None:
                        ps = pstats.Stats(stat)
                    else:
                        ps.add(stat)
                except TypeError:
                    logger.info("Incorrectly formatted profiling information in _stats, skipping")
        return ps

    def save_profiling_data(self, stream=None):
        """:param stream: an output stream to write the profiling data """
        ps = self.get_profiling_data()
        # XXX(yan): pstats does not support dumping to a file stream, only to a file
        # name. Below is essentially the implementation of pstats.dump_stats() without
        # the extra open().
        if stream is not None:
            import marshal

            marshal.dump(ps.stats, stream)


# TODO document all callbacks
class ExamplePlugin(Plugin):
    def will_open_transaction_callback(self, state, tx):
        logger.info("will open a transaction %r %r", state, tx)

    def will_close_transaction_callback(self, state, tx):
        logger.info("will close a transaction %r %r", state, tx)

    def will_decode_instruction_callback(self, state, pc):
        logger.info("will_decode_instruction %r %r", state, pc)

    def will_execute_instruction_callback(self, state, pc, instruction):
        logger.info("will_execute_instruction %r %r %r", state, pc, instruction)

    def did_execute_instruction_callback(self, state, pc, target_pc, instruction):
        logger.info("did_execute_instruction %r %r %r %r", state, pc, target_pc, instruction)

    def will_run_callback(self, state):
        """Called once at the beginning of the run.
        state is the initial root state
        """
        logger.info("will_run")

    def did_run_callback(self):
        logger.info("did_run")

    def will_fork_state_callback(self, parent_state, expression, solutions, policy):
        logger.info("will_fork_state %r %r %r %r", parent_state, expression, solutions, policy)

    def did_fork_state_callback(self, child_state, expression, new_value, policy, children):
        logger.info(
            "did_fork_state %r %r %r %r %r", child_state, expression, new_value, policy, children
        )

    def did_load_state_callback(self, state, state_id):
        logger.info("did_load_state %r %r", state, state_id)

    def did_enqueue_state_callback(self, state, state_id):
        logger.info("did_enqueue_state %r %r", state, state_id)

    def will_terminate_state_callback(self, state, exception):
        logger.info("will_terminate_state %r %r", state, exception)

    def will_generate_testcase_callback(self, state, testcase, message):
        logger.info("will_generate_testcase %r %r %r", state, testcase, message)

    def will_read_memory_callback(self, state, where, size):
        logger.info("will_read_memory %r %r %r", state, where, size)

    def did_read_memory_callback(self, state, where, value, size):
        logger.info("did_read_memory %r %r %r %r", state, where, value, size)

    def will_write_memory_callback(self, state, where, value, size):
        logger.info("will_write_memory %r %r %r", state, where, value, size)

    def did_write_memory_callback(self, state, where, value, size):
        logger.info("did_write_memory %r %r %r %r", state, where, value, size)

    def will_read_register_callback(self, state, register):
        logger.info("will_read_register %r %r", state, register)

    def did_read_register_callback(self, state, register, value):
        logger.info("did_read_register %r %r %r", state, register, value)

    def will_write_register_callback(self, state, register, value):
        logger.info("will_write_register %r %r %r", state, register, value)

    def did_write_register_callback(self, state, register, value):
        logger.info("did_write_register %r %r %r", state, register, value)


@dataclass
class StateDescriptor:
    """
    Dataclass that tracks information about a State.
    """

    #: State ID Number
    state_id: int
    #: Which State List the state currently resides in (or None if it's been removed entirely)
    state_list: typing.Optional[StateLists] = None
    #: State IDs of any states that forked from this one
    children: set = field(default_factory=set)
    #: State ID of zero or one forked state that created this one
    parent: typing.Optional[int] = None
    #: The time that any field of this Descriptor was last updated
    last_update: datetime = field(default_factory=datetime.now)
    #: The time at which the on_execution_intermittent callback was last applied to this state. This is when the PC and exec count get updated.
    last_intermittent_update: typing.Optional[datetime] = None
    #: The time at which this state was created (or first detected, if the did_enque callback didn't fire for some reason)
    created_at: datetime = field(default_factory=datetime.now)
    #: What the state is currently doing (ie waiting for a worker, running, solving, etc.) See enums.StateStatus
    status: StateStatus = StateStatus.waiting_for_worker
    #: The last thing a state was doing. Allows us to swap back to this once it finishes solving.
    _old_status: typing.Optional[StateStatus] = None
    #: Total number of instruction executions in this state, including those in its parents
    total_execs: typing.Optional[int] = None
    #: Number of executions that took place in this state alone, excluding its parents
    own_execs: typing.Optional[int] = None
    #: Last program counter (if set)
    pc: typing.Optional[typing.Any] = None
    #: Last concrete program counter, useful when a state forks and the program counter becomes symbolic
    last_pc: typing.Optional[typing.Any] = None
    #: Dict mapping field names to the time that field was last updated
    field_updated_at: typing.Dict[str, datetime] = field(default_factory=dict)
    #: Message attached to the TerminateState exception that ended this state
    termination_msg: typing.Optional[str] = None

    def __setattr__(self, key, value):
        """
        Force updates the last_updated item any time a field is written to
        """
        if key != "last_update":
            super().__setattr__(key, value)
        now = datetime.now()
        # This calls setattr on the _dict_, so it doesn't cause an infinite loop
        getattr(self, "field_updated_at", {})[key] = now
        super().__setattr__("last_update", now)


class IntrospectionAPIPlugin(Plugin):
    """
    Plugin that tracks the movements of States throughout the State lifecycle. Creates a StateDescriptor for each state
    and stores them in its context, and keeps them up to date whenever a callback registers a change in the State.
    """

    NAME = "introspector"

    @property
    def name(self) -> str:
        return "IntrospectionAPIPlugin"

    def create_state(self, state_id: int):
        """
        Adds a StateDescriptor to the context in the READY state list

        :param state_id: ID of the state
        """
        assert state_id is not None
        with self.locked_context("manticore_state", dict) as context:
            context[state_id] = StateDescriptor(state_id=state_id, state_list=StateLists.ready)

    def will_run_callback(self, ready_states: typing.Generator):
        """
        Called at the beginning of ManticoreBase.run(). Creates a state descriptor for each of the ready states.

        :param ready_states: Generator that allows us to iterate over the ready states (and modify them if necessary)
        """
        for state in ready_states:
            self.create_state(state.id)

    def did_enqueue_state_callback(self, state_id: int):
        """
        Called whenever a state is added to the ready_states list. Creates a state descriptor.

        :param state_id: State ID of the new State
        """
        logger.debug("did_enqueue_state: %s", state_id)
        self.create_state(state_id)

    def did_transition_state_callback(
        self, state_id: int, from_list: StateLists, to_list: StateLists
    ):
        """
        Called whenever a state moves from one state list to another. Updates the status based on which list the state
        has been moved to.

        :param state_id: The ID of the state that was moved
        :param from_list: The list the state used to be in
        :param to_list: The list it's currently in
        """
        logger.debug("did_transition_state %s: %s --> %s", state_id, from_list, to_list)
        with self.locked_context("manticore_state", dict) as context:
            if state_id not in context:
                logger.warning(
                    "Got a state transition event for %s, but failed to capture its initialization",
                    state_id,
                )
            state = context.setdefault(
                state_id, StateDescriptor(state_id=state_id, state_list=from_list)
            )
            if state.state_list != from_list:
                logger.warning(
                    "Callbacks failed to capture state %s transitioning from %s to %s",
                    state_id,
                    state.state_list,
                    from_list,
                )
            state.state_list = to_list
            if to_list == StateLists.ready:
                state.status = StateStatus.waiting_for_worker
            elif to_list == StateLists.busy:
                state.status = StateStatus.running
            elif to_list in {StateLists.terminated, StateLists.killed}:
                state.status = StateStatus.stopped

    def did_remove_state_callback(self, state_id: int):
        """
        Called whenever a state was removed. As in, not terminated, not killed, but removed. This happens when we fork -
        the parent state is removed and the children are enqueued. It can also be triggered manually if we really don't
        like a state for some reason. Doesn't destroy the state descriptor, but updates its status and list accordingly.

        :param state_id: ID of the state that was removed
        """
        logger.debug("did_remove_state: %s", state_id)
        with self.locked_context("manticore_state", dict) as context:
            if state_id not in context:
                logger.warning(
                    "Removing state %s, but failed to capture its initialization", state_id
                )
            else:
                # Wipe the state list to indicate it's been deleted, but keep it around for record-keeping
                desc = context[state_id]
                desc.state_list = None
                desc.status = StateStatus.destroyed

    def did_fork_state_callback(
        self, state, expression, solutions, policy, children: typing.List[int]
    ):
        """
        Called upon each fork. Sets the children for each state.

        :param state: The parent state
        :param expression: The expression we forked on
        :param solutions: Possible values of the expression
        :param policy: The policy used for finding solutions
        :param children: the state IDs of the children
        """
        state_id = state.id
        logger.debug("did_fork_state: %s --> %s", state_id, children)
        with self.locked_context("manticore_state", dict) as context:
            if state_id not in context:
                logger.warning(
                    "Forked state %s, but failed to capture its initialization", state_id
                )
            context.setdefault(state_id, StateDescriptor(state_id=state_id)).children.update(
                children
            )
            for child_id in children:
                context.setdefault(child_id, StateDescriptor(state_id=child_id)).parent = state_id

    def will_solve_callback(self, state, constraints, expr, solv_func: str):
        """
        Called when we're about to ask the solver for something. Updates the status of the state accordingly.

        :param state: State asking for the solve
        :param constraints: Current constraint set used for solving
        :param expr: Expression to be solved
        :param solv_func: Which solver function is being used to find a solution
        """
        if state is None:
            logger.debug("Solve callback fired outside of a state, dropping...")
            return
        with self.locked_context("manticore_state", dict) as context:
            if state.id not in context:
                logger.warning(
                    "Caught will_solve in state %s, but failed to capture its initialization",
                    state.id,
                )
            desc = context.setdefault(state.id, StateDescriptor(state_id=state.id))
            desc._old_status = desc.status
            desc.status = StateStatus.waiting_for_solver

    def did_solve_callback(self, state, constraints, expr, solv_func: str, solutions):
        """
        Called when we've finished solving. Sets the status of the state back to whatever it was.

        :param state: State asking for the solve
        :param constraints: Current constraint set used for solving
        :param expr: Expression to be solved
        :param solv_func: Which solver function is being used to find a solution
        :param solutions: the solved values for expr
        """
        if state is None:
            logger.debug("Solve callback fired outside of a state, dropping...")
            return
        with self.locked_context("manticore_state", dict) as context:
            if state.id not in context:
                logger.warning(
                    "Caught did_solve in state %s, but failed to capture its initialization",
                    state.id,
                )
            desc = context[state.id]
            desc.status = desc._old_status

    def on_execution_intermittent_callback(
        self, state, update_cb: typing.Callable, *args, **kwargs
    ):
        """
        Called every n instructions, where n is config.core.execs_per_intermittent_cb. Calls the provided callback
        to update platform-specific information on the descriptor.

        :param state: The state that raised the intermittent event
        :param update_cb: Callback provided by the caller that will set some platform-specific fields on the state
        descriptor. This could be PC for native, or something else for EVM
        :param args: Optional args to pass to the callback
        :param kwargs: Optional kwargs to pass to the callback
        """
        with self.locked_context("manticore_state", dict) as context:
            if state.id not in context:
                logger.warning(
                    "Caught intermittent callback in state %s, but failed to capture its initialization",
                    state.id,
                )
            update_cb(
                context.setdefault(state.id, StateDescriptor(state_id=state.id)),
                *args,
                **kwargs,
            )
            context[state.id].last_intermittent_update = datetime.now()

    def did_terminate_state_callback(self, state, ex: Exception):
        """
        Capture TerminateState exceptions so we can get the messages attached

        :param state: State that was terminated
        :param ex: The TerminateState exception w/ the termination message
        """
        state_id = state.id
        with self.locked_context("manticore_state", dict) as context:
            if state_id not in context:
                logger.warning(
                    "Caught termination of state %s, but failed to capture its initialization",
                    state_id,
                )
            context.setdefault(state_id, StateDescriptor(state_id=state_id)).termination_msg = str(
                ex
            )

    def get_state_descriptors(self) -> typing.Dict[int, StateDescriptor]:
        """
        :return: the most up-to-date copy of the state descriptor dict available
        """
        with self.locked_context("manticore_state", dict) as context:
            out = context.copy()  # TODO: is this necessary to break out of the lock?
        return out

    def did_kill_state_callback(self, state, ex: Exception):
        """
        Capture other state-killing exceptions so we can get the corresponding message

        :param state: State that was killed
        :param ex: The exception w/ the termination message
        """
        state_id = state.id
        with self.locked_context("manticore_state", dict) as context:
            if state_id not in context:
                logger.warning(
                    "Caught killing of state %s, but failed to capture its initialization",
                    state_id,
                )
            context.setdefault(state_id, StateDescriptor(state_id=state_id)).termination_msg = repr(
                ex
            )

    @property
    def unique_name(self) -> str:
        return IntrospectionAPIPlugin.NAME
