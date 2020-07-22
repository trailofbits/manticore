import logging
from contextlib import contextmanager
import cProfile
import pstats
import threading
from functools import wraps

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
    def name(self):
        return str(self.__class__)

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
        """ Called so the plugin can attach some results to the testcase if the
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

    def will_start_run_callback(self, state):
        """ Called once at the beginning of the run.
            state is the initial root state
        """
        logger.info("will_start_run")

    def did_run_callback(self):
        logger.info("did_run")

    def will_fork_state_callback(self, parent_state, expression, solutions, policy):
        logger.info("will_fork_state %r %r %r %r", parent_state, expression, solutions, policy)

    def did_fork_state_callback(self, child_state, expression, new_value, policy):
        logger.info("did_fork_state %r %r %r %r", child_state, expression, new_value, policy)

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
