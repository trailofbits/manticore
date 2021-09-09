import copy
import logging

from typing import List, Tuple, Sequence

from .smtlib import solver, Bool, issymbolic, BitVecConstant
from .smtlib.expression import Expression
from ..utils.event import Eventful
from ..utils.helpers import PickleSerializer
from ..utils import config
from .plugin import StateDescriptor

consts = config.get_group("core")
consts.add(
    "execs_per_intermittent_cb",
    default=1000,
    description="How often to fire the `exec_intermittent` event",
)

logger = logging.getLogger(__name__)


class StateException(Exception):
    """ All state related exceptions """


class TerminateState(StateException):
    """ Terminates current state exploration """

    def __init__(self, message, testcase=False):
        super().__init__(message)
        self.testcase = testcase


class AbandonState(TerminateState):
    """Exception returned for abandoned states when
    execution is finished
    """

    def __init__(self, message="Abandoned state"):
        super().__init__(message)


class Concretize(StateException):
    """Base class for all exceptions that trigger the concretization
    of a symbolic expression

    This will fork the state using a pre-set concretization policy
    Optional `setstate` function set the state to the actual concretized value.
    #Fixme Doc.

    """

    _ValidPolicies = ["MIN", "MAX", "MINMAX", "ALL", "SAMPLED", "ONE", "PESSIMISTIC", "OPTIMISTIC"]

    def __init__(self, message, expression, setstate=None, policy=None, **kwargs):
        if policy is None:
            policy = "ALL"
        if policy not in self._ValidPolicies:
            raise StateException(
                f'Policy ({policy}) must be one of: {", ".join(self._ValidPolicies)}'
            )
        self.expression = expression
        self.setstate = setstate
        self.policy = policy
        self.message = f"Concretize: {message} (Policy: {policy})"
        super().__init__(**kwargs)


class SerializeState(Concretize):
    """Allows the user to save a copy of the current state somewhere on the
    disk so that analysis can later be resumed from this point.
    """

    def _setstate(self, state, _value):
        with open(self.filename, "wb") as statef:
            PickleSerializer().serialize(state, statef)

    def __init__(self, filename, **kwargs):
        super().__init__(
            f"Saving state to {filename}",
            BitVecConstant(size=32, value=0),
            setstate=self._setstate,
            policy="ONE",
            **kwargs,
        )
        self.filename = filename


class ForkState(Concretize):
    """Specialized concretization class for Bool expressions.
    It tries True and False as concrete solutions. /

    Note: as setstate is None the concrete value is not written back
    to the state. So the expression could still by symbolic(but constrained)
    in forked states.
    """

    def __init__(self, message, expression: Bool, **kwargs):
        assert isinstance(expression, Bool), "Need a Bool to fork a state in two states"
        super().__init__(message, expression, policy="ALL", **kwargs)


class EventSolver(Eventful):
    """
    Wrapper around the solver that raises `will_solve` and `did_solve` around every call. Each call expands to:
    ```
    def method_name(self, constraints, expression, *args, **kwargs):
        self._publish("will_solve", constraints, expression, "method_name")
        solved = SelectedSolver.instance().method_name(constraints, expression, *args, **kwargs)
        self._publish("did_solve", constraints, expression, "method_name", solved)
        return solved
    ```
    """

    _published_events = {"solve"}

    @property
    def _solver(self):
        from .smtlib import SelectedSolver

        return SelectedSolver.instance()  # solver

    def can_be_true(self, constraints, expression, *args, **kwargs):
        self._publish("will_solve", constraints, expression, "can_be_true")
        solved = self._solver.can_be_true(constraints, expression, *args, **kwargs)
        self._publish("did_solve", constraints, expression, "can_be_true", solved)
        return solved

    def get_all_values(self, constraints, expression, *args, **kwargs):
        self._publish("will_solve", constraints, expression, "get_all_values")
        solved = self._solver.get_all_values(constraints, expression, *args, **kwargs)
        self._publish("did_solve", constraints, expression, "get_all_values", solved)
        return solved

    def get_value(self, constraints, expression, *args, **kwargs):
        self._publish("will_solve", constraints, expression, "get_value")
        solved = self._solver.get_value(constraints, expression, *args, **kwargs)
        self._publish("did_solve", constraints, expression, "get_value", solved)
        return solved

    def max(self, constraints, expression, *args, **kwargs):
        self._publish("will_solve", constraints, expression, "max")
        solved = self._solver.max(constraints, expression, *args, **kwargs)
        self._publish("did_solve", constraints, expression, "max", solved)
        return solved

    def min(self, constraints, expression, *args, **kwargs):
        self._publish("will_solve", constraints, expression, "min")
        solved = self._solver.min(constraints, expression, *args, **kwargs)
        self._publish("did_solve", constraints, expression, "min", solved)
        return solved

    def minmax(self, constraints, expression, *args, **kwargs):
        self._publish("will_solve", constraints, expression, "minmax")
        solved = self._solver.minmax(constraints, expression, *args, **kwargs)
        self._publish("did_solve", constraints, expression, "minmax", solved)
        return solved

    def __getattr__(self, item: str):
        """
        Pass through any undefined attribute lookups to the underlying solver
        :param item: The name of the field to get
        :return: The item, if present on self._solver
        """
        return getattr(self._solver, item)


class StateBase(Eventful):
    """
    Representation of a unique program state/path.

    :param ConstraintSet constraints: Initial constraints
    :param Platform platform: Initial operating system state
    :ivar dict context: Local context for arbitrary data storage
    """

    _published_events = {"execution_intermittent"}

    def __init__(self, constraints, platform, **kwargs):
        super().__init__(**kwargs)
        self.manticore = None
        self._platform = platform
        self._constraints = constraints
        self._platform.constraints = constraints
        self._input_symbols = list()
        self._child = None
        self._context = dict()
        self._terminated_by = None
        self._solver = EventSolver()
        self._total_exec = 0
        self._own_exec = 0
        # 33
        # Events are lost in serialization and fork !!
        self.forward_events_from(self._solver)
        self.forward_events_from(platform)

    def __getstate__(self):
        state = super().__getstate__()
        state["platform"] = self._platform
        state["constraints"] = self._constraints
        state["input_symbols"] = self._input_symbols
        state["child"] = self._child
        state["context"] = self._context
        state["terminated_by"] = self._terminated_by
        state["exec_counter"] = self._total_exec
        return state

    def __setstate__(self, state):
        super().__setstate__(state)
        self._platform = state["platform"]
        self._constraints = state["constraints"]
        self._input_symbols = state["input_symbols"]
        self._child = state["child"]
        self._context = state["context"]
        self._terminated_by = state["terminated_by"]
        self._total_exec = state["exec_counter"]
        self._own_exec = 0
        self._solver = EventSolver()
        # 33
        # Events are lost in serialization and fork !!
        self.forward_events_from(self._solver)
        self.forward_events_from(self._platform)

    @property
    def id(self):
        return getattr(self, "_id", None)

    def __repr__(self):
        return f"<State object with id {self.id}>"

    # Fixme(felipe) change for with "state.cow_copy() as st_temp":.
    # This need to change. this is the center of ALL the problems. re. CoW
    def __enter__(self):
        assert self._child is None
        self._platform.constraints = None
        new_state = self.__class__(self._constraints.__enter__(), self._platform)
        self.platform.constraints = new_state.constraints
        new_state._input_symbols = list(self._input_symbols)
        new_state._context = copy.copy(self._context)
        new_state._id = None
        new_state.manticore = self.manticore
        new_state._total_exec = self._total_exec
        self.copy_eventful_state(new_state)

        self._child = new_state
        assert new_state.platform.constraints is new_state.constraints

        return new_state

    def __exit__(self, ty, value, traceback):
        self._constraints.__exit__(ty, value, traceback)
        self._child = None
        self.platform.constraints = self.constraints

    @property
    def input_symbols(self):
        return self._input_symbols

    @property
    def context(self):
        return self._context

    @property
    def platform(self):
        return self._platform

    @property
    def constraints(self):
        return self._constraints

    @constraints.setter
    def constraints(self, constraints):
        self._constraints = constraints
        self.platform.constraints = constraints

    def _update_state_descriptor(self, descriptor: StateDescriptor, *args, **kwargs):
        """
        Called on execution_intermittent to update the descriptor for this state. This is intended for information
        like the PC or instruction count, where updating after each instruction would be a waste of cycles.
        This one updates the execution counts

        :param descriptor: StateDescriptor for this state
        """
        descriptor.total_execs = self._total_exec
        descriptor.own_execs = self._own_exec

    def execute(self):
        self._total_exec += 1
        self._own_exec += 1

        if self._total_exec % consts.execs_per_intermittent_cb == 0:
            self._publish("on_execution_intermittent", self._update_state_descriptor)

    def constrain(self, constraint):
        """Constrain state.

        :param manticore.core.smtlib.Bool constraint: Constraint to add
        """
        constraint = self.migrate_expression(constraint)
        self._constraints.add(constraint)

    def abandon(self):
        """Abandon the currently-active state.

        Note: This must be called from the Executor loop, or a :func:`~manticore.Manticore.hook`.
        """
        raise AbandonState

    def new_symbolic_buffer(self, nbytes, **options):
        """Create and return a symbolic buffer of length `nbytes`. The buffer is
        not written into State's memory; write it to the state's memory to
        introduce it into the program state.

        :param int nbytes: Length of the new buffer
        :param str label: (keyword arg only) The label to assign to the buffer
        :param bool cstring: (keyword arg only) Whether or not to enforce that the buffer is a cstring
                 (i.e. no NULL bytes, except for the last byte). (bool)
        :param taint: Taint identifier of the new buffer
        :type taint: tuple or frozenset

        :return: :class:`~manticore.core.smtlib.expression.Expression` representing the buffer.
        """
        label = options.get("label")
        avoid_collisions = False
        if label is None:
            label = "buffer"
            avoid_collisions = True
        taint = options.get("taint", frozenset())
        expr = self._constraints.new_array(
            name=label,
            index_max=nbytes,
            value_bits=8,
            taint=taint,
            avoid_collisions=avoid_collisions,
        )
        self._input_symbols.append(expr)

        if options.get("cstring", False):
            for i in range(nbytes - 1):
                self._constraints.add(expr[i] != 0)

        return expr

    def new_symbolic_value(self, nbits, label=None, taint=frozenset()):
        """Create and return a symbolic value that is `nbits` bits wide. Assign
        the value to a register or write it into the address space to introduce
        it into the program state.

        :param int nbits: The bitwidth of the value returned
        :param str label: The label to assign to the value
        :param taint: Taint identifier of this value
        :type taint: tuple or frozenset
        :return: :class:`~manticore.core.smtlib.expression.Expression` representing the value
        """
        assert nbits in (1, 4, 8, 16, 32, 64, 128, 256)
        avoid_collisions = False
        if label is None:
            label = "val"
            avoid_collisions = True

        expr = self._constraints.new_bitvec(
            nbits, name=label, taint=taint, avoid_collisions=avoid_collisions
        )
        self._input_symbols.append(expr)
        return expr

    def concretize(self, symbolic, policy, maxcount=7):
        """This finds a set of solutions for symbolic using policy.

        This limits the number of solutions returned to `maxcount` to avoid
        a blowup in the state space. **This means that if there are more
        than `maxcount` feasible solutions, some states will be silently
        ignored.**
        """
        assert self.constraints == self.platform.constraints
        symbolic = self.migrate_expression(symbolic)

        vals = []
        if policy == "MINMAX":
            vals = self._solver.minmax(self._constraints, symbolic)
        elif policy == "MAX":
            vals = (self._solver.max(self._constraints, symbolic),)
        elif policy == "MIN":
            vals = (self._solver.min(self._constraints, symbolic),)
        elif policy == "SAMPLED":
            m, M = self._solver.minmax(self._constraints, symbolic)
            vals += [m, M]
            if M - m > 3:
                if self._solver.can_be_true(self._constraints, symbolic == (m + M) // 2):
                    vals.append((m + M) // 2)
            if M - m > 100:
                for i in (0, 1, 2, 5, 32, 64, 128, 320):
                    if self._solver.can_be_true(self._constraints, symbolic == m + i):
                        vals.append(m + i)
                    if maxcount <= len(vals):
                        break
            if M - m > 1000 and maxcount > len(vals):
                vals += self._solver.get_all_values(
                    self._constraints, symbolic, maxcnt=maxcount - len(vals), silent=True
                )
        elif policy == "ONE":
            vals = [self._solver.get_value(self._constraints, symbolic)]
        elif policy == "OPTIMISTIC":
            logger.info("Optimistic case when forking")
            if self._solver.can_be_true(self._constraints, symbolic):
                vals = (True,)
            else:
                # We assume the path constraint was feasible to begin with
                vals = (False,)
        elif policy == "PESSIMISTIC":
            logger.info("Pessimistic case when forking")
            if self._solver.can_be_true(self._constraints, symbolic == False):
                vals = (False,)
            else:
                # We assume the path constraint was feasible to begin with
                vals = (True,)
        else:
            assert policy == "ALL"
            vals = self._solver.get_all_values(
                self._constraints, symbolic, maxcnt=maxcount, silent=True
            )

        return tuple(set(vals))

    def migrate_expression(self, expression):
        if not issymbolic(expression):
            return expression
        migration_map = self.context.get("migration_map")
        if migration_map is None:
            migration_map = {}
        migrated_expression = self.constraints.migrate(expression, name_migration_map=migration_map)
        self.context["migration_map"] = migration_map
        return migrated_expression

    def is_feasible(self):
        return self.can_be_true(True)

    def can_be_true(self, expr):
        expr = self.migrate_expression(expr)
        return self._solver.can_be_true(self._constraints, expr)

    def can_be_false(self, expr):
        expr = self.migrate_expression(expr)
        return self._solver.can_be_true(self._constraints, expr == False)

    def must_be_true(self, expr):
        expr = self.migrate_expression(expr)
        return self._solver.can_be_true(self._constraints, expr) and not self._solver.can_be_true(
            self._constraints, expr == False
        )

    def solve_one(self, expr, constrain=False):
        """
        A version of solver_one_n for a single expression. See solve_one_n.
        """
        return self.solve_one_n(expr, constrain=constrain)[0]

    def solve_one_n(self, *exprs: Expression, constrain: bool = False) -> List[int]:
        """
        Concretize a list of symbolic :class:`~manticore.core.smtlib.expression.Expression` into
        a list of solutions.

        :param exprs: An iterable of manticore.core.smtlib.Expression
        :param bool constrain: If True, constrain expr to solved solution value
        :return: List of concrete value or a tuple of concrete values
        """
        return self.solve_one_n_batched(exprs, constrain)

    def solve_one_n_batched(
        self, exprs: Sequence[Expression], constrain: bool = False
    ) -> List[int]:
        """
        Concretize a list of symbolic :class:`~manticore.core.smtlib.expression.Expression` into
        a list of solutions.
        :param exprs: An iterable of manticore.core.smtlib.Expression
        :param bool constrain: If True, constrain expr to solved solution value
        :return: List of concrete value or a tuple of concrete values
        """
        # Return ret instead of value, to allow the bytearray/bytes conversion
        ret = []
        exprs = [self.migrate_expression(x) for x in exprs]
        values = self._solver.get_value_in_batch(self._constraints, exprs)
        assert len(values) == len(exprs)
        for idx, expr in enumerate(exprs):
            value = values[idx]
            if constrain:
                self.constrain(expr == values[idx])
            # Include forgiveness here
            if isinstance(value, bytearray):
                value = bytes(value)
            ret.append(value)
        return ret

    def solve_n(self, expr, nsolves):
        """
        Concretize a symbolic :class:`~manticore.core.smtlib.expression.Expression` into
        `nsolves` solutions.

        :param manticore.core.smtlib.Expression expr: Symbolic value to concretize
        :return: Concrete value
        :rtype: list[int]
        """
        expr = self.migrate_expression(expr)
        return self._solver.get_all_values(self._constraints, expr, nsolves, silent=True)

    def solve_max(self, expr):
        """
        Solves a symbolic :class:`~manticore.core.smtlib.expression.Expression` into
        its maximum solution

        :param manticore.core.smtlib.Expression expr: Symbolic value to solve
        :return: Concrete value
        :rtype: list[int]
        """
        if isinstance(expr, int):
            return expr
        expr = self.migrate_expression(expr)
        return self._solver.max(self._constraints, expr)

    def solve_min(self, expr):
        """
        Solves a symbolic :class:`~manticore.core.smtlib.expression.Expression` into
        its minimum solution

        :param manticore.core.smtlib.Expression expr: Symbolic value to solve
        :return: Concrete value
        :rtype: list[int]
        """
        if isinstance(expr, int):
            return expr
        expr = self.migrate_expression(expr)
        return self._solver.min(self._constraints, expr)

    def solve_minmax(self, expr):
        """
        Solves a symbolic :class:`~manticore.core.smtlib.expression.Expression` into
        its minimum and maximun solution. Only defined for bitvects.

        :param manticore.core.smtlib.Expression expr: Symbolic value to solve
        :return: Concrete value
        :rtype: list[int]
        """
        if isinstance(expr, int):
            return expr
        expr = self.migrate_expression(expr)
        return self._solver.minmax(self._constraints, expr)

    ################################################################################################
    # The following should be moved to specific class StatePosix?

    def solve_buffer(self, addr, nbytes, constrain=False):
        """
        Reads `nbytes` of symbolic data from a buffer in memory at `addr` and attempts to
        concretize it

        :param int address: Address of buffer to concretize
        :param int nbytes: Size of buffer to concretize
        :param bool constrain: If True, constrain the buffer to the concretized value
        :return: Concrete contents of buffer
        :rtype: list[int]
        """
        buffer = self.cpu.read_bytes(addr, nbytes)
        result = []
        with self._constraints as temp_cs:
            cs_to_use = self.constraints if constrain else temp_cs
            for c in buffer:
                result.append(self._solver.get_value(cs_to_use, c))
                cs_to_use.add(c == result[-1])
        return result

    def symbolicate_buffer(
        self, data, label="INPUT", wildcard="+", string=False, taint=frozenset()
    ):
        """Mark parts of a buffer as symbolic (demarked by the wildcard byte)

        :param str data: The string to symbolicate. If no wildcard bytes are provided,
                this is the identity function on the first argument.
        :param str label: The label to assign to the value
        :param str wildcard: The byte that is considered a wildcard
        :param bool string: Ensure bytes returned can not be NULL
        :param taint: Taint identifier of the symbolicated data
        :type taint: tuple or frozenset

        :return: If data does not contain any wildcard bytes, data itself. Otherwise,
            a list of values derived from data. Non-wildcard bytes are kept as
            is, wildcard bytes are replaced by Expression objects.
        """
        if wildcard in data:
            size = len(data)
            symb = self._constraints.new_array(
                name=label, index_max=size, taint=taint, avoid_collisions=True
            )
            self._input_symbols.append(symb)

            tmp = []
            for i in range(size):
                if data[i] == wildcard:
                    tmp.append(symb[i])
                else:
                    tmp.append(data[i])

            data = tmp

        if string:
            for b in data:
                if issymbolic(b):
                    self._constraints.add(b != 0)
                else:
                    assert b != 0
        return data
