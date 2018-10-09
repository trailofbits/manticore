import copy
import logging

from .smtlib import solver, Bool
from ..utils.helpers import issymbolic

#import exceptions
from .cpu.abstractcpu import ConcretizeRegister
from .memory import ConcretizeMemory, MemoryException
from ..platforms.platform import *

logger = logging.getLogger(__name__)


class StateException(Exception):
    ''' All state related exceptions '''


class TerminateState(StateException):
    ''' Terminates current state exploration '''

    def __init__(self, message, testcase=False):
        super().__init__(message)
        self.testcase = testcase


class Concretize(StateException):
    ''' Base class for all exceptions that trigger the concretization
        of a symbolic expression

        This will fork the state using a pre-set concretization policy
        Optional `setstate` function set the state to the actual concretized value.
        #Fixme Doc.

    '''
    _ValidPolicies = ['MINMAX', 'ALL', 'SAMPLED', 'ONE']

    def __init__(self, message, expression, setstate=None, policy=None, **kwargs):
        if policy is None:
            policy = 'ALL'
        if policy not in self._ValidPolicies:
            raise Exception("Policy (%s) must be one of: %s" % (policy, ', '.join(self._ValidPolicies),))
        self.expression = expression
        self.setstate = setstate
        self.policy = policy
        self.message = "Concretize: %s (Policy: %s)" % (message, policy)
        super().__init__(**kwargs)


class ForkState(Concretize):
    ''' Specialized concretization class for Bool expressions.
        It tries True and False as concrete solutions. /

        Note: as setstate is None the concrete value is not written back
        to the state. So the expression could still by symbolic(but constrained)
        in forked states.
    '''

    def __init__(self, message, expression, **kwargs):
        assert isinstance(expression, Bool), 'Need a Bool to fork a state in two states'
        super().__init__(message, expression, policy='ALL', **kwargs)


class State(Eventful):

    '''
    Representation of a unique program state/path.

    :param ConstraintSet constraints: Initial constraints
    :param Platform platform: Initial operating system state
    :ivar dict context: Local context for arbitrary data storage
    '''

    _published_events = {'generate_testcase'}

    def __init__(self, constraints, platform, **kwargs):
        super().__init__(**kwargs)
        self._platform = platform
        self._constraints = constraints
        self._platform.constraints = constraints
        self._input_symbols = list()
        self._child = None
        self._context = dict()
        # 33
        # Events are lost in serialization and fork !!
        self.forward_events_from(platform)

        # FIXME(felipe) This should go into some event callback in a plugin (start_run?)
        self._init_context()

    def __getstate__(self):
        state = super().__getstate__()
        state['platform'] = self._platform
        state['constraints'] = self._constraints
        state['input_symbols'] = self._input_symbols
        state['child'] = self._child
        state['context'] = self._context
        return state

    def __setstate__(self, state):
        super().__setstate__(state)
        self._platform = state['platform']
        self._constraints = state['constraints']
        self._input_symbols = state['input_symbols']
        self._child = state['child']
        self._context = state['context']
        # 33
        # Events are lost in serialization and fork !!
        self.forward_events_from(self._platform)

    # Fixme(felipe) change for with "state.cow_copy() as st_temp":.
    # This need to change. this is the center of ALL the problems. re. CoW
    def __enter__(self):
        assert self._child is None
        self._platform.constraints = None
        new_state = State(self._constraints.__enter__(), self._platform)
        self.platform.constraints = new_state.constraints
        new_state._input_symbols = list(self._input_symbols)
        new_state._context = copy.copy(self._context)
        self._child = new_state
        assert new_state.platform.constraints is new_state.constraints

        # fixme NEW State won't inherit signals (pro: added signals to new_state wont affect parent)
        return new_state

    def __exit__(self, ty, value, traceback):
        self._constraints.__exit__(ty, value, traceback)
        self._child = None
        self.platform.constraints = self.constraints

    def execute(self):
        try:
            result = self._platform.execute()

        # Instead of State importing SymbolicRegisterException and SymbolicMemoryException
        # from cpu/memory shouldn't we import Concretize from linux, cpu, memory ??
        # We are forcing State to have abstractcpu
        except ConcretizeRegister as e:
            expression = self.cpu.read_register(e.reg_name)

            def setstate(state, value):
                state.cpu.write_register(setstate.e.reg_name, value)
            setstate.e = e
            raise Concretize(str(e),
                             expression=expression,
                             setstate=setstate,
                             policy=e.policy)
        except ConcretizeMemory as e:
            expression = self.cpu.read_int(e.address, e.size)

            def setstate(state, value):
                state.cpu.write_int(setstate.e.address, value, e.size)
            setstate.e = e
            raise Concretize(str(e),
                             expression=expression,
                             setstate=setstate,
                             policy=e.policy)
        except MemoryException as e:
            raise TerminateState(str(e), testcase=True)

        # Remove when code gets stable?
        assert self.platform.constraints is self.constraints
        return result

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

    def constrain(self, constraint):
        '''Constrain state.

        :param manticore.core.smtlib.Bool constraint: Constraint to add
        '''
        constraint = self.migrate_expression(constraint)
        self._constraints.add(constraint)

    def abandon(self):
        '''Abandon the currently-active state.

        Note: This must be called from the Executor loop, or a :func:`~manticore.Manticore.hook`.
        '''
        raise TerminateState("Abandoned state")

    def new_symbolic_buffer(self, nbytes, **options):
        '''Create and return a symbolic buffer of length `nbytes`. The buffer is
        not written into State's memory; write it to the state's memory to
        introduce it into the program state.

        :param int nbytes: Length of the new buffer
        :param str label: (keyword arg only) The label to assign to the buffer
        :param bool cstring: (keyword arg only) Whether or not to enforce that the buffer is a cstring
                 (i.e. no NULL bytes, except for the last byte). (bool)
        :param taint: Taint identifier of the new buffer
        :type taint: tuple or frozenset

        :return: :class:`~manticore.core.smtlib.expression.Expression` representing the buffer.
        '''
        label = options.get('label')
        avoid_collisions = False
        if label is None:
            label = 'buffer'
            avoid_collisions = True
        taint = options.get('taint', frozenset())
        expr = self._constraints.new_array(name=label, index_max=nbytes, value_bits=8, taint=taint, avoid_collisions=avoid_collisions)
        self._input_symbols.append(expr)

        if options.get('cstring', False):
            for i in range(nbytes - 1):
                self._constraints.add(expr[i] != 0)

        return expr

    def new_symbolic_value(self, nbits, label=None, taint=frozenset()):
        '''Create and return a symbolic value that is `nbits` bits wide. Assign
        the value to a register or write it into the address space to introduce
        it into the program state.

        :param int nbits: The bitwidth of the value returned
        :param str label: The label to assign to the value
        :param taint: Taint identifier of this value
        :type taint: tuple or frozenset
        :return: :class:`~manticore.core.smtlib.expression.Expression` representing the value
        '''
        assert nbits in (1, 4, 8, 16, 32, 64, 128, 256)
        avoid_collisions = False
        if label is None:
            label = 'val'
            avoid_collisions = True

        expr = self._constraints.new_bitvec(nbits, name=label, taint=taint, avoid_collisions=avoid_collisions)
        self._input_symbols.append(expr)
        return expr

    def concretize(self, symbolic, policy, maxcount=7):
        ''' This finds a set of solutions for symbolic using policy.
            This raises TooManySolutions if more solutions than maxcount
        '''
        assert self.constraints == self.platform.constraints
        vals = []
        if policy == 'MINMAX':
            vals = self._solver.minmax(self._constraints, symbolic)
        elif policy == 'MAX':
            vals = self._solver.max(self._constraints, symbolic)
        elif policy == 'MIN':
            vals = self._solver.min(self._constraints, symbolic)
        elif policy == 'SAMPLED':
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
                vals += self._solver.get_all_values(self._constraints, symbolic,
                                                    maxcnt=maxcount - len(vals), silent=True)
        elif policy == 'ONE':
            vals = [self._solver.get_value(self._constraints, symbolic)]
        else:
            assert policy == 'ALL'
            vals = solver.get_all_values(self._constraints, symbolic, maxcnt=maxcount, silent=True)

        return tuple(set(vals))

    @property
    def _solver(self):
        from .smtlib import solver
        return solver

    def migrate_expression(self, expression):
        if not issymbolic(expression):
            return expression
        migration_map = self.context.get('migration_map')
        if migration_map is None:
            migration_map = {}
        migrated_expression = self.constraints.migrate(expression, name_migration_map=migration_map)
        self.context['migration_map'] = migration_map
        return migrated_expression

    def is_feasible(self):
        return self.can_be_true(True)

    def can_be_true(self, expr):
        expr = self.migrate_expression(expr)
        return self._solver.can_be_true(self._constraints, expr)

    def must_be_true(self, expr):
        expr = self.migrate_expression(expr)
        return not self._solver.can_be_true(self._constraints, expr == False)

    def solve_one(self, expr, constrain=False):
        '''
        Concretize a symbolic :class:`~manticore.core.smtlib.expression.Expression` into
        one solution.

        :param manticore.core.smtlib.Expression expr: Symbolic value to concretize
        :param bool constrain: If True, constrain expr to concretized value
        :return: Concrete value
        :rtype: int
        '''
        expr = self.migrate_expression(expr)
        value = self._solver.get_value(self._constraints, expr)
        if constrain:
            self.constrain(expr == value)
        #Include forgiveness here
        if isinstance(value, bytearray):
            value = bytes(value)
        return value

    def solve_n(self, expr, nsolves):
        '''
        Concretize a symbolic :class:`~manticore.core.smtlib.expression.Expression` into
        `nsolves` solutions.

        :param manticore.core.smtlib.Expression expr: Symbolic value to concretize
        :return: Concrete value
        :rtype: list[int]
        '''
        expr = self.migrate_expression(expr)
        return self._solver.get_all_values(self._constraints, expr, nsolves, silent=True)

    def solve_max(self, expr):
        '''
        Solves a symbolic :class:`~manticore.core.smtlib.expression.Expression` into
        its maximum solution

        :param manticore.core.smtlib.Expression expr: Symbolic value to solve
        :return: Concrete value
        :rtype: list[int]
        '''
        if isinstance(expr, int):
            return expr
        expr = self.migrate_expression(expr)
        return self._solver.max(self._constraints, expr)

    def solve_min(self, expr):
        '''
        Solves a symbolic :class:`~manticore.core.smtlib.expression.Expression` into
        its minimum solution

        :param manticore.core.smtlib.Expression expr: Symbolic value to solve
        :return: Concrete value
        :rtype: list[int]
        '''
        if isinstance(expr, int):
            return expr
        expr = self.migrate_expression(expr)
        return self._solver.min(self._constraints, expr)

    ################################################################################################
    # The following should be moved to specific class StatePosix?
    def solve_buffer(self, addr, nbytes, constrain=False):
        '''
        Reads `nbytes` of symbolic data from a buffer in memory at `addr` and attempts to
        concretize it

        :param int address: Address of buffer to concretize
        :param int nbytes: Size of buffer to concretize
        :param bool constrain: If True, constrain the buffer to the concretized value
        :return: Concrete contents of buffer
        :rtype: list[int]
        '''
        buffer = self.cpu.read_bytes(addr, nbytes)
        result = []
        with self._constraints as temp_cs:
            cs_to_use = self.constraints if constrain else temp_cs
            for c in buffer:
                result.append(self._solver.get_value(cs_to_use, c))
                cs_to_use.add(c == result[-1])
        return result

    def invoke_model(self, model):
        '''
        Invoke a `model`. A `model` is a callable whose first argument is a
        :class:`~manticore.core.state.State`. If the `model` models a normal (non-variadic)
        function, the following arguments correspond to the arguments of the C function
        being modeled. If the `model` models a variadic function, the following argument
        is a generator object, which can be used to access function arguments dynamically.
        The `model` callable should simply return the value that should be returned by the
        native function being modeled.

        :param callable model: Model to invoke
        '''
        self._platform.invoke_model(model, prefix_args=(self,))

    def symbolicate_buffer(self, data, label='INPUT', wildcard='+', string=False, taint=frozenset()):
        '''Mark parts of a buffer as symbolic (demarked by the wildcard byte)

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
        '''
        if wildcard in data:
            size = len(data)
            symb = self._constraints.new_array(name=label, index_max=size, taint=taint, avoid_collisions=True)
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

    @property
    def cpu(self):
        return self._platform.current

    @property
    def mem(self):
        return self._platform.current.memory

    # FIXME(felipe) Remove this
    def _init_context(self):
        self.context['branches'] = dict()

    # FIXME(felipe) Remove this
    def record_branch(self, target):
        branches = self.context['branches']
        branch = (self.cpu._last_pc, target)
        if branch in branches:
            branches[branch] += 1
        else:
            branches[branch] = 1

    def generate_testcase(self, name, message='State generated testcase'):
        """
        Generate a testcase for this state and place in the analysis workspace.

        :param str name: Short string identifying this testcase used to prefix workspace entries.
        :param str message: Longer description
        """
        self._publish('will_generate_testcase', name, message)
