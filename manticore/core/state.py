import os
import copy
import logging
from collections import OrderedDict

from .smtlib import solver
from ..utils.helpers import issymbolic
from ..utils.event import Signal, forward_signals


#import exceptions
from .cpu.abstractcpu import ConcretizeRegister
from .memory import ConcretizeMemory, MemoryException
from ..platforms.platform import *

logger = logging.getLogger("STATE")

class StateException(Exception):
    ''' All state related exceptions '''
    pass


class TerminateState(StateException):
    ''' Terminates current state exploration '''
    def __init__(self, message, testcase=False):
        super(TerminateState, self).__init__(message)
        self.testcase = testcase


class Concretize(StateException):
    ''' Base class for all exceptions that trigger the concretization 
        of a symbolic expression

        This will fork the state using a pre-set concretization policy
        Optional `setstate` function set the state to the actual concretized value.
        #Fixme Doc.

    '''
    _ValidPolicies = ['MINMAX', 'ALL', 'SAMPLED', 'ONE']
    def __init__(self, message, expression, setstate=None, policy='ALL',  **kwargs):
        assert policy in self._ValidPolicies, "Policy must be one of: %s"%(', '.join(self._ValidPolicies),)
        self.expression = expression
        self.setstate = setstate
        self.policy = policy
        self.message = "Concretize: %s (Policy: %s)"%(message, policy)
        super(Concretize, self).__init__(**kwargs)


class ForkState(Concretize):
    ''' Specialized concretization class for Bool expressions. 
        It tries True and False as concrete solutions. /

        Note: as setstate is None the concrete value is not written back 
        to the state. So the expression could still by symbolic(but constrained) 
        in forked states.
    '''
    def __init__(self, message, expression, **kwargs):
        assert isinstance(expression, Bool), 'Need a Bool to fork a state in two states'
        super(ForkState, self).__init__(message, expression, policy='ALL', **kwargs)


from ..utils.event import Signal


class State(object):
    '''
    Representation of a unique program state/path.

    :param ConstraintSet constraints: Initial constraints 
    :param Platform platform: Initial operating system state
    :ivar dict context: Local context for arbitrary data storage
    '''

    def __init__(self, constraints, platform):
        self.platform = platform
        self.forks = 0
        self.constraints = constraints
        self.platform.constraints = constraints

        self.input_symbols = list()
        self._child = None

        self.context = dict()
        ##################################################################33
        # Signals are lost in serialization and fork !!
        #self.will_add_constraint = Signal()

        #Import all signals from platform
        forward_signals(self, platform)

    def __reduce__(self):
        return (self.__class__, (self.constraints, self.platform),
                {'context': self.context, '_child': self._child, 'input_symbols': self.input_symbols})

    @staticmethod
    def state_count():
        return State._state_count.value

    @property
    def cpu(self):
        return self.platform.current

    @property
    def mem(self):
        return self.platform.current.memory

    def __enter__(self):
        assert self._child is None
        new_state = State(self.constraints.__enter__(), self.platform)
        new_state.input_symbols = self.input_symbols
        new_state.context = copy.deepcopy(self.context)
        self._child = new_state
        
        #fixme NEW State won't inherit signals (pro: added signals to new_state wont affect parent)
        return new_state

    def __exit__(self, ty, value, traceback):
        self.constraints.__exit__(ty, value, traceback)
        self._child = None

    def execute(self):
        try:
            result = self.platform.execute()

        #Instead of State importing SymbolicRegisterException and SymbolicMemoryException 
        # from cpu/memory shouldn't we import Concretize from linux, cpu, memory ?? 
        # We are forcing State to have abstractcpu
        except ConcretizeRegister as e:
            expression = self.cpu.read_register(e.reg_name)
            def setstate(state, value):
                state.cpu.write_register(e.reg_name, value)
            raise Concretize(e.message,
                                expression=expression, 
                                setstate=setstate,
                                policy=e.policy)
        except ConcretizeMemory as e:
            expression = self.cpu.read_int(e.address, e.size)
            def setstate(state, value):
                state.cpu.write_int(e.reg_name, value, e.size)
            raise Concretize(e.message,
                                expression=expression, 
                                setstate=setstate,
                                policy=e.policy)
        except MemoryException as e:
            raise TerminateState(e.message, testcase=True)

        #Remove when code gets stable?
        assert self.platform.constraints is self.constraints
        assert self.mem.constraints is self.constraints
        return result

    def constrain(self, constraint):
        '''Constrain state.

        :param manticore.core.smtlib.Bool constraint: Constraint to add
        '''
        self.constraints.add(constraint)

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
        :param str name: (keyword arg only) The name to assign to the buffer
        :param bool cstring: (keyword arg only) Whether or not to enforce that the buffer is a cstring
                 (i.e. no \0 bytes, except for the last byte). (bool)

        :return: :class:`~manticore.core.smtlib.expression.Expression` representing the buffer.
        '''
        name = options.get('name', 'buffer')
        expr = self.constraints.new_array(name=name, index_max=nbytes)
        self.input_symbols.append(expr)

        if options.get('cstring', False):
            for i in range(nbytes - 1):
                self.constraints.add(expr[i] != 0)

        return expr

    def new_symbolic_value(self, nbits, label='val', taint=frozenset()):
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
        expr = self.constraints.new_bitvec(nbits, name=label, taint=taint)
        self.input_symbols.append(expr)
        return expr

    def symbolicate_buffer(self, data, label='INPUT', wildcard='+', string=False):
        '''Mark parts of a buffer as symbolic (demarked by the wildcard byte)

        :param str data: The string to symbolicate. If no wildcard bytes are provided,
                this is the identity function on the first argument.
        :param str label: The label to assign to the value
        :param str wildcard: The byte that is considered a wildcard
        :param bool string: Ensure bytes returned can not be \0

        :return: If data does not contain any wildcard bytes, data itself. Otherwise,
            a list of values derived from data. Non-wildcard bytes are kept as
            is, wildcard bytes are replaced by Expression objects.
        '''
        if wildcard in data:
            size = len(data)
            symb = self.constraints.new_array(name=label, index_max=size)
            self.input_symbols.append(symb)

            tmp = []
            for i in xrange(size):
                if data[i] == wildcard:
                    tmp.append(symb[i])
                else:
                    tmp.append(data[i])

            data = tmp

        if string:
            for b in data:
                if issymbolic(b):
                    self.constraints.add(b != 0)
                else:
                    assert b != 0
        return data

    def concretize(self, symbolic, policy, maxcount=100):
        ''' This finds a set of solutions for symbolic using policy.
            This raises TooManySolutions if more solutions than maxcount 
        '''
        vals = []
        if policy == 'MINMAX':
            vals = self._solver.minmax(self.constraints, symbolic)
        elif policy == 'SAMPLED':
            m, M = self._solver.minmax(self.constraints, symbolic)
            vals += [m, M]
            if M - m > 3:
                if self._solver.can_be_true(self.constraints, symbolic == (m + M) / 2):
                    vals.append((m + M) / 2)
            if M - m > 100:
                vals += self._solver.get_all_values(self.constraints, symbolic,
                                                    maxcnt=maxcount, silent=True)
        elif policy == 'ONE':
            vals = [self._solver.get_value(self.constraints, symbolic)]
        else:
            assert policy == 'ALL'
            vals = solver.get_all_values(self.constraints, symbolic, maxcnt=maxcount,
                                         silent=False)

        return list(set(vals))

    @property
    def _solver(self):
        from .smtlib import solver
        return solver

    def solve_one(self, expr):
        '''
        Concretize a symbolic :class:`~manticore.core.smtlib.expression.Expression` into
        one solution.

        :param manticore.core.smtlib.Expression expr: Symbolic value to concretize
        :return: Concrete value
        :rtype: int
        '''
        return self._solver.get_value(self.constraints, expr)

    def solve_n(self, expr, nsolves, policy='minmax'):
        '''
        Concretize a symbolic :class:`~manticore.core.smtlib.expression.Expression` into
        `nsolves` solutions.

        :param manticore.core.smtlib.Expression expr: Symbolic value to concretize
        :return: Concrete value
        :rtype: list[int]
        '''
        return self._solver.get_all_values(self.constraints, expr, nsolves, silent=True)

    def solve_buffer(self, addr, nbytes):
        '''
        Reads `nbytes` of symbolic data from a buffer in memory at `addr` and attempts to
        concretize it

        :param int address: Address of buffer to concretize
        :param int nbytes: Size of buffer to concretize
        :return: Concrete contents of buffer
        :rtype: list[int]
        '''
        buffer = self.cpu.read_bytes(addr, nbytes)
        result = []
        with self.constraints as temp_cs:
            for c in buffer:
                result.append(self._solver.get_value(temp_cs, c))
                temp_cs.add(c == result[-1])
        return result

    def record_branches(self, targets):
        _, branch = self.last_pc
        for target in targets:
            key = (branch, target)
            try:
                self.branches[key] += 1
            except KeyError:
                self.branches[key] = 1

    def generate_inputs(self, workspace, generate_files=False):
        '''
        Save the inputs of the state

        :param str workspace: the working directory
        :param bool generate_files: true if symbolic files are also generated
        '''

        # Save constraints formula
        smtfile = 'state_{:08x}.smt'.format(self.co)
        with open(os.path.join(workspace, smtfile), 'wb') as f:
            f.write(str(self.constraints))

        # check that the state is sat
        assert solver.check(self.constraints)

        # save the inputs
        for symbol in self.input_symbols:
            buf = solver.get_value(self.constraints, symbol)
            filename = os.path.join(workspace, 'state_{:08x}.txt'.format(self.co))
            open(filename, 'a').write("{:s}: {:s}\n".format(symbol.name, repr(buf)))

        # save the symbolic files
        if generate_files:
            files = getattr(self.platform, 'files', None)
            if files is not None:
                for f in files:
                    array = getattr(f, 'array', None)
                    if array is not None:
                        buf = solver.get_value(self.constraints, array)
                        filename = os.path.basename(array.name)
                        filename = 'state_{:08x}.{:s}'.format(self.co, filename)
                        filename = os.path.join(workspace, filename)
                        with open(filename, 'a') as f:
                            f.write("{:s}".format(buf))


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
        self.platform.invoke_model(model, prefix_args=(self,))

