
###############################################################################
# Solver
# A solver maintains a companion smtlib capable process connected via stdio.
# It can be in 4 main states: None, unknown, sat, unsat
# None      nothing was yet sent to the smtlib process. Al the state is only at the python side
# unknown   is an error state. Some query sent earlier was unsuccessful or timed out.
#           Further interaction with the smtlib process will probably keep returning
#           unknown. An exception is raised.
# sat       the current set of constraints is satisfiable and has at least one solution
# unsat     the current set of constraints is impossible
#
# It starts at None.
# Once you Solver.check() it the status is changed to sat or unsat (or unknown+exception)
# You can create new symbols operate on them. The declarations will be sent to the smtlib process when needed.
# You can add new constraints. A new constraint may change the state from {None, sat} to {sat, unsat, unknown}
from abc import ABCMeta, abstractmethod
from subprocess import PIPE, Popen, check_output

from ...exceptions import Z3NotFoundError, SolverError, SolverUnknown, TooManySolutions
from . import operators as Operators
from .expression import *
from .constraints import *
import logging
import re
import shlex
import time
from .visitors import *
from ...utils.helpers import issymbolic, istainted, taint_with, get_taints
from ...utils import config
import io
import collections

logger = logging.getLogger(__name__)

consts = config.get_group('smt')
consts.add('timeout', default=240, description='Timeout, in seconds, for each Z3 invocation')
consts.add('memory', default=16384, description='Max memory for Z3 to use (in Megabytes)')
consts.add('maxsolutions', default=10000, description='Maximum solutions to provide when solving for all values')
consts.add('z3_bin', default='z3', description='Z3 binary to use')

class Solver(object, metaclass=ABCMeta):
    @abstractmethod
    def __init__(self):
        pass

    def optimize(self, constraints, X, operation, M=10000):
        ''' Iteratively finds the maximum or minimal value for the operation
            (Normally Operators.UGT or Operators.ULT)
            :param constraints: the constraints set
            :param X: a symbol or expression
            :param M: maximum number of iterations allowed
        '''
        raise Exception("Abstract method not implemented")

    def check(self, constraints):
        ''' Check if expression can be valid '''
        return self.can_be_true(constraints, True)

    def can_be_true(self, constraints, expression):
        ''' Check if expression could be valid '''
        raise Exception("Abstract method not implemented")

    def must_be_true(self, constraints, expression):
        ''' Check if expression is True and that it can not be False with current
            constraints
        '''
        solutions = self.get_all_values(constraints, expression, maxcnt=2, silent=True)
        return solutions == [True]

    def get_all_values(self, constraints, x, maxcnt=10000, silent=False):
        ''' Returns a list with all the possible values for the symbol x'''
        raise Exception("Abstract method not implemented")

    def get_value(self, constraints, expression):
        ''' Ask the solver for one possible assignment for expression using current set
            of constraints.
            The current set of assertions must be sat.
            :param val: an expression or symbol '''
        raise Exception("Abstract method not implemented")

    def max(self, constraints, X, M=10000):
        ''' Iteratively finds the maximum value for a symbol.
            :param X: a symbol or expression
            :param M: maximum number of iterations allowed
        '''
        assert isinstance(X, BitVec)
        return self.optimize(constraints, X, 'maximize')

    def min(self, constraints, X, M=10000):
        ''' Iteratively finds the minimum value for a symbol.
            :param X: a symbol or expression
            :param M: maximum number of iterations allowed
        '''
        assert isinstance(X, BitVec)
        return self.optimize(constraints, X, 'minimize')

    def minmax(self, constraints, x, iters=10000):
        ''' Returns the min and max possible values for x. '''
        if issymbolic(x):
            m = self.min(constraints, x, iters)
            M = self.max(constraints, x, iters)
            return m, M
        else:
            return x, x


# FixME move this \/ This configuration should be registered as global config
consider_unknown_as_unsat = True


Version = collections.namedtuple('Version', 'major minor patch')


class Z3Solver(Solver):
    def __init__(self):
        ''' Build a Z3 solver instance.
            This is implemented using an external z3 solver (via a subprocess).
        '''
        super().__init__()
        self._proc = None

        self._command = f'{consts.z3_bin} -t:{consts.timeout*1000} -memory:{consts.memory} -smt2 -in'
        self._init = ['(set-logic QF_AUFBV)', '(set-option :global-decls false)']
        self._get_value_fmt = (re.compile('\(\((?P<expr>(.*))\ #x(?P<value>([0-9a-fA-F]*))\)\)'), 16)

        self.debug = False
        # To cache what get-info returned; can be directly set when writing tests
        self._received_version = None
        self.version = self._solver_version()

        self.support_maximize = False
        self.support_minimize = False
        self.support_reset = True
        logger.debug('Z3 version: %s', self.version)

        if self.version >= Version(4, 5, 0):
            self.support_maximize = False
            self.support_minimize = False
            self.support_reset = False
        elif self.version >= Version(4, 4, 1):
            self.support_maximize = True
            self.support_minimize = True
            self.support_reset = False
        else:
            logger.debug(' Please install Z3 4.4.1 or newer to get optimization support')

    def _solver_version(self):
        '''
        If we
        fail to parse the version, we assume z3's output has changed, meaning it's a newer
        version than what's used now, and therefore ok.

        Anticipated version_cmd_output format: 'Z3 version 4.4.2'
                                               'Z3 version 4.4.5 - 64 bit - build hashcode $Z3GITHASH'


        '''
        their_version = Version(0, 0, 0)
        self._reset()
        if self._received_version is None:
            self._send('(get-info :version)')
            self._received_version = self._recv()
        key, version = shlex.split(self._received_version[1:-1])
        return Version(*map(int, version.split('.')))

    def _start_proc(self):
        ''' Auxiliary method to spawn the external solver process'''
        assert '_proc' not in dir(self) or self._proc is None
        try:
            self._proc = Popen(shlex.split(self._command), stdin=PIPE, stdout=PIPE, bufsize=0, universal_newlines=True)
        except OSError as e:
            print(e, "Probably too many cached expressions? visitors._cache...")
            # Z3 was removed from the system in the middle of operation
            raise Z3NotFoundError  # TODO(mark) don't catch this exception in two places

        # run solver specific initializations
        for cfg in self._init:
            self._send(cfg)

    def _stop_proc(self):
        ''' Auxiliary method to stop the external solver process'''
        if self._proc is None:
            return
        if self._proc.returncode is None:
            try:
                self._send("(exit)")
            except (SolverError, IOError) as e:
                # z3 was too fast to close
                logger.debug(str(e))
            finally:
                try:
                    self._proc.stdin.close()
                except IOError as e:
                    logger.debug(str(e))
                try:
                    self._proc.stdout.close()
                except IOError as e:
                    logger.debug(str(e))
                self._proc.kill()
                # Wait for termination, to avoid zombies.
                self._proc.wait()
        self._proc = None

    # marshaling/pickle
    def __getstate__(self):
        raise Exception()

    def __setstate__(self, state):
        raise Exception()

    def __del__(self):
        try:
            if self._proc is not None:
                self._stop_proc()
            # self._proc.stdin.writelines(('(exit)\n',))
            # self._proc.wait()
        except Exception as e:
            logger.error(str(e))
            pass

    def _reset(self, constraints=None):
        ''' Auxiliary method to reset the smtlib external solver to initial defaults'''
        if self._proc is None:
            self._start_proc()
        else:
            if self.support_reset:
                self._send("(reset)")

                for cfg in self._init:
                    self._send(cfg)
            else:
                self._stop_proc()
                self._start_proc()
        if constraints is not None:
            self._send(constraints)

    def _send(self, cmd):
        ''' Send a string to the solver.
            :param cmd: a SMTLIBv2 command (ex. (check-sat))
        '''
        logger.debug('>%s', cmd)
        try:
            self._proc.stdout.flush()
            self._proc.stdin.write(f'{cmd}\n')
        except IOError as e:
            raise SolverError(str(e))

    def _recv(self):
        ''' Reads the response from the solver '''
        def readline():
            buf = self._proc.stdout.readline()
            return buf, buf.count('('), buf.count(')')
        bufl = []
        left = 0
        right = 0
        buf, l, r = readline()
        bufl.append(buf)
        left += l
        right += r
        while left != right:
            buf, l, r = readline()
            bufl.append(buf)
            left += l
            right += r
        buf = ''.join(bufl).strip()
        logger.debug('<%s', buf)
        if '(error' in bufl[0]:
            raise Exception(f"Error in smtlib: {bufl[0]}")
        return buf

    # UTILS: check-sat get-value
    def _check(self):
        ''' Check the satisfiability of the current state '''
        logger.debug("Solver.check() ")
        start = time.time()
        self._send('(check-sat)')
        _status = self._recv()
        logger.debug("Check took %s seconds (%s)", time.time() - start, _status)
        if _status not in ('sat', 'unsat', 'unknown'):
            raise SolverError(_status)
        if consider_unknown_as_unsat:
            if _status == 'unknown':
                logger.info('Found an unknown core, probably a solver timeout')
                _status = 'unsat'

        if _status == 'unknown':
            raise SolverUnknown(_status)

        return _status

    def _assert(self, expression):
        ''' Auxiliary method to send an assert '''
        assert isinstance(expression, Bool)
        smtlib = translate_to_smtlib(expression)
        self._send('(assert %s)' % smtlib)

    def _getvalue(self, expression):
        ''' Ask the solver for one possible assignment for val using current set
            of constraints.
            The current set of assertions must be sat.
            :param val: an expression or symbol '''
        if not issymbolic(expression):
            return expression
        assert isinstance(expression, Variable)

        if isinstance(expression, Array):
            result = bytearray()
            for c in expression:
                expression_str = translate_to_smtlib(c)
                self._send('(get-value (%s))' % expression_str)
                response = self._recv()
                result.append(int('0x{:s}'.format(response.split(expression_str)[1][3:-2]), 16))
            return bytes(result)
        else:
            self._send('(get-value (%s))' % expression.name)
            ret = self._recv()
            assert ret.startswith('((') and ret.endswith('))'), ret

            if isinstance(expression, Bool):
                return {'true': True, 'false': False}[ret[2:-2].split(' ')[1]]
            elif isinstance(expression, BitVec):
                pattern, base = self._get_value_fmt
                m = pattern.match(ret)
                expr, value = m.group('expr'), m.group('value')
                return int(value, base)

        raise NotImplementedError("_getvalue only implemented for Bool and BitVec")

    # push pop
    def _push(self):
        ''' Pushes and save the current constraint store and state.'''
        self._send('(push 1)')

    def _pop(self):
        ''' Recall the last pushed constraint store and state. '''
        self._send('(pop 1)')

    #@memoized
    def can_be_true(self, constraints, expression):
        ''' Check if two potentially symbolic values can be equal '''
        if isinstance(expression, bool):
            if not expression:
                return expression
            else:
                #if True check if constraints are feasible
                self._reset(constraints)
                return self._check() == 'sat'
        assert isinstance(expression, Bool)

        with constraints as temp_cs:
            temp_cs.add(expression)
            self._reset(temp_cs.to_string(related_to=expression))
            return self._check() == 'sat'

    # get-all-values min max minmax
    #@memoized
    def get_all_values(self, constraints, expression, maxcnt=None, silent=False):
        ''' Returns a list with all the possible values for the symbol x'''
        if not isinstance(expression, Expression):
            return [expression]
        assert isinstance(constraints, ConstraintSet)
        assert isinstance(expression, Expression)
        expression = simplify(expression)
        if maxcnt is None:
            maxcnt = consts.maxsolutions

        with constraints as temp_cs:
            if isinstance(expression, Bool):
                var = temp_cs.new_bool()
            elif isinstance(expression, BitVec):
                var = temp_cs.new_bitvec(expression.size)
            elif isinstance(expression, Array):
                var = temp_cs.new_array(index_max=expression.index_max, value_bits=expression.value_bits, taint=expression.taint).array
            else:
                raise NotImplementedError("get_all_values only implemented for Bool and BitVec")

            temp_cs.add(var == expression)
            self._reset(temp_cs.to_string(related_to=var))

            result = []
            val = None
            while self._check() == 'sat':
                value = self._getvalue(var)
                result.append(value)
                self._assert(var != value)

                if len(result) >= maxcnt:
                    if silent:
                        # do not throw an exception if set to silent
                        # Default is not silent, assume user knows
                        # what they are doing and will check the size
                        # of returned vals list (previous smtlib behavior)
                        break
                    else:
                        raise TooManySolutions(result)

            return result

    #@memoized
    def optimize(self, constraints, x, goal, M=10000):
        ''' Iteratively finds the maximum or minimal value for the operation
            (Normally Operators.UGT or Operators.ULT)
            :param X: a symbol or expression
            :param M: maximum number of iterations allowed
        '''
        assert goal in ('maximize', 'minimize')
        assert isinstance(x, BitVec)
        operation = {'maximize': Operators.UGE, 'minimize': Operators.ULE}[goal]

        with constraints as temp_cs:
            X = temp_cs.new_bitvec(x.size)
            temp_cs.add(X == x)
            aux = temp_cs.new_bitvec(X.size, name='optimized_')
            self._reset(temp_cs.to_string(related_to=X))
            self._send(aux.declaration)

            if getattr(self, f'support_{goal}'):
                self._push()
                try:
                    self._assert(operation(X, aux))
                    self._send('(%s %s)' % (goal, aux.name))
                    self._send('(check-sat)')
                    _status = self._recv()
                    if _status not in ('sat', 'unsat', 'unknown'):
                        # Minimize (or Maximize) sometimes prints the objective before the status
                        # This will be a line like NAME |-> VALUE
                        maybe_sat = self._recv()
                        if maybe_sat == 'sat':
                            pattern = re.compile('(?P<expr>.*?)\s+\|->\s+(?P<value>.*)', re.DOTALL)
                            m = pattern.match(_status)
                            expr, value = m.group('expr'), m.group('value')
                            assert expr == aux.name
                            return int(value)
                    elif _status == 'sat':
                        ret = self._recv()
                        if not (ret.startswith('(') and ret.endswith(')')):
                            raise SolverError('bad output on max, z3 may have been killed')

                        pattern = re.compile('\(objectives.*\((?P<expr>.*) (?P<value>\d*)\).*\).*', re.MULTILINE | re.DOTALL)
                        m = pattern.match(ret)
                        expr, value = m.group('expr'), m.group('value')
                        assert expr == aux.name
                        return int(value)
                finally:
                    self._pop()
                    self._reset(temp_cs)
                    self._send(aux.declaration)

            operation = {'maximize': Operators.UGT, 'minimize': Operators.ULT}[goal]
            self._assert(aux == X)
            last_value = None
            i = 0
            while self._check() == 'sat':
                last_value = self._getvalue(aux)
                self._assert(operation(aux, last_value))
                i = i + 1
                if (i > M):
                    raise SolverError("Optimizing error, maximum number of iterations was reached")
            if last_value is not None:
                return last_value
            raise SolverError("Optimizing error, unsat or unknown core")

    #@memoized
    def get_value(self, constraints, expression):
        ''' Ask the solver for one possible assignment for val using current set
            of constraints.
            The current set of assertions must be sat.
            :param val: an expression or symbol '''
        if not issymbolic(expression):
            return expression
        assert isinstance(expression, (Bool, BitVec, Array))
        with constraints as temp_cs:
            if isinstance(expression, Bool):
                var = temp_cs.new_bool()
            elif isinstance(expression, BitVec):
                var = temp_cs.new_bitvec(expression.size)
            elif isinstance(expression, Array):
                var = []
                result = []
                for i in range(expression.index_max):
                    subvar = temp_cs.new_bitvec(expression.value_bits)
                    var.append(subvar)
                    temp_cs.add(subvar == simplify(expression[i]))

                self._reset(temp_cs)
                if self._check() != 'sat':
                    raise SolverError('Model is not available')

                for i in range(expression.index_max):
                    self._send('(get-value (%s))' % var[i].name)
                    ret = self._recv()
                    assert ret.startswith('((') and ret.endswith('))')
                    pattern, base = self._get_value_fmt
                    m = pattern.match(ret)
                    expr, value = m.group('expr'), m.group('value')
                    result.append(int(value, base))
                return bytes(result)

            temp_cs.add(var == expression)

            self._reset(temp_cs)

        if self._check() != 'sat':
            raise SolverError('Model is not available')

        self._send('(get-value (%s))' % var.name)
        ret = self._recv()
        if not (ret.startswith('((') and ret.endswith('))')):
            raise SolverError('SMTLIB error parsing response: %s' % ret)

        if isinstance(expression, Bool):
            return {'true': True, 'false': False}[ret[2:-2].split(' ')[1]]
        if isinstance(expression, BitVec):
            pattern, base = self._get_value_fmt
            m = pattern.match(ret)
            expr, value = m.group('expr'), m.group('value')
            return int(value, base)
        raise NotImplementedError("get_value only implemented for Bool and BitVec")


solver = Z3Solver()
