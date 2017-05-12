###############################################################################
# Solver
# A solver maintains a companion smtlib capable process connected via stdio.
# It can be in 4 main states: None, unknown, sat, unsat
# None      nothing was yet sent to the smtlib process. Al the state is only at the python side
# unknown   is an error state. Some query sent early was unsuccessful or timed out. Further 
#           interaction with the smtlib process will probably kept beign unknown. An exception is raised.
# sat       the current set of constraints is satisfiable and has at least one solution
# unsat     the current set of constraints is impossible
#
# It starts at None.
# Once you Solver.check() it the status is changed to sat or unsat (or unknown+exception)
# You can create new symbols operate on them. The declarations will be sent to the smtlib process when needed.
# You can add new constraints. A new constraint may change the state from {None, sat} to {sat, unsat, unknown}

from subprocess import PIPE, Popen, check_output
from abc import ABCMeta, abstractmethod
from copy import copy, deepcopy
import operators as Operators
from expression import *
from constraints import *
import logging
import re
import time
from visitors import *
from ...utils.helpers import issymbolic, memoized
import collections

logger = logging.getLogger("SMT")

class Z3NotFoundError(EnvironmentError):
    pass

class SolverException(Exception):
    pass

class SolverUnknown(SolverException):
    pass

class TooManySolutions(SolverException):
    def __init__(self, solutions):
        super(TooManySolutions, self).__init__("Max number of different solutions hit")
        self.solutions = solutions

class Solver(object):
    __metaclass__ = ABCMeta

    @abstractmethod
    def __init__(self):
        pass

    @abstractmethod
    def optimize(self, X, operation, M=10000):
        ''' Iterativelly finds the maximum or minimal value for the operation 
            (Normally Operators.UGT or Operators.ULT)
            :param X: a symbol or expression
            :param M: maximum number of iterations allowed
        '''
        pass

    def check(self, constraints):
        ''' Check if expression can be valid '''
        return self.can_be_true(constraints, True)

    @abstractmethod
    def can_be_true(self, constraints, expression):
        ''' Check if expression can be valid '''
        pass

    @abstractmethod
    def get_all_values(self, constraints, x, maxcnt=10000, silent=False):
        ''' Returns a list with all the possible values for the symbol x'''
        pass

    @abstractmethod
    def get_value(self, constraints, expression):
        ''' Ask the solver for one possible assignment for expression using current set
            of constraints.
            The current set of assertions must be sat.
            :param val: an expression or symbol '''
        pass

    def max(self, constraints, X, M=10000):
        ''' Iterativelly finds the maximum value for a symbol.
            :param X: a symbol or expression
            :param M: maximum number of iterations allowed
        '''
        assert isinstance(X, BitVec)
        return self.optimize(constraints, X, 'maximize')

    def min(self, constraints, X, M=10000):
        ''' Iterativelly finds the minimum value for a symbol.
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

#FixME move this \/ This configuration should be registered as global config 
consider_unknown_as_unsat = True


Version = collections.namedtuple('Version', 'major minor patch')
class Z3Solver(Solver):
    def __init__(self):
        ''' Build a Z3 solver instance.
            This is implemented using an external z3 solver (via a subprocess).
        '''
        super(Z3Solver, self).__init__()
        self._proc = None
        self._log = '' #this should be enabled only if we are debugging

        self.version = self._solver_version()

        self.support_maximize = False
        self.support_minimize = False
        self.support_reset = True
        logger.debug('Z3 version: %s', self.version)

        if self.version >= Version(4, 4, 1):
            self.support_maximize = True
            self.support_minimize = True
        else:
            logger.debug(' Please install Z3 4.4.1 or newer to get optimization support')

        self._command = 'z3 -t:120000 -smt2 -in'
        self._init = ['(set-logic QF_AUFBV)', '(set-option :global-decls false)']
        self._get_value_fmt = (re.compile('\(\((?P<expr>(.*))\ #x(?P<value>([0-9a-fA-F]*))\)\)'), 16)

    @staticmethod
    def _solver_version():
        '''
        If we
        fail to parse the version, we assume z3's output has changed, meaning it's a newer
        version than what's used now, and therefore ok.
        
        Anticipated version_cmd_output format: 'Z3 version 4.4.2'
                                               'Z3 version 4.4.5 - 64 bit - build hashcode $Z3GITHASH'

    
        '''
        their_version = Version(0,0,0)
        try:
            version_cmd_output = check_output('z3 -version'.split())
        except OSError:
            raise Z3NotFoundError
        try:
            version = version_cmd_output.split()[2]
            their_version = Version(*map(int, version.split('.')))
        except (IndexError, ValueError, TypeError):
            pass
        return their_version

        
    def _start_proc(self):
        ''' Auxiliary method to spawn the external solver process'''
        assert '_proc' not in dir(self) or self._proc is None
        try:
            self._proc = Popen(self._command.split(' '), stdin=PIPE, stdout=PIPE )
        except OSError:
            #Z3 was removed from the system in the middle of operation
            raise Z3NotFoundError  # TODO(mark) don't catch this exception in two places

        #run solver specific initializations
        for cfg in self._init:
            self._send(cfg)

    def _stop_proc(self):
        ''' Auxiliary method to stop the external solver process'''
        if self._proc is not None:
            self._send("(exit)")
            self._proc.stdin.close()
            self._proc.stdout.close()
            self._proc.wait()
        try:
            self._proc.kill()
        except:
            pass
        self._proc = None

    #marshaling/pickle
    def __getstate__(self):
        raise Exception()

    def __setstate__(self, state):
        raise Exception()

    def __del__(self):
        try:
            self._proc.stdin.writelines(('(exit)\n',))
            self._proc.wait()
        except Exception,e:
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
        logger.debug('>%s',cmd)
        self._log += str(cmd) + '\n'
        try:
            buf = str(cmd)
            self._proc.stdin.write(buf+'\n')
        except IOError as e:
            raise SolverException(e)

    def _recv(self):
        ''' Reads the response from the solver '''
        def readline():
            buf = self._proc.stdout.readline()
            return buf, buf.count('('), buf.count(')')
        bufl = []
        left = 0
        right = 0
        buf,l,r = readline()
        bufl.append(buf)
        left +=l
        right+=r
        while left != right:
            buf,l,r = readline()
            bufl.append(buf)
            left +=l
            right+=r
        buf = ''.join(bufl).strip()
        logger.debug('<%s', buf)
        if '(error' in bufl[0]:
            raise Exception("Error in smtlib: {}".format(bufl[0]))
        return buf

    ## UTILS: check-sat get-value 
    def _check(self):
        ''' Check the satisfiability of the current state '''
        logger.debug("Solver.check() ")
        start = time.time()
        self._send('(check-sat)')
        _status = self._recv()
        logger.debug("Check took %s seconds (%s)", time.time()- start, _status)
        if _status not in ('sat','unsat','unknown'):
            raise SolverException(_status)
        if consider_unknown_as_unsat:
            if _status == 'unknown':
                logger.warning('Found an unknown core, probably a solver timeout')
                _status = 'unsat'

        if _status == 'unknown':
            raise SolverUnknown(_status)

        return _status

    def _assert(self, expression):
        ''' Auxiliary method to send an assert '''
        assert isinstance(expression, Bool)
        smtlib = translate_to_smtlib(expression)
        self._send('(assert %s)'%smtlib)

    def _getvalue(self, expression):
        ''' Ask the solver for one possible assignment for val using current set
            of constraints.
            The current set of assertions must be sat.
            :param val: an expression or symbol '''
        if not issymbolic(expression):
            return expression
        assert isinstance(expression, Variable)

        self._send('(get-value (%s))'%expression.name)
        ret = self._recv()
        assert ret.startswith('((') and ret.endswith('))')

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
        ''' Recall the last pushed constraint store  and state. '''
        self._send('(pop 1)')



    #@memoized
    def can_be_true(self, constraints, expression):
        ''' Check if two potentially symbolic values can be equal '''
        if isinstance(expression, bool):
            if expression == False:
                return expression
            else:
                expression = BoolConstant(expression)
        assert isinstance(expression, Bool)

        with constraints as temp_cs:
            temp_cs.add(expression)
            self._reset(temp_cs.related_to(expression))
            return self._check() == 'sat'


    #get-all-values min max minmax
    #@memoized
    def get_all_values(self, constraints, expression, maxcnt=300, silent=False):
        ''' Returns a list with all the possible values for the symbol x'''
        assert isinstance(constraints, ConstraintSet)
        assert isinstance(expression, Expression)

        with constraints as temp_cs:
            if isinstance(expression, Bool):
                var = temp_cs.new_bool()
            elif isinstance(expression, BitVec):
                var = temp_cs.new_bitvec(expression.size)
            else:
                raise NotImplementedError("get_all_values only implemted for Bool and BitVec")

            temp_cs.add(var==expression)
            self._reset(temp_cs.related_to(var))

            result = []
            val = None
            while self._check() == 'sat':
                value = self._getvalue(var)
                result.append(value)

                # Reset the solver to avoid the incremental mode 
                # Triggered with two consecutive calls to check-sat
                # Yet, if the number of solution is large, sending back
                # the whole formula is more expensive
                if len(result) < 50:
                    self._reset(temp_cs.related_to(var) )
                    for value in result:
                        self._assert( var != value )
                else:
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
        ''' Iterativelly finds the maximum or minimal value for the operation 
            (Normally Operators.UGT or Operators.ULT)
            :param X: a symbol or expression
            :param M: maximum number of iterations allowed
        '''
        assert goal in ('maximize', 'minimize')
        assert isinstance(x, BitVec)
        operation = {'maximize':Operators.UGE, 'minimize': Operators.ULE}[goal]

        with constraints as temp_cs:
            X = temp_cs.new_bitvec(x.size)
            temp_cs.add(X == x)
            aux = temp_cs.new_bitvec(X.size)
            self._reset(temp_cs)
            self._send(aux.declaration)

            if getattr(self, 'support_{}'.format(goal)):
                self._push()
                try:
                    self._assert( operation(X, aux) )
                    self._send('(%s %s)' % (goal, aux.name) )
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
                            raise SolverException('bad output on max, z3 may have been killed')

                        pattern = re.compile('\(objectives.*\((?P<expr>.*) (?P<value>\d*)\).*\).*', re.MULTILINE|re.DOTALL)
                        m = pattern.match(ret)
                        expr, value = m.group('expr'), m.group('value')
                        assert expr == aux.name
                        return int(value)
                finally:
                    self._pop()
                    self._reset(temp_cs)
                    self._send(aux.declaration)

            operation = {'maximize':Operators.UGT, 'minimize': Operators.ULT}[goal]
            self._assert( aux == X )
            last_value = None
            i = 0
            while self._check() == 'sat' :
                last_value = self._getvalue(aux)
                self._assert(operation(aux, last_value))
                i = i + 1
                if (i > M):
                    raise SolverException("Optimizing error, maximum number of iterations was reached")
            if last_value != None:
                return last_value
            raise SolverException("Optimizing error, unsat or unknown core")

    #@memoized
    def get_value(self, constraints, expression):
        ''' Ask the solver for one possible assignment for val using current set
            of constraints.
            The current set of assertions must be sat.
            :param val: an expression or symbol '''
        if not issymbolic(expression):
            if isinstance(expression, str):
                expression = ord(expression)
            return expression
        assert isinstance(expression, (Bool, BitVec, Array))
        with constraints as temp_cs:
            if isinstance(expression, Bool):
                var = temp_cs.new_bool()
            elif isinstance(expression, BitVec):
                var = temp_cs.new_bitvec(expression.size)
            elif isinstance(expression, Array):
                var = []
                result = ''
                for i in xrange(expression.index_max):
                    subvar = temp_cs.new_bitvec(8)
                    var.append(subvar)
                    temp_cs.add(subvar==expression[i])

                self._reset(temp_cs)
                if self._check() != 'sat':
                    raise SolverException('Model is not available')

                for i in xrange(expression.index_max):
                    self._send('(get-value (%s))'%var[i].name)
                    ret = self._recv()
                    assert ret.startswith('((') and ret.endswith('))')
                    pattern, base = self._get_value_fmt
                    m = pattern.match(ret)
                    expr, value = m.group('expr'), m.group('value')
                    result += chr(int(value, base))
                return result

            temp_cs.add(var == expression)

            self._reset(temp_cs)

        if self._check() != 'sat':
            raise SolverException('Model is not available')

        self._send('(get-value (%s))'%var.name)
        ret = self._recv()
        assert ret.startswith('((') and ret.endswith('))')

        if isinstance(expression, Bool):
            return {'true':True, 'false':False}[ret[2:-2].split(' ')[1]]
        if isinstance(expression, BitVec):
            pattern, base = self._get_value_fmt
            m = pattern.match(ret)
            expr, value = m.group('expr'), m.group('value')
            return int(value, base)
        raise NotImplementedError("get_value only implemented for Bool and BitVec")


solver = Z3Solver()
