###############################################################################
# Solver
# A solver maintains a companion smtlib capable proceess connected via stdio.
# It can be in 4 main states: None, unknown, sat, unsat
# None      nothing was yet sent to the smtlib proccess. Al the state is only at the python side
# unknown   is an error state. Some query sent early was unsuccessful or timed out. Further 
#           interaction with the smtlib proccess will probably kept beign unknown. An exception is raised.
# sat       the current set of constraints is sat-isfiable and has at least one solution
# unsat     the current set of constraints is impossible
#
# It starts at None.
# Once you Solver.check() it the status is changed to sat or unsat (or unknown+exception)
# You can create new symbols operate on them. The declarations will be sended to the smtlib proceess when needed.
# You can add new constraints. A new contraint may change the state from {None, sat} to {sat, unsat, unknown}

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
from ...utils.helpers import issymbolic
logger = logging.getLogger("SMT")

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
        ''' Iterativelly finds the maximun or minimal value for the operation 
            (Normally Operators.UGT or Operators.ULT)
            @param X: a symbol or expression
            @param M: maximun number of iterations allowed
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
        ''' Ask the solver for one possible assigment for expression using currrent set
            of constraints.
            The current set of assertions must be sat.
            @param val: an expression or symbol '''
        pass

    def max(self, constraints, X, M=10000):
        ''' Iterativelly finds the maximum value for a symbol.
            @param X: a symbol or expression
            @param M: maximun number of iterations allowed
        '''
        assert isinstance(X, BitVec)
        return self.optimize(constraints, X, 'maximize')

    def min(self, constraints, X, M=10000):
        ''' Iterativelly finds the minimum value for a symbol.
            @param X: a symbol or expression
            @param M: maximun number of iterations allowed
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

import collections
import functools

class memoized(object):
   '''Decorator. Caches a function's return value each time it is called.
   If called later with the same arguments, the cached value is returned
   (not reevaluated).
   '''
   def __init__(self, func):
      self.func = func
      self.cache = {}
   def __call__(self, *args, **kwargs):
      key = args + tuple(sorted(kwargs.items()))
      if not isinstance(key, collections.Hashable):
         # uncacheable. a list, for instance.
         # better to not cache than blow up.
         return self.func(*args, **kwargs)
      if key in self.cache:
         return self.cache[key]
      else:
         value = self.func(*args, **kwargs)
         self.cache[key] = value
         return value
   def __repr__(self):
      '''Return the function's docstring.'''
      return self.func.__doc__
   def __get__(self, obj, objtype):
      '''Support instance methods.'''
      return functools.partial(self.__call__, obj)

#FixME move this \/
consider_unknown_as_unsat = True

class SMTSolver(Solver):
    def __init__(self):
        ''' Build a solver intance.
            This is implemented using an external native solver via a subprocess.
            Everytime a new symbol or assertion is added a smtlibv2 command is 
            sent to the solver.
            The actual state is also mantained in memory to be able to save and
            restore the state. 
            The analisys may be saved to disk and continued after a while or 
            forked in memory or even sent over the network.
        '''
        super(SMTSolver, self).__init__()
        try:
            version_cmd_output = check_output(self.version_cmd.split())
        except OSError:
            raise Exception('Z3 not installed!')
        self._check_solver_version(version_cmd_output)
        self._proc = None
        self._constraints = None
        self._log = ''

    def _check_solver_version(self, version_cmd_output):
        ''' Auxiliary method to check the version of the external solver
            This will spawn the external solver with the configured parameters and check that the banner matches the expected version.
        '''
        pass

    def _start_proc(self):
        ''' Auxiliary method to spawn the external solver pocess'''
        assert '_proc' not in dir(self) or self._proc is None
        try:
            self._proc = Popen(self.command.split(' '), stdin=PIPE, stdout=PIPE )
        except OSError:
            raise Exception('Z3 not installed!')  # TODO(mark) don't catch this exception in two places

        #run solver specific initializations
        for cfg in self.init:
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
                for cfg in self.init:
                    self._send(cfg)
            else: 
                self._stop_proc()
                self._start_proc()
        if constraints is not None:
            self._send(constraints)


    def _send(self, cmd):
        ''' Send a string to the solver.
            @param cmd: a SMTLIBv2 command (ex. (check-sat))
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

    ## UTILS: check-sat get-value simplify 
    def _check(self):
        ''' Check the satisfiability of the current state '''
        logger.debug("!! Solver.check() ")
        start = time.time()
        self._send('(check-sat)')
        _status = self._recv()
        logger.debug("Check took %s seconds (%s)", time.time()- start, _status)
        if _status not in ('sat','unsat','unknown'):
            #print "<"*100 + self._log +">"*100
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
        ''' Ask the solver for one possible assigment for val using currrent set
            of constraints.
            The current set of assertions must be sat.
            @param val: an expression or symbol '''
        if not issymbolic(expression):
            return expression
        assert isinstance(expression, Variable)

        self._send('(get-value (%s))'%expression.name)
        ret = self._recv()
        assert ret.startswith('((') and ret.endswith('))')

        if isinstance(expression, Bool):
            return {'true': True, 'false': False}[ret[2:-2].split(' ')[1]]
        elif isinstance(expression, BitVec):
            pattern, base = self.get_value_fmt
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
                self._assert( var != value )
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
        ''' Iterativelly finds the maximun or minimal value for the operation 
            (Normally Operators.UGT or Operators.ULT)
            @param X: a symbol or expression
            @param M: maximun number of iterations allowed
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
                    self._send('(check-sat)' )
                    if self._recv() == 'sat': #first line
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
        ''' Ask the solver for one possible assigment for val using currrent set
            of constraints.
            The current set of assertions must be sat.
            @param val: an expression or symbol '''
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
                    pattern, base = self.get_value_fmt
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
            pattern, base = self.get_value_fmt
            m = pattern.match(ret)
            expr, value = m.group('expr'), m.group('value')
            return int(value, base)
        raise NotImplementedError("get_value only implemented for Bool and BitVec")


    def simplify(self):
        ''' Ask the solver to try to simplify the expression val.
            This works only with z3.
            @param val: a symbol or expression. 
        '''
        simple_constraints = []
        for exp in self._constraints:
            new_constraint = exp.simplify()
            if not isinstance(new_constraint, Bool):
                simple_constraints.append(new_constraint)
        self._constraints = set(simple_constraints)

Version = collections.namedtuple('Version', 'major minor patch')

class Z3Solver(SMTSolver):
    def __init__(self):
        self.command = 'z3 -t:30000 -smt2 -in'
        self.init = ['(set-logic QF_AUFBV)', '(set-option :global-decls false)']
        self.version_cmd = 'z3 -version'
        self.min_version = Version(4, 4, 2)
        self.get_value_fmt = (re.compile('\(\((?P<expr>(.*))\ #x(?P<value>([0-9a-fA-F]*))\)\)'), 16)
        self.support_simplify = True
        self.support_reset = False
        self.support_maximize = True
        self.support_minimize = True
        super(Z3Solver, self).__init__()

    def _check_solver_version(self, version_cmd_output):
        '''
        Check that the z3 version we're using is at least the minimum we need. If we
        fail to parse the version, we assume z3's output has changed, meaning it's a newer
        version than what's used now, and therefore ok.
        
        Anticipated version_cmd_output format: 'Z3 version 4.4.2'
        '''
        try:
            version = version_cmd_output.split()[2]
            their_version = Version(*map(int, version.split('.')))
            if their_version < self.min_version:
                raise SolverException("Z3 Version >= {}.{}.{} required".format(*self.min_version))
        except (IndexError, ValueError, TypeError):
            pass

solver = Z3Solver()
