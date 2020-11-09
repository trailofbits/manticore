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

import os
import shutil
import threading
from queue import Queue
import collections
import shlex
import time
from functools import lru_cache
from typing import Dict, Tuple, Sequence, Optional
from subprocess import PIPE, Popen, check_output
import re
from . import operators as Operators
from .constraints import *
from .visitors import *
from ...exceptions import Z3NotFoundError, SolverError, SolverUnknown, TooManySolutions, SmtlibError
from ...utils import config
from . import issymbolic


class SolverType(config.ConfigEnum):
    """Used as configuration constant for choosing solver flavor"""

    z3 = "z3"
    cvc4 = "cvc4"
    yices = "yices"
    auto = "auto"


logger = logging.getLogger(__name__)
consts = config.get_group("smt")
consts.add("timeout", default=120, description="Timeout, in seconds, for each Z3 invocation")
consts.add("memory", default=1024 * 8, description="Max memory for Z3 to use (in Megabytes)")
consts.add(
    "maxsolutions",
    default=10000,
    description="Maximum solutions to provide when solving for all values",
)
consts.add("z3_bin", default="z3", description="Z3 solver binary to use")
consts.add("cvc4_bin", default="cvc4", description="CVC4 solver binary to use")
consts.add("yices_bin", default="yices-smt2", description="Yices solver binary to use")


consts.add("defaultunsat", default=True, description="Consider solver timeouts as unsat core")
consts.add(
    "optimize", default=True, description="Use smtlib command optimize to find min/max if available"
)

consts.add(
    "solver",
    default=SolverType.auto,
    description="Choose default smtlib2 solver (z3, yices, cvc4, auto)",
)

# Regular expressions used by the solver
RE_GET_EXPR_VALUE_FMT_BIN = re.compile(r"\(\((?P<expr>(.*))[ \n\s]*#b(?P<value>([0-1]*))\)\)")
RE_GET_EXPR_VALUE_FMT_DEC = re.compile(r"\(\((?P<expr>(.*))\ \(_\ bv(?P<value>(\d*))\ \d*\)\)\)")
RE_GET_EXPR_VALUE_FMT_HEX = re.compile(r"\(\((?P<expr>(.*))\ #x(?P<value>([0-9a-fA-F]*))\)\)")
RE_OBJECTIVES_EXPR_VALUE = re.compile(
    r"\(objectives.*\((?P<expr>.*) (?P<value>\d*)\).*\).*", re.MULTILINE | re.DOTALL
)
RE_MIN_MAX_OBJECTIVE_EXPR_VALUE = re.compile(r"(?P<expr>.*?)\s+\|->\s+(?P<value>.*)", re.DOTALL)


class SingletonMixin(object):
    __singleton_instances: Dict[Tuple[int, int], "SingletonMixin"] = {}

    @classmethod
    def instance(cls):
        tid = threading.get_ident()
        pid = os.getpid()
        if not (pid, tid) in cls.__singleton_instances:
            cls.__singleton_instances[(pid, tid)] = cls()
        return cls.__singleton_instances[(pid, tid)]


class SolverException(SmtlibError):
    """
    Solver exception
    """

    pass


class Solver(SingletonMixin):
    def __init__(self):
        pass

    def optimize(self, constraints, X, operation, M=10000):
        """
        Iteratively finds the maximum or minimal value for the operation
        (Normally Operators.UGT or Operators.ULT)

        :param constraints: the constraints set
        :param X: a symbol or expression
        :param M: maximum number of iterations allowed
        """
        raise SmtlibError("Abstract method not implemented")

    def check(self, constraints) -> bool:
        """Check if given constraints can be valid"""
        return self.can_be_true(constraints, True)

    def can_be_true(self, constraints, expression=True) -> bool:
        """Check if given expression could be valid"""
        raise SolverException("Abstract method not implemented")

    def must_be_true(self, constraints, expression) -> bool:
        """Check if expression is True and that it can not be False with current constraints"""
        solutions = self.get_all_values(constraints, expression, maxcnt=2, silent=True)
        return solutions == [True]

    def get_all_values(self, constraints, x, maxcnt=10000, silent=False):
        """Returns a list with all the possible values for the symbol x"""
        raise SolverException("Abstract method not implemented")

    def get_value(self, constraints, expression):
        """Ask the solver for one possible result of given expression using given set of constraints."""
        raise SolverException("Abstract method not implemented")

    def max(self, constraints, X: BitVec, M=10000):
        """
        Iteratively finds the maximum value for a symbol within given constraints.
        :param X: a symbol or expression
        :param M: maximum number of iterations allowed
        """
        assert isinstance(X, BitVec)
        return self.optimize(constraints, X, "maximize", M)

    def min(self, constraints, X: BitVec, M=10000):
        """
        Iteratively finds the minimum value for a symbol within given constraints.

        :param constraints: constraints that the expression must fulfil
        :param X: a symbol or expression
        :param M: maximum number of iterations allowed
        """
        assert isinstance(X, BitVec)
        return self.optimize(constraints, X, "minimize", M)

    def minmax(self, constraints, x, iters=10000):
        """Returns the min and max possible values for x within given constraints"""
        if issymbolic(x):
            m = self.min(constraints, x, iters)
            M = self.max(constraints, x, iters)
            return m, M
        else:
            return x, x


Version = collections.namedtuple("Version", "major minor patch")


class SmtlibProc:
    def __init__(self, command: str, debug: bool = False):
        """ Single smtlib interactive process

        :param command: the shell command to execute
        :param debug: log all messaging
        """
        self._proc: Optional[Popen] = None
        self._command = command
        self._debug = debug

    def start(self):
        """Spawns POpen solver process"""
        if self._proc is not None:
            return
        self._proc = Popen(
            shlex.split(self._command),
            stdin=PIPE,
            stdout=PIPE,
            bufsize=0,
            universal_newlines=True,
            close_fds=True,
        )

    def stop(self):
        """
        Stops the solver process by:
        - sending a SIGKILL signal,
        - waiting till the process terminates (so we don't leave a zombie process)
        """
        if self._proc is None:
            return
        # if it did not finished already
        if self._proc.returncode is None:
            self._proc.stdin.close()
            self._proc.stdout.close()
            # Kill the process
            self._proc.kill()
            self._proc.wait()

            # No need to wait for termination, zombies avoided.
        self._proc = None

    def __readline_and_count(self):
        assert self._proc
        assert self._proc.stdout
        buf = self._proc.stdout.readline()  # No timeout enforced here
        # If debug is enabled check if the solver reports a syntax error
        # Error messages may contain an unbalanced parenthesis situation
        if self._debug:
            if "(error" in buf:
                raise SolverException(f"Error in smtlib: {buf}")
        lparen, rparen = map(sum, zip(*((c == "(", c == ")") for c in buf)))
        return buf, lparen, rparen

    def send(self, cmd: str) -> None:
        """
        Send a string to the solver.

        :param cmd: a SMTLIBv2 command (ex. (check-sat))
        """
        if self._debug:
            logger.debug(">%s", cmd)
        self._proc.stdout.flush()  # type: ignore
        self._proc.stdin.write(f"{cmd}\n")  # type: ignore

    def recv(self) -> str:
        """Reads the response from the smtlib solver"""
        buf, left, right = self.__readline_and_count()
        bufl = [buf]
        while left != right:
            buf, l, r = self.__readline_and_count()
            bufl.append(buf)
            left += l
            right += r

        buf = "".join(bufl).strip()

        if self._debug:
            logger.debug("<%s", buf)

        return buf

    def _restart(self) -> None:
        """Auxiliary to start or restart the external solver"""
        self.stop()
        self.start()

    def is_started(self):
        return self._proc is not None


class SMTLIBSolver(Solver):
    def __init__(
        self,
        command: str,
        init: Sequence[str] = None,
        value_fmt: int = 16,
        support_reset: bool = False,
        support_minmax: bool = False,
        support_pushpop: bool = False,
        multiple_check: bool = True,
        debug: bool = False,
    ):

        """
        Build a smtlib solver instance.
        This is implemented using an external solver (via a subprocess).
        """
        super().__init__()
        self._smtlib: SmtlibProc = SmtlibProc(command, debug)

        # Commands used to initialize smtlib
        if init is None:
            init = tuple()
        self._init = init
        self._get_value_fmt = (
            {
                2: RE_GET_EXPR_VALUE_FMT_BIN,
                10: RE_GET_EXPR_VALUE_FMT_DEC,
                16: RE_GET_EXPR_VALUE_FMT_HEX,
            }[value_fmt],
            value_fmt,
        )

        self._support_minmax = support_minmax
        self._support_reset = support_reset
        self._support_pushpop = support_pushpop
        self._multiple_check = multiple_check

        if not self._support_pushpop:
            setattr(self, "_push", None)
            setattr(self, "_pop", None)

        if self._support_minmax and consts.optimize:
            setattr(self, "optimize", self._optimize_fancy)
        else:
            setattr(self, "optimize", self._optimize_generic)

        self._smtlib.start()
        # run solver specific initializations

    def _reset(self, constraints: Optional[str] = None) -> None:
        """Auxiliary method to reset the smtlib external solver to initial defaults"""
        if self._support_reset:
            self._smtlib.start()  # does not do anything if already started
            self._smtlib.send("(reset)")
        else:
            self._smtlib.stop()  # does not do anything if already stopped
            self._smtlib.start()

        for cfg in self._init:
            self._smtlib.send(cfg)

        if constraints is not None:
            self._smtlib.send(constraints)

    # UTILS: check-sat get-value
    def _is_sat(self) -> bool:
        """
        Check the satisfiability of the current state

        :return: whether current state is satisfiable or not.
        """
        start = time.time()
        self._smtlib.send("(check-sat)")
        status = self._smtlib.recv()
        logger.debug("Check took %s seconds (%s)", time.time() - start, status)
        if status not in ("sat", "unsat", "unknown"):
            raise SolverError(status)
        if consts.defaultunsat:
            if status == "unknown":
                logger.info("Found an unknown core, probably a solver timeout")
                status = "unsat"
        if status == "unknown":
            raise SolverUnknown(status)
        return status == "sat"

    def _assert(self, expression: Bool):
        """Auxiliary method to send an assert"""
        smtlib = translate_to_smtlib(expression)
        self._smtlib.send(f"(assert {smtlib})")

    def __getvalue_bv(self, expression_str: str) -> int:
        self._smtlib.send(f"(get-value ({expression_str}))")
        pattern, base = self._get_value_fmt
        m = pattern.match(self._smtlib.recv())
        expr, value = m.group("expr"), m.group("value")  # type: ignore
        return int(value, base)

    def __getvalue_bool(self, expression_str):
        self._smtlib.send(f"(get-value ({expression_str}))")
        ret = self._smtlib.recv()
        return {"true": True, "false": False}[ret[2:-2].split(" ")[1]]

    def _getvalue(self, expression) -> Union[int, bool, bytes]:
        """
        Ask the solver for one possible assignment for given expression using current set of constraints.
        The current set of expressions must be sat.

        NOTE: This is an internal method: it uses the current solver state (set of constraints!).
        """
        if not issymbolic(expression):
            return expression

        if isinstance(expression, Array):
            result = bytearray()
            for c in expression:
                expression_str = translate_to_smtlib(c)
                result.append(self.__getvalue_bv(expression_str))
            return bytes(result)
        else:
            if isinstance(expression, BoolVariable):
                return self.__getvalue_bool(expression.name)
            elif isinstance(expression, BitVecVariable):
                return self.__getvalue_bv(expression.name)

        raise NotImplementedError(
            f"_getvalue only implemented for Bool, BitVec and Array. Got {type(expression)}"
        )

    # push pop
    def _push(self):
        """Pushes and save the current constraint store and state."""
        self._smtlib.send("(push 1)")

    def _pop(self):
        """Recall the last pushed constraint store and state."""
        self._smtlib.send("(pop 1)")

    @lru_cache(maxsize=32)
    def can_be_true(self, constraints: ConstraintSet, expression: Union[bool, Bool] = True) -> bool:
        """Check if two potentially symbolic values can be equal"""
        if isinstance(expression, bool):
            if not expression:
                return expression
            else:
                # if True check if constraints are feasible
                self._reset(constraints.to_string())
                return self._is_sat()

        with constraints as temp_cs:
            temp_cs.add(expression)
            self._reset(temp_cs.to_string())
            return self._is_sat()

    # get-all-values min max minmax
    def _optimize_generic(self, constraints: ConstraintSet, x: BitVec, goal: str, max_iter=10000):
        """
        Iteratively finds the maximum or minimum value for the operation
        (Normally Operators.UGT or Operators.ULT)

        :param constraints: constraints to take into account
        :param x: a symbol or expression
        :param goal: goal to achieve, either 'maximize' or 'minimize'
        :param max_iter: maximum number of iterations allowed
        """
        # TODO: consider adding a mode to return best known value on timeout
        assert goal in ("maximize", "minimize")
        operation = {"maximize": Operators.UGE, "minimize": Operators.ULE}[goal]

        last_value: Optional[Union[int, bool, bytes]] = None

        start = time.time()
        with constraints as temp_cs:
            X = temp_cs.new_bitvec(x.size)  # _getvalue needs a Variable
            temp_cs.add(X == x)
            self._reset(temp_cs.to_string())

            # Find one value and use it as currently known min/Max
            if not self._is_sat():
                raise SolverException("UNSAT")
            last_value = self._getvalue(X)
            self._assert(operation(X, last_value))

            # This uses a binary search to find a suitable range for aux
            # Use known solution as min or max depending on the goal
            if goal == "maximize":
                m, M = last_value, (1 << X.size) - 1
            else:
                m, M = 0, last_value

            # Iteratively divide the range
            L = None
            while L not in (M, m):
                L = (m + M) // 2
                self._assert(operation(X, L))
                sat = self._is_sat()

                # depending on the goal move one of the extremes
                if goal == "maximize" and sat or goal == "minimize" and not sat:
                    m = L
                else:
                    M = L

                if time.time() - start > consts.timeout:
                    raise SolverError("Timeout")

        # reset to before the dichotomic search
        with constraints as temp_cs:
            X = temp_cs.new_bitvec(x.size)  # _getvalue needs a Variable
            temp_cs.add(X == x)
            self._reset(temp_cs.to_string())

            # At this point we know aux is inside [m,M]
            # Lets constrain it to that range
            self._assert(Operators.UGE(X, m))
            self._assert(Operators.ULE(X, M))

            # And now check all remaining possible extremes
            last_value = None
            i = 0
            while self._is_sat():
                last_value = self._getvalue(X)
                self._assert(operation(X, last_value))
                self._assert(X != last_value)
                i = i + 1
                if i > max_iter:
                    raise SolverError("Optimizing error, maximum number of iterations was reached")
                if time.time() - start > consts.timeout:
                    raise SolverError("Timeout")
            if last_value is not None:
                return last_value
            raise SolverError("Optimizing error, unsat or unknown core")

    @lru_cache(maxsize=32)
    def get_all_values(
        self,
        constraints: ConstraintSet,
        expression,
        maxcnt: Optional[int] = None,
        silent: bool = False,
    ):
        """Returns a list with all the possible values for the symbol x"""
        if not isinstance(expression, Expression):
            return [expression]
        assert isinstance(expression, Expression)
        expression = simplify(expression)
        if maxcnt is None:
            maxcnt = consts.maxsolutions
            if isinstance(expression, Bool) and consts.maxsolutions > 1:
                # We know there is max 2 solutions when Bool
                maxcnt = 2
                silent = True

        with constraints as temp_cs:
            if isinstance(expression, Bool):
                var = temp_cs.new_bool()
            elif isinstance(expression, BitVec):
                var = temp_cs.new_bitvec(expression.size)
            elif isinstance(expression, Array):
                var = temp_cs.new_array(
                    index_max=expression.index_max,
                    value_bits=expression.value_bits,
                    taint=expression.taint,
                ).array
            else:
                raise NotImplementedError(
                    f"get_all_values only implemented for {type(expression)} expression type."
                )

            temp_cs.add(var == expression)
            self._reset(temp_cs.to_string())
            result = []
            start = time.time()
            while self._is_sat():
                value = self._getvalue(var)
                result.append(value)

                if len(result) >= maxcnt:
                    if silent:
                        # do not throw an exception if set to silent
                        # Default is not silent, assume user knows
                        # what they are doing and will check the size
                        # of returned vals list (previous smtlib behavior)
                        break
                    else:
                        raise TooManySolutions(result)
                if time.time() - start > consts.timeout:
                    if silent:
                        logger.info("Timeout searching for all solutions")
                        return list(result)
                    raise SolverError("Timeout")
                # Sometimes adding a new contraint after a check-sat eats all the mem
                if self._multiple_check:
                    self._smtlib.send(f"(assert {translate_to_smtlib(var != value)})")
                else:
                    temp_cs.add(var != value)
                    self._reset(temp_cs.to_string())
            return list(result)

    def _optimize_fancy(self, constraints: ConstraintSet, x: BitVec, goal: str, max_iter=10000):
        """
        Iteratively finds the maximum or minimum value for the operation
        (Normally Operators.UGT or Operators.ULT)

        :param constraints: constraints to take into account
        :param x: a symbol or expression
        :param goal: goal to achieve, either 'maximize' or 'minimize'
        :param max_iter: maximum number of iterations allowed
        """
        # TODO: consider adding a mode to return best known value on timeout
        assert goal in ("maximize", "minimize")
        operation = {"maximize": Operators.UGE, "minimize": Operators.ULE}[goal]

        with constraints as temp_cs:
            X = temp_cs.new_bitvec(x.size)
            temp_cs.add(X == x)
            aux = temp_cs.new_bitvec(X.size, name="optimized_")
            self._reset(temp_cs.to_string())

            self._assert(operation(X, aux))
            self._smtlib.send("(%s %s)" % (goal, aux.name))
            self._smtlib.send("(check-sat)")
            _status = self._smtlib.recv()
            if _status == "sat":
                return self._getvalue(aux)
            raise SolverError("Optimize failed")

    def get_value(self, constraints: ConstraintSet, *expressions):
        """
        Ask the solver for one possible result of given expressions using
        given set of constraints.
        """
        values = []
        start = time.time()
        with constraints.related_to(*expressions) as temp_cs:
            for expression in expressions:
                if not issymbolic(expression):
                    values.append(expression)
                    continue
                assert isinstance(expression, (Bool, BitVec, Array))
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
                    self._reset(temp_cs.to_string())
                    if not self._is_sat():
                        raise SolverError(
                            "Solver could not find a value for expression under current constraint set"
                        )

                    for i in range(expression.index_max):
                        result.append(self.__getvalue_bv(var[i].name))
                    values.append(bytes(result))
                    if time.time() - start > consts.timeout:
                        raise SolverError("Timeout")
                    continue

                temp_cs.add(var == expression)

                self._reset(temp_cs.to_string())

                if not self._is_sat():
                    raise SolverError(
                        "Solver could not find a value for expression under current constraint set"
                    )

                if isinstance(expression, Bool):
                    values.append(self.__getvalue_bool(var.name))
                if isinstance(expression, BitVec):
                    values.append(self.__getvalue_bv(var.name))
            if time.time() - start > consts.timeout:
                raise SolverError("Timeout")

        if len(expressions) == 1:
            return values[0]
        else:
            return values


class Z3Solver(SMTLIBSolver):
    def __init__(self):
        """
        Build a Z3 solver instance.
        This is implemented using an external z3 solver (via a subprocess).
        See https://github.com/Z3Prover/z3
        """
        command = f"{consts.z3_bin} -t:{consts.timeout * 1000} -memory:{consts.memory} -smt2 -in"

        init, support_minmax, support_reset, multiple_check = self.__autoconfig()
        super().__init__(
            command=command,
            init=init,
            value_fmt=16,
            support_minmax=support_minmax,
            support_reset=support_reset,
            multiple_check=multiple_check,
            support_pushpop=True,
            debug=False,
        )

    def __autoconfig(self):
        init = [
            # http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_AUFBV
            # Closed quantifier-free formulas over the theory of bitvectors and bitvector arrays extended with
            # free sort and function symbols.
            "(set-logic QF_AUFBV)",
            # The declarations and definitions will be scoped
            "(set-option :global-decls false)",
        ]

        # To cache what get-info returned; can be directly set when writing tests
        self.version = self._solver_version()
        support_reset = True

        if self.version > Version(4, 8, 4):
            # sam.moelius: Option "tactic.solve_eqs.context_solve" was turned on by this commit in z3:
            #   https://github.com/Z3Prover/z3/commit/3e53b6f2dbbd09380cd11706cabbc7e14b0cc6a2
            # Turning it off greatly improves Manticore's performance on test_integer_overflow_storageinvariant
            # in test_consensys_benchmark.py.
            init.append("(set-option :tactic.solve_eqs.context_solve false)")

        support_minmax = self.version >= Version(4, 4, 1)

        # Certain version of Z3 fails to handle multiple check-sat
        # https://gist.github.com/feliam/0f125c00cb99ef05a6939a08c4578902
        multiple_check = self.version < Version(4, 8, 7)
        return init, support_minmax, support_reset, multiple_check

    def _solver_version(self) -> Version:
        """
        If we fail to parse the version, we assume z3's output has changed, meaning it's a newer
        version than what's used now, and therefore ok.

        Anticipated version_cmd_output format: 'Z3 version 4.4.2'
                                               'Z3 version 4.4.5 - 64 bit - build hashcode $Z3GITHASH'
        """
        try:
            received_version = check_output([f"{consts.z3_bin}", "--version"])
            Z3VERSION = re.compile(
                r".*(?P<major>([0-9]+))\.(?P<minor>([0-9]+))\.(?P<patch>([0-9]+)).*"
            )
            m = Z3VERSION.match(received_version.decode("utf-8"))
            major, minor, patch = map(
                int, (m.group("major"), m.group("minor"), m.group("patch"))  # type: ignore
            )
            parsed_version = Version(major, minor, patch)
        except (ValueError, TypeError) as e:
            logger.warning(
                f"Could not parse Z3 version: '{str(received_version)}'. Assuming compatibility."
            )
            parsed_version = Version(float("inf"), float("inf"), float("inf"))
        return parsed_version


class YicesSolver(SMTLIBSolver):
    def __init__(self):
        init = ["(set-logic QF_AUFBV)"]
        command = f"{consts.yices_bin} --timeout={consts.timeout}  --incremental"
        super().__init__(
            command=command,
            init=init,
            value_fmt=2,
            debug=False,
            support_minmax=False,
            support_reset=False,
        )


class CVC4Solver(SMTLIBSolver):
    def __init__(self):
        init = ["(set-logic QF_AUFBV)", "(set-option :produce-models true)"]
        command = f"{consts.cvc4_bin} --lang=smt2 --incremental"
        super().__init__(command=command, value_fmt=10, init=init)


class SelectedSolver:
    choice = None

    @classmethod
    def instance(cls):
        if consts.solver == consts.solver.auto:
            if cls.choice is None:
                if shutil.which(consts.yices_bin):
                    cls.choice = consts.solver.yices
                elif shutil.which(consts.z3_bin):
                    cls.choice = consts.solver.z3
                elif shutil.which(consts.cvc4_bin):
                    cls.choice = consts.solver.cvc4
                else:
                    raise SolverException(
                        f"No Solver not found. Install one ({consts.yices_bin}, {consts.z3_bin}, {consts.cvc4_bin})."
                    )
        else:
            cls.choice = consts.solver

        SelectedSolver = {"cvc4": CVC4Solver, "yices": YicesSolver, "z3": Z3Solver}[cls.choice.name]
        return SelectedSolver.instance()
