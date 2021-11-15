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

import collections
import fcntl
import os
import shlex
import shutil
import time
from abc import abstractmethod
from random import shuffle
from subprocess import PIPE, Popen, check_output
from typing import Any, Sequence, List

from . import operators as Operators
from .constraints import *
from .visitors import *
from ...exceptions import SolverError, SolverUnknown, TooManySolutions, SmtlibError
from ...utils import config

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
consts.add("boolector_bin", default="boolector", description="Boolector solver binary to use")


consts.add("defaultunsat", default=True, description="Consider solver timeouts as unsat core")
consts.add(
    "optimize", default=True, description="Use smtlib command optimize to find min/max if available"
)

# Regular expressions used by the solver
RE_GET_EXPR_VALUE_ALL = re.compile(
    r"\(([a-zA-Z0-9_]*)[ \n\s]*(#b[0-1]*|#x[0-9a-fA-F]*|[(]?_ bv[0-9]* [0-9]*|true|false)\)"
)
RE_GET_EXPR_VALUE_FMT_BIN = re.compile(r"\(\((?P<expr>(.*))[ \n\s]*#b(?P<value>([0-1]*))\)\)")
RE_GET_EXPR_VALUE_FMT_DEC = re.compile(r"\(\((?P<expr>(.*))\ \(_\ bv(?P<value>(\d*))\ \d*\)\)\)")
RE_GET_EXPR_VALUE_FMT_HEX = re.compile(r"\(\((?P<expr>(.*))\ #x(?P<value>([0-9a-fA-F]*))\)\)")
RE_OBJECTIVES_EXPR_VALUE = re.compile(
    r"\(objectives.*\((?P<expr>.*) (?P<value>\d*)\).*\).*", re.MULTILINE | re.DOTALL
)
RE_MIN_MAX_OBJECTIVE_EXPR_VALUE = re.compile(r"(?P<expr>.*?)\s+\|->\s+(?P<value>.*)", re.DOTALL)

SOLVER_STATS = {"unknown": 0, "timeout": 0}


class SolverType(config.ConfigEnum):
    """Used as configuration constant for choosing solver flavor"""

    z3 = "z3"
    cvc4 = "cvc4"
    yices = "yices"
    auto = "auto"
    portfolio = "portfolio"
    boolector = "boolector"


consts.add(
    "solver",
    default=SolverType.auto,
    description="Choose default smtlib2 solver (z3, yices, cvc4, boolector, portfolio, auto)",
)


def _convert(v):
    r = None
    if v == "true":
        r = True
    elif v == "false":
        r = False
    elif v.startswith("#b"):
        r = int(v[2:], 2)
    elif v.startswith("#x"):
        r = int(v[2:], 16)
    elif v.startswith("_ bv"):
        r = int(v[len("_ bv") : -len(" 256")], 10)
    elif v.startswith("(_ bv"):
        v = v[len("(_ bv") :]
        r = int(v[: v.find(" ")], 10)

    assert r is not None
    return r


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
        """Single smtlib interactive process

        :param command: the shell command to execute
        :param debug: log all messaging
        """
        self._proc: Optional[Popen] = None
        self._command = command
        self._debug = debug
        self._last_buf = ""

    def start(self):
        """Spawns POpen solver process"""
        if self._proc is not None:
            return
        self._proc = Popen(
            shlex.split(self._command),
            stdin=PIPE,
            stdout=PIPE,
            # bufsize=0,  # if we set input to unbuffered, we get syntax errors in large formulas
            universal_newlines=True,
            close_fds=True,
        )

        # stdout should be non-blocking
        fl = fcntl.fcntl(self._proc.stdout, fcntl.F_GETFL)
        fcntl.fcntl(self._proc.stdout, fcntl.F_SETFL, fl | os.O_NONBLOCK)
        self._last_buf = ""

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

    def send(self, cmd: str) -> None:
        """
        Send a string to the solver.

        :param cmd: a SMTLIBv2 command (ex. (check-sat))
        """
        if self._debug:
            logger.debug(">%s", cmd)
        assert self._proc is not None
        try:
            self._proc.stdout.flush()  # type: ignore
            self._proc.stdin.write(f"{cmd}\n")  # type: ignore
            self._proc.stdin.flush()  # type: ignore
        except (BrokenPipeError, IOError) as e:
            logger.critical(
                f"Solver encountered an error trying to send commands: {e}.\n"
                f"\tOutput: {self._proc.stdout}\n\n"
                f"\tStderr: {self._proc.stderr}"
            )
            raise e

    def recv(self, wait=True) -> Optional[str]:
        """Reads the response from the smtlib solver

        :param wait: a boolean that indicate to wait with a blocking call
        until the results are available. Otherwise, it returns None if the solver
        does not respond.

        """
        tries = 0
        timeout = 0.0

        buf = ""
        if self._last_buf != "":  # we got a partial response last time, let's use it
            buf = buf + self._last_buf

        while True:
            try:
                buf = buf + self._proc.stdout.read()  # type: ignore
                buf = buf.strip()
            except TypeError:
                if not wait:
                    if buf != "":  # we got an error, but something was returned, let's save it
                        self._last_buf = buf
                    return None
                else:
                    tries += 1

            if buf == "":
                continue

            # this verifies if the response from the solver is complete (it has balanced brackets)
            lparen, rparen = map(sum, zip(*((c == "(", c == ")") for c in buf)))
            if lparen == rparen and buf != "":
                break

            if tries > 3:
                time.sleep(timeout)
                timeout += 0.1

        buf = buf.strip()
        self._last_buf = ""

        if "(error" in buf:
            raise SolverException(f"Solver error: {buf}")

        if self._debug:
            logger.debug("<%s", buf)

        return buf

    def _restart(self) -> None:
        """Auxiliary to start or restart the external solver"""
        self.stop()
        self.start()

    def is_started(self):
        return self._proc is not None

    def clear_buffers(self):
        self._proc.stdout.flush()
        self._proc.stdin.flush()


class SMTLIBSolver(Solver):
    ncores: Optional[int] = None
    sname: Optional[str] = None

    @classmethod
    @abstractmethod
    def command(self) -> str:
        raise NotImplementedError()

    @classmethod
    @abstractmethod
    def inits(self) -> List[str]:
        raise NotImplementedError()

    def __init__(
        self,
        command: str,
        init: Sequence[str] = None,
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

        self._smtlib.clear_buffers()

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
        assert status is not None
        logger.debug("Check took %s seconds (%s)", time.time() - start, status)
        if "ALARM TRIGGERED" in status:
            return False

        if status not in ("sat", "unsat", "unknown"):
            raise SolverError(status)
        if consts.defaultunsat:
            if status == "unknown":
                logger.info("Found an unknown core, probably a solver timeout")
                SOLVER_STATS["timeout"] += 1
                status = "unsat"
                raise SolverUnknown(status)

        if status == "unknown":
            SOLVER_STATS["unknown"] += 1
            raise SolverUnknown(status)
        else:
            assert self.sname is not None
            SOLVER_STATS.setdefault(self.sname, 0)
            SOLVER_STATS[self.sname] += 1

        return status == "sat"

    def _assert(self, expression: Bool):
        """Auxiliary method to send an assert"""
        smtlib = translate_to_smtlib(expression)
        self._smtlib.send(f"(assert {smtlib})")

    def __getvalue_bv(self, expression_str: str) -> int:
        self._smtlib.send(f"(get-value ({expression_str}))")
        t = self._smtlib.recv()
        assert t is not None
        base = 2
        m = RE_GET_EXPR_VALUE_FMT_BIN.match(t)
        if m is None:
            m = RE_GET_EXPR_VALUE_FMT_DEC.match(t)
            base = 10
        if m is None:
            m = RE_GET_EXPR_VALUE_FMT_HEX.match(t)
            base = 16
        if m is None:
            raise SolverError(f"I don't know how to parse the value {str(t)} from {expression_str}")

        expr, value = m.group("expr"), m.group("value")  # type: ignore
        return int(value, base)

    def __getvalue_bool(self, expression_str):
        self._smtlib.send(f"(get-value ({expression_str}))")
        ret = self._smtlib.recv()
        return {"true": True, "false": False, "#b0": False, "#b1": True}[ret[2:-2].split(" ")[1]]

    def __getvalue_all(self, expressions_str: List[str], is_bv: List[bool]) -> Dict[str, int]:
        all_expressions_str = " ".join(expressions_str)
        self._smtlib.send(f"(get-value ({all_expressions_str}))")
        ret_solver: Optional[str] = self._smtlib.recv()
        assert ret_solver is not None
        return_values = re.findall(RE_GET_EXPR_VALUE_ALL, ret_solver)
        return {value[0]: _convert(value[1]) for value in return_values}

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
                    SOLVER_STATS["timeout"] += 1
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
                    SOLVER_STATS["unknown"] += 1
                    raise SolverError("Optimizing error, maximum number of iterations was reached")
                if time.time() - start > consts.timeout:
                    SOLVER_STATS["timeout"] += 1
                    raise SolverError("Timeout")
            if last_value is not None:
                return last_value

            SOLVER_STATS["unknown"] += 1
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
                    SOLVER_STATS["timeout"] += 1
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

            assert self.sname is not None
            SOLVER_STATS.setdefault(self.sname, 0)
            SOLVER_STATS[self.sname] += 1

            if _status == "sat":
                return self._getvalue(aux)
            raise SolverError("Optimize failed")

    def get_value(self, constraints: ConstraintSet, *expressions):
        values = self.get_value_in_batch(constraints, expressions)
        if len(expressions) == 1:
            return values[0]
        else:
            return values

    def get_value_in_batch(self, constraints: ConstraintSet, expressions):
        """
        Ask the solver for one possible result of given expressions using
        given set of constraints.
        """
        values: List[Any] = [None] * len(expressions)
        start = time.time()
        with constraints.related_to(*expressions) as temp_cs:
            vars: List[Any] = []
            for idx, expression in enumerate(expressions):
                if not issymbolic(expression):
                    values[idx] = expression
                    vars.append(None)
                    continue
                assert isinstance(expression, (Bool, BitVec, Array))
                if isinstance(expression, Bool):
                    var = temp_cs.new_bool()
                    vars.append(var)
                    temp_cs.add(var == expression)
                elif isinstance(expression, BitVec):
                    var = temp_cs.new_bitvec(expression.size)
                    vars.append(var)
                    temp_cs.add(var == expression)
                elif isinstance(expression, Array):
                    var = []
                    for i in range(expression.index_max):
                        subvar = temp_cs.new_bitvec(expression.value_bits)
                        var.append(subvar)
                        temp_cs.add(subvar == simplify(expression[i]))
                    vars.append(var)

            self._reset(temp_cs.to_string())
            if not self._is_sat():
                raise SolverError(
                    "Solver could not find a value for expression under current constraint set"
                )

            values_to_ask: List[str] = []
            is_bv: List[bool] = []
            for idx, expression in enumerate(expressions):
                if not issymbolic(expression):
                    continue
                var = vars[idx]
                if isinstance(expression, Bool):
                    values_to_ask.append(var.name)
                    is_bv.append(False)
                if isinstance(expression, BitVec):
                    values_to_ask.append(var.name)
                    is_bv.append(True)
                if isinstance(expression, Array):
                    # result = []
                    for i in range(expression.index_max):
                        values_to_ask.append(var[i].name)
                        is_bv.append(True)

            if values_to_ask == []:
                return values

            values_returned = self.__getvalue_all(values_to_ask, is_bv)
            for idx, expression in enumerate(expressions):
                if not issymbolic(expression):
                    continue
                var = vars[idx]
                if isinstance(expression, Bool):
                    values[idx] = values_returned[var.name]
                if isinstance(expression, BitVec):
                    if var.name not in values_returned:
                        logger.error(
                            "var.name", var.name, "not in values_returned", values_returned
                        )

                    values[idx] = values_returned[var.name]
                if isinstance(expression, Array):
                    result = []
                    for i in range(expression.index_max):
                        result.append(values_returned[var[i].name])
                    values[idx] = bytes(result)

            if time.time() - start > consts.timeout:
                SOLVER_STATS["timeout"] += 1
                raise SolverError("Timeout")

        return values


class Z3Solver(SMTLIBSolver):
    sname = "z3"

    @classmethod
    def command(self) -> str:
        return f"{consts.z3_bin} -t:{consts.timeout * 1000} -memory:{consts.memory} -smt2 -in"

    @classmethod
    def inits(self) -> List[str]:
        return [
            "(set-logic QF_AUFBV)",
            "(set-option :global-decls false)",
            "(set-option :tactic.solve_eqs.context_solve false)",
        ]

    def __init__(self):
        """
        Build a Z3 solver instance.
        This is implemented using an external z3 solver (via a subprocess).
        See https://github.com/Z3Prover/z3
        """
        command = self.command()
        self.ncores = 1

        init, support_minmax, support_reset, multiple_check = self.__autoconfig()
        super().__init__(
            command=command,
            init=init,
            support_minmax=support_minmax,
            support_reset=support_reset,
            multiple_check=multiple_check,
            support_pushpop=True,
            debug=False,
        )

    def __autoconfig(self):
        init = self.inits()

        # To cache what get-info returned; can be directly set when writing tests
        self.version = self._solver_version()
        support_reset = True

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
    sname = "yices"

    @classmethod
    def command(self) -> str:
        return f"{consts.yices_bin} --timeout={consts.timeout}  --incremental"

    @classmethod
    def inits(self) -> List[str]:
        return ["(set-logic QF_AUFBV)"]

    def __init__(self):
        init = self.inits()
        command = self.command()
        self.ncores = 1
        super().__init__(
            command=command,
            init=init,
            debug=False,
            support_minmax=False,
            support_reset=False,
        )


class CVC4Solver(SMTLIBSolver):
    sname = "cvc4"

    @classmethod
    def command(self) -> str:
        return f"{consts.cvc4_bin} --tlimit={consts.timeout * 1000} --lang=smt2 --incremental"

    @classmethod
    def inits(self) -> List[str]:
        return ["(set-logic QF_AUFBV)", "(set-option :produce-models true)"]

    def __init__(self):
        init = self.inits()
        command = self.command()
        self.ncores = 1
        super().__init__(command=command, init=init)


class BoolectorSolver(SMTLIBSolver):
    sname = "boolector"

    @classmethod
    def command(self) -> str:
        return f"{consts.boolector_bin} --time={consts.timeout} -i"

    @classmethod
    def inits(self) -> List[str]:
        return ["(set-logic QF_AUFBV)", "(set-option :produce-models true)"]

    def __init__(self, args: List[str] = []):
        init = self.inits()
        command = self.command()
        self.ncores = 1
        super().__init__(command=command, init=init)


class SmtlibPortfolio:
    def __init__(self, solvers: List[str], debug: bool = False):
        """Single smtlib interactive process

        :param command: the shell command to execute
        :param debug: log all messaging
        """
        self._procs: Dict[str, SmtlibProc] = {}
        self._solvers: List[str] = solvers
        self._debug = debug

    def start(self):
        if len(self._procs) == 0:
            for solver in self._solvers:
                self._procs[solver] = SmtlibProc(solver_selector[solver].command(), self._debug)

        for _, proc in self._procs.items():
            proc.start()

    def stop(self):
        """
        Stops the solver process by:
        - sending a SIGKILL signal,
        - waiting till the process terminates (so we don't leave a zombie process)
        """
        for solver, proc in self._procs.items():
            proc.stop()

    def send(self, cmd: str) -> None:
        """
        Send a string to the solver.

        :param cmd: a SMTLIBv2 command (ex. (check-sat))
        """
        assert len(self._procs) > 0
        inds = list(range(len(self._procs)))
        shuffle(inds)

        for i in inds:
            solver = self._solvers[i]
            proc = self._procs[solver]
            if not proc.is_started():
                continue

            proc.send(cmd)

    def recv(self) -> str:
        """Reads the response from the smtlib solver"""
        tries = 0
        timeout = 0.0
        inds = list(range(len(self._procs)))
        # print(self._solvers)
        while True:
            shuffle(inds)
            for i in inds:

                solver = self._solvers[i]
                proc = self._procs[solver]

                if not proc.is_started():
                    continue

                buf = proc.recv(wait=False)
                if buf is not None:

                    for osolver in self._solvers:  # iterate on all the solvers
                        if osolver != solver:  # check for the other ones
                            self._procs[osolver].stop()  # stop them

                    return buf
                else:
                    tries += 1

            if tries > 10 * len(self._procs):
                time.sleep(timeout)
                timeout += 0.1

    def _restart(self) -> None:
        """Auxiliary to start or restart the external solver"""
        self.stop()
        self.start()

    def is_started(self):
        return len(self._procs) > 0

    def init(self):
        assert len(self._solvers) == len(self._procs)
        for solver, proc in self._procs.items():
            for cfg in solver_selector[solver].inits():
                proc.send(cfg)


class PortfolioSolver(SMTLIBSolver):
    sname = "portfolio"

    def __init__(self):
        solvers = []
        if shutil.which(consts.yices_bin):
            solvers.append(consts.solver.yices.name)
        # not sure we want z3 here, since it tends to be slower
        # if shutil.which(consts.z3_bin):
        #    solvers.append(consts.solver.z3.name)
        if shutil.which(consts.cvc4_bin):
            solvers.append(consts.solver.cvc4.name)
        if shutil.which(consts.boolector_bin):
            solvers.append(consts.solver.boolector.name)
        if solvers == []:
            raise SolverException(
                f"No Solver not found. Install one ({consts.yices_bin}, {consts.z3_bin}, {consts.cvc4_bin}, {consts.boolector_bin})."
            )

        logger.info("Creating portfolio with solvers: " + ",".join(solvers))
        assert len(solvers) > 0
        support_reset: bool = False
        support_minmax: bool = False
        support_pushpop: bool = False
        multiple_check: bool = True
        debug: bool = False

        self._smtlib: SmtlibPortfolio = SmtlibPortfolio(solvers, debug)
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
        self.ncores = len(solvers)

    def _reset(self, constraints: Optional[str] = None) -> None:
        """Auxiliary method to reset the smtlib external solver to initial defaults"""
        if self._support_reset:
            self._smtlib.start()  # does not do anything if already started
            self._smtlib.send("(reset)")
        else:
            self._smtlib.stop()  # does not do anything if already stopped
            self._smtlib.start()

        self._smtlib.init()

        if constraints is not None:
            self._smtlib.send(constraints)


solver_selector = {
    "cvc4": CVC4Solver,
    "boolector": BoolectorSolver,
    "yices": YicesSolver,
    "z3": Z3Solver,
    "portfolio": PortfolioSolver,
}


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
                elif shutil.which(consts.boolector_bin):
                    cls.choice = consts.solver.boolector
                else:
                    raise SolverException(
                        f"No Solver not found. Install one ({consts.yices_bin}, {consts.z3_bin}, {consts.cvc4_bin}, {consts.boolector_bin})."
                    )

        else:
            cls.choice = consts.solver

        SelectedSolver = solver_selector[cls.choice.name]
        return SelectedSolver.instance()
