import logging
import os
import time
import typing

from .state import State
from ..core.manticore import ManticoreBase
from ..core.smtlib import ConstraintSet, issymbolic, SelectedSolver
from .types import I32, I64, F32, F64
from .structure import FuncInst

logger = logging.getLogger(__name__)


class ManticoreWASM(ManticoreBase):
    """
    Manticore class for interacting with WASM, analagous to ManticoreNative or ManticoreEVM.
    """

    def __init__(
        self, path_or_state, env={}, sup_env={}, workspace_url=None, policy="random", **kwargs
    ):
        """
        :param path_or_state: Path to binary or a state (object) to begin from.
        :param env: Dict of imports to place under the "env" module
        :param sup_env: Maps module names to import dicts (a la {"env":{}})
        """
        if isinstance(path_or_state, str):
            if not os.path.isfile(path_or_state):
                raise OSError(f"{path_or_state} is not an existing regular file")
            initial_state = _make_initial_state(path_or_state, env, sup_env, **kwargs)
        else:
            initial_state = path_or_state

        self.exported_functions = (
            initial_state._platform.module.get_funcnames()
        )  #: List of exported function names in the default module

        super().__init__(initial_state, workspace_url=workspace_url, policy=policy, **kwargs)

        self.subscribe("will_terminate_state", self._terminate_state_callback)

    def run(self, timeout=None):
        """
        Begins the Manticore run

        :param timeout: number of seconds after which to kill execution
        """
        with self.locked_context() as context:
            context["time_started"] = time.time()

        with self.kill_timeout(timeout):
            super().run()

    def finalize(self):
        """
        Finish a run and solve for test cases.
        Calls save_run_data
        """
        super().finalize()
        self.save_run_data()

    def save_run_data(self):
        super().save_run_data()

        time_ended = time.time()

        with self.locked_context() as context:
            time_elapsed = time_ended - context["time_started"]

            logger.info("Total time: %s", time_elapsed)

            context["time_ended"] = time_ended
            context["time_elapsed"] = time_elapsed

    def __getattr__(self, item):
        """
        Allows users to invoke & run functions in the same style as ethereum smart contracts. So:
        `m.invoke("collatz", arg_gen); m.run()` becomes `m.collatz(arg_gen)`.
        :param item: Name of the function to call
        :return: A function that, when called, will invoke and run the target function.
        """
        if item not in self.exported_functions:
            raise AttributeError(f"Can't find a WASM function called {item}")

        def f(argv_generator=None):
            with self.locked_context("wasm.saved_states", list) as saved_states:
                while saved_states:
                    state_id = saved_states.pop()
                    self._terminated_states.remove(state_id)
                    self._ready_states.append(state_id)

            if argv_generator is not None:
                self.invoke(item, argv_generator)
            else:
                self.invoke(item)
            self.run()

        return f

    @ManticoreBase.at_not_running
    def invoke(self, name="main", argv_generator=lambda s: []):
        """
        Maps the "invoke" command over all the ready states
        :param name: The function to invoke
        :param argv_generator: A function that takes the current state and returns a list of arguments
        """
        for state in self.ready_states:
            args = argv_generator(state)
            logger.info("Invoking: %s(%s)", name, ", ".join(str(a) for a in args))
            state.platform.invoke(name=name, argv=args)

    @ManticoreBase.at_not_running
    def default_invoke(self, func_name: str = "main"):
        """
        Looks for a `main` function or `start` function and invokes it with symbolic arguments
        :param func_name: Optional name of function to look for
        """
        funcs = [func_name]
        if "main" not in func_name:
            funcs.append("main")

        state = next(self.ready_states)
        for name in funcs:
            func_inst: typing.Optional[FuncInst] = state.platform.get_export(name)
            if isinstance(func_inst, FuncInst):
                func_ty = func_inst.type

                args = []
                for idx, ty in enumerate(func_ty.param_types):
                    if ty in {I32, F32}:
                        args.append(state.new_symbolic_value(32, f"arg{idx}_{ty.__name__}"))
                    elif ty in {I64, F64}:
                        args.append(state.new_symbolic_value(64, f"arg{idx}_{ty.__name__}"))

                self.invoke(name=name, argv_generator=lambda s: args)
                break

    @ManticoreBase.at_not_running
    def collect_returns(self, n=1):
        """
        Iterates over the terminated states and collects the top n values from the stack.
        Generally only used for testing.

        :param n: Number of values to collect
        :return: A list of list of lists.
            > One list for each state
                > One list for each n
                    > The output from solver.get_all_values
        """
        outer = []
        for state in self.terminated_states:
            inner = []
            p = state.platform
            for _i in range(n):
                ret = None
                if not p.stack.empty():
                    ret = p.stack.pop()
                if issymbolic(ret):
                    if ret.size == 32:
                        inner.append(
                            list(
                                I32(a)  # TODO - eventually we'll need to support floats as well.
                                for a in SelectedSolver.instance().get_all_values(
                                    state.constraints, ret
                                )
                            )
                        )
                    elif ret.size == 64:
                        inner.append(
                            list(
                                I64(
                                    a
                                )  # TODO - that'll probably require us to subclass bitvecs into IxxBV and FxxBV
                                for a in SelectedSolver.instance().get_all_values(
                                    state.constraints, ret
                                )
                            )
                        )
                else:
                    inner.append([ret])
            outer.append(inner)
        return outer

    def _terminate_state_callback(self, state, e):
        """
        Adds state to the wasm.saved_states list

        :param state: the terminated state
        :param e: any exception raised
        """
        with self.locked_context("wasm.saved_states", list) as saved_states:
            saved_states.append(state.id)

    @ManticoreBase.at_not_running
    def _reinit(self):
        """
        Moves terminated states back into the ready states list. Only used for testing, may promote to
        a part of the official API in the future.
        """
        # If there are ready states still then it was a paused execution
        assert not self._ready_states
        assert not self._busy_states

        with self.locked_context("wasm.saved_states", list) as saved_states:
            while saved_states:
                state_id = saved_states.pop()
                self._terminated_states.remove(state_id)
                self._ready_states.append(state_id)

    def generate_testcase(self, state, message="test", name="test"):
        testcase = super().generate_testcase(state, message)
        self._output.save_input_symbols(testcase, state)

        with testcase.open_stream("stack") as stackf:
            stackf.write(str(state.stack.data))

        with testcase.open_stream("memory") as memoryf:
            memoryf.write(str(state.mem.dump()))

        term = getattr(state, "_terminated_by", None)
        if term:
            with testcase.open_stream("status") as summary:
                summary.write(f"{str(term)}\n\n")


def _make_initial_state(binary_path, env={}, sup_env={}, **kwargs) -> State:
    """
    Wraps _make_wasm_bin

    :param binary_path: filename of the wasm module
    :param env: Import dict
    :param sup_env: Maps module names to import dicts (a la {"env":{}})
    :param kwargs:
    :return: initial state
    """
    if binary_path.endswith(".wasm"):
        return _make_wasm_bin(binary_path, env=env, sup_env=sup_env, **kwargs)
    raise RuntimeError("ManticoreWASM only supports .wasm files at the moment")


def _make_wasm_bin(program, env={}, sup_env={}, **kwargs) -> State:
    """
    Returns an initial state for a binary WASM module

    :param program: filename of the wasm module
    :param env: Import dict
    :param sup_env: Maps module names to import dicts (a la {"env":{}})
    :return: initial state
    """
    from ..platforms import wasm

    logger.info("Loading program %s", program)

    constraints = kwargs.get("constraints", ConstraintSet())
    platform = wasm.WASMWorld(program, constraints=constraints)
    platform.instantiate(
        env,
        sup_env,
        exec_start=kwargs.get("exec_start", False),
        stub_missing=kwargs.get("stub_missing", True),
    )
    initial_state = State(constraints, platform)

    return initial_state
