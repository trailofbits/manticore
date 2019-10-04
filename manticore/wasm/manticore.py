import logging
import os
import time

from .state import State
from ..core.manticore import ManticoreBase
from ..core.smtlib import ConstraintSet, issymbolic, Z3Solver
from .types import I32, I64

logger = logging.getLogger(__name__)


class ManticoreWASM(ManticoreBase):
    """
    Manticore class for interacting with WASM, analagous to ManticoreNative or ManticoreEVM.
    """

    def __init__(self, path_or_state, env={}, workspace_url=None, policy="random", **kwargs):
        """
        :param path_or_state: Path to binary or a state (object) to begin from.
        :param argv: arguments passed to the binary.
        """
        if isinstance(path_or_state, str):
            if not os.path.isfile(path_or_state):
                raise OSError(f"{path_or_state} is not an existing regular file")
            initial_state = _make_initial_state(path_or_state, env, **kwargs)
        else:
            initial_state = path_or_state

        super().__init__(initial_state, workspace_url=workspace_url, policy=policy, **kwargs)

        self.subscribe("will_terminate_state", self._terminate_state_callback)

    def run(self, timeout=None):
        """
        Begins the Manticore run

        :param timeout: number of seconds after which to kill execution
        """
        with self.locked_context() as context:
            context["time_started"] = time.time()

        super().run(timeout=timeout)

    def finalize(self):
        """
        Finish a run and solve for test cases. TODO: do more than just dump pickled states
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

    @ManticoreBase.at_not_running
    def invoke(self, name="main", argv_generator=lambda s: []):
        """
        Maps the "invoke" command over all the ready states
        :param name: The function to invoke
        :param argv_generator: A function that takes the current state and returns a list of arguments
        """
        for state in self.ready_states:
            state.platform.invoke(name=name, argv=argv_generator(state))

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
                                for a in Z3Solver.instance().get_all_values(state.constraints, ret)
                            )
                        )
                    elif ret.size == 64:
                        inner.append(
                            list(
                                I64(
                                    a
                                )  # TODO - that'll probably require us to subclass bitvecs into IxxBV and FxxBV
                                for a in Z3Solver.instance().get_all_values(state.constraints, ret)
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


def _make_initial_state(binary_path, env={}, **kwargs):
    """
    Wraps _make_wasm_bin

    :param binary_path:
    :param env:
    :param kwargs:
    :return:
    """
    if binary_path.endswith(".wasm"):
        return _make_wasm_bin(binary_path, env=env, **kwargs)


def _make_wasm_bin(program, env={}, **kwargs) -> State:
    """
    Returns an initial state for a binary WASM module
    
    :param program: filenamae of the wasm module
    :param env: Import dict
    :return: initial state
    """
    from ..platforms import wasm

    logger.info("Loading program %s", program)

    constraints = kwargs.get("constraints", ConstraintSet())
    platform = wasm.WASMWorld(program, constraints=constraints)
    platform.instantiate(env, exec_start=kwargs.get("exec_start", False))
    initial_state = State(constraints, platform)

    return initial_state
