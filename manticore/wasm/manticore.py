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
        with self.locked_context() as context:
            context["time_started"] = time.time()

        super().run(timeout=timeout)

    def finalize(self):
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
        for state in self.ready_states:
            state.platform.invoke(name=name, argv=argv_generator(state))

    @ManticoreBase.at_not_running
    def collect_returns(self):
        out = []
        for state in self.terminated_states:
            p = state.platform
            ret = None
            if not p.stack.empty():
                ret = p.stack.pop()
                if issymbolic(ret):
                    if ret.size == 32:
                        out.append(
                            list(
                                I32(a)
                                for a in Z3Solver.instance().get_all_values(state.constraints, ret)
                            )
                        )
                    elif ret.size == 64:
                        out.append(
                            list(
                                I64(a)
                                for a in Z3Solver.instance().get_all_values(state.constraints, ret)
                            )
                        )
                else:
                    out.append([ret])
        return out

    def _terminate_state_callback(self, state, e):
        with self.locked_context("wasm.saved_states", list) as saved_states:
            saved_states.append(state.id)

    @ManticoreBase.at_not_running
    def _reinit(self):
        # If there are ready states still then it was a paused execution
        assert not self._ready_states
        assert not self._busy_states

        with self.locked_context("wasm.saved_states", list) as saved_states:
            while saved_states:
                state_id = saved_states.pop()
                self._terminated_states.remove(state_id)
                self._ready_states.append(state_id)


def _make_initial_state(binary_path, env={}, **kwargs):
    if binary_path.endswith(".wasm"):
        return _make_wasm_bin(binary_path, **kwargs)


def _make_wasm_bin(program, env={}, **kwargs):
    from ..platforms import wasm

    logger.info("Loading program %s", program)

    constraints = ConstraintSet()
    platform = wasm.WASMWorld(program, constraints=constraints)
    platform.instantiate(env, exec_start=kwargs.get("exec_start", False))
    initial_state = State(constraints, platform)

    return initial_state
