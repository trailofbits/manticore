import logging
import os
import time
import functools

from .state import State
from ..core.manticore import ManticoreBase
from ..core.smtlib import ConstraintSet, issymbolic, Z3Solver

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
    def invoke(self, name="main", argv=[]):
        for state in self.ready_states:
            state.platform.invoke(name=name, argv=argv)

    @ManticoreBase.at_not_running
    def collect_returns(self):
        out = []
        for state in self.terminated_states:
            p = state.platform
            ret = None
            if not p.stack.empty():
                ret = p.stack.pop()
                if issymbolic(ret):
                    out.append(list(Z3Solver.instance().get_all_values(state.constraints, ret)))
                else:
                    out.append([ret])
        return out


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
