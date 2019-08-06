import logging
import os
import time
import functools

from .state import State
from ..core.manticore import ManticoreBase
from ..core.smtlib import ConstraintSet

logger = logging.getLogger(__name__)


class ManticoreWASM(ManticoreBase):
    """
    """

    def __init__(self, path_or_state, argv=None, workspace_url=None, policy="random", **kwargs):
        """
        :param path_or_state: Path to binary or a state (object) to begin from.
        :param argv: arguments passed to the binary.
        """
        if isinstance(path_or_state, str):
            if not os.path.isfile(path_or_state):
                raise OSError(f"{path_or_state} is not an existing regular file")
            initial_state = _make_initial_state(path_or_state, argv=argv, **kwargs)
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


def _make_initial_state(binary_path, **kwargs):
    if binary_path.endswith(".wasm"):
        return _make_wasm_bin(binary_path, **kwargs)
    # elif binary_path.endswith(".wat"):
    #     state = _make_wasm_watf(binary_path, **kwargs)


def getchar(constraints: ConstraintSet, *args):
    print("Called getchar with args:", args)
    return [constraints.new_bitvec(32, "getchar_output")]


def _make_wasm_bin(program, **kwargs):
    from ..platforms import wasm

    logger.info("Loading program %s", program)

    constraints = ConstraintSet()
    platform = wasm.WASMWorld(program)

    platform.instantiate({"getchar": functools.partial(getchar, constraints)})
    platform.invoke("main")

    initial_state = State(constraints, platform)

    return initial_state
