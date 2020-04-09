import wrapt
import logging
from ..utils.event import Eventful

from typing import Callable, Iterable, Mapping

logger = logging.getLogger(__name__)


class OSException(Exception):
    pass


@wrapt.decorator
def unimplemented(wrapped: Callable, _instance, args: Iterable, kwargs: Mapping):
    cpu = getattr(getattr(_instance, "parent", None), "current", None)
    addr_str = "" if cpu is None else f" at {hex(cpu.read_register('PC'))}"
    logger.warning(
        f"Unimplemented system call: %s: %s(%s)",
        addr_str,
        wrapped.__name__,
        ", ".join(hex(a) if isinstance(a, int) else str(a) for a in args),
    )
    return wrapped(*args, **kwargs)


class SyscallNotImplemented(OSException):
    """
    Exception raised when you try to call an unimplemented system call.
    Go to linux.py and add it!
    """

    def __init__(self, idx, name):
        msg = f'Syscall index "{idx}" ({name}) not implemented.'
        super().__init__(msg)


class ConcretizeSyscallArgument(OSException):
    def __init__(self, reg_num, message="Concretizing syscall argument", policy="SAMPLED"):
        self.reg_num = reg_num
        self.message = message
        self.policy = policy
        super().__init__(message)


class Platform(Eventful):
    """
    Base class for all platforms e.g. operating systems or virtual machines.
    """

    def __init__(self, path, **kwargs):
        super().__init__(**kwargs)

    def invoke_model(self, model, prefix_args=None):
        self._function_abi.invoke(model, prefix_args)

    def __setstate__(self, state):
        super().__setstate__(state)

    def __getstate__(self):
        state = super().__getstate__()
        return state

    def generate_workspace_files(self):
        return {}
