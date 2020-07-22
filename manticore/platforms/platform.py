import logging

from functools import wraps
from typing import Any, Callable, TypeVar

from ..utils.event import Eventful


logger = logging.getLogger(__name__)


class OSException(Exception):
    pass


T = TypeVar("T")


def unimplemented(wrapped: Callable[..., T]) -> Callable[..., T]:
    @wraps(wrapped)
    def new_wrapped(self: Any, *args, **kwargs) -> T:
        cpu = getattr(getattr(self, "parent", None), "current", None)
        pc_str = "<unknown PC>" if cpu is None else hex(cpu.read_register("PC"))
        logger.warning(
            f"Unimplemented system call: %s: %s(%s)",
            pc_str,
            wrapped.__name__,
            ", ".join(hex(a) if isinstance(a, int) else str(a) for a in args),
        )
        return wrapped(self, *args, **kwargs)

    return new_wrapped


class SyscallNotImplemented(OSException):
    """
    Exception raised when you try to call an unimplemented system call.
    Go to linux.py and add an implementation!
    """

    def __init__(self, idx, name):
        msg = f'Syscall index "{idx}" ({name}) not implemented.'
        super().__init__(msg)


class Platform(Eventful):
    """
    Base class for all platforms e.g. operating systems or virtual machines.
    """

    _published_events = {"solve"}

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
