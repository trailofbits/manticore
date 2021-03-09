import logging
from functools import wraps
from typing import Any, Callable, TypeVar, Optional

from ..utils.event import Eventful
from ..core.state import StateBase
from ..native.cpu.abstractcpu import Cpu


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

    current: Any

    _published_events = {"solve"}

    def __init__(self, *, state: Optional[StateBase] = None, **kwargs):
        self._state = state
        super().__init__(**kwargs)

    def set_state(self, state: StateBase):
        self._state = state
        state.forward_events_from(self)

    @property
    def constraints(self):
        return self._state._constraints

    def __setstate__(self, state):
        super().__setstate__(state)

    def __getstate__(self):
        state = super().__getstate__()
        return state


class NativePlatform(Platform):
    def __init__(self, path, **kwargs):
        super().__init__(**kwargs)

    def invoke_model(self, model, prefix_args=None):
        self._function_abi.invoke(model, prefix_args)

    def generate_workspace_files(self):
        return {}
