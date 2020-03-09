from functools import wraps
import inspect
import warnings

# DeprecationWarning is ignored by default, so we define a subcategory that we can give a different default.


class ManticoreDeprecationWarning(DeprecationWarning):
    """The deprecation warning class used by Manticore."""

    pass


warnings.simplefilter("default", category=ManticoreDeprecationWarning)


def deprecated(message: str):
    """A decorator for marking functions as deprecated. """
    assert isinstance(message, str), "The deprecated decorator requires a message string argument."

    def decorator(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            warnings.warn(
                f"`{func.__qualname__}` is deprecated. {message}",
                category=ManticoreDeprecationWarning,
                stacklevel=2,
            )
            return func(*args, **kwargs)

        return wrapper

    return decorator
