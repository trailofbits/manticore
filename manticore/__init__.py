import sys

if sys.version_info < (3, 6):
    print("Manticore requires Python 3.6 or higher.")
    sys.exit(-1)

from .utils import config, log
from .utils.log import set_verbosity
from .core.smtlib import issymbolic, istainted
from .ethereum.manticore import ManticoreEVM
from .core.plugin import Plugin
from .exceptions import ManticoreError

__all__ = [
    issymbolic.__name__,
    istainted.__name__,
    ManticoreEVM.__name__,
    set_verbosity.__name__,
    ManticoreError.__name__,
]
