import sys

if sys.version_info < (3, 6):
    print('Manticore requires Python 3.6 or higher.')
    sys.exit(-1)

from .utils import config, log
from .utils.helpers import issymbolic, istainted

__all__ = [issymbolic.__name__, istainted.__name__]
