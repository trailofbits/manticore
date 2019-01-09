import sys

if sys.version_info < (3, 6):
    print('Manticore requires Python 3.6 or higher.')
    sys.exit(-1)

from .utils import config, log
from .utils.helpers import issymbolic, istainted

consts = config.get_group('main')
consts.add('stdin_size', default=256, description='Maximum symbolic stdin size')

__all__ = [issymbolic.__name__, istainted.__name__]
