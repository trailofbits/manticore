from .utils import config, log
from .utils.helpers import issymbolic, istainted

log.init_logging()

consts = config.get_group('main')
consts.add('stdin_size', default=256, description='Maximum symbolic stdin size')

__all__ = [issymbolic.__name__, istainted.__name__]
