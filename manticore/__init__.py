from .utils import config, log

log.init_logging()

consts = config.get_group('main')
consts.add('stdin_size', default=256, description='Maximum symbolic stdin size')
