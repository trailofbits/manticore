import logging
import sys
import types
from logging import DEBUG, WARNING, ERROR, INFO


class ContextFilter(logging.Filter):
    '''
    This is a filter which injects contextual information into the log.
    '''

    def summarized_name(self, name):
        '''
        Produce a summarized record name
          i.e. manticore.core.executor -> m.c.executor
        '''
        components = name.split('.')
        prefix = '.'.join(c[0] for c in components[:-1])
        return '{}.{}'.format(prefix, components[-1])

    def filter(self, record):
        if hasattr(self, 'stateid') and isinstance(self.stateid, (int, long)):
            record.stateid = '[%d]' % self.stateid
        else:
            record.stateid = ''

        record.name = self.summarized_name(record.name)
        return True


manticore_verbosity = 0
all_loggers = []


def init_logging(default_level=logging.WARNING):
    global all_loggers
    loggers = logging.getLogger().manager.loggerDict.keys()

    ctxfilter = ContextFilter()
    logfmt = ("%(asctime)s: [%(process)d]%(stateid)s %(name)s:%(levelname)s:"
              " %(message)s")
    handler = logging.StreamHandler(sys.stdout)
    formatter = logging.Formatter(logfmt)
    handler.setFormatter(formatter)
    for name in loggers:
        logger = logging.getLogger(name)
        if not name.startswith('manticore'):
            continue
        if name in all_loggers:
            continue
        logger.addHandler(handler)
        logger.propagate = False
        logger.setLevel(default_level)
        logger.addFilter(ctxfilter)
        logger.setState = types.MethodType(loggerSetState, logger)
        all_loggers.append(name)
    set_verbosity(manticore_verbosity)


def loggerSetState(logger, stateid):
    logger.filters[0].stateid = stateid


def set_verbosity(setting):
    global manticore_verbosity, all_loggers
    zero = map(lambda x: (x, logging.WARNING), all_loggers)
    levels = [
        # 0
        zero,
        # 1
        [
            ('manticore.manticore', logging.INFO),
            ('manticore.main', logging.INFO),
            ('manticore.ethereum', logging.INFO),
        ],
        # 2 (-v)
        [
            ('manticore.core.executor', logging.INFO),
            ('manticore.platforms.*', logging.DEBUG),
            ('manticore.ethereum', logging.DEBUG),
            ('manticore.core.plugin', logging.DEBUG),
        ],
        # 3 (-vv)
        [
            ('manticore.core.cpu.*', logging.DEBUG)
        ],
        # 4 (-vvv)
        [
            ('manticore.core.memory', logging.DEBUG),
            ('manticore.core.cpu.*', logging.DEBUG),
            ('manticore.core.cpu.*.registers', logging.DEBUG)
        ],
        # 5 (-vvvv)
        [
            ('manticore.manticore', logging.DEBUG),
            ('manticore.core.smtlib', logging.DEBUG),
            ('manticore.core.smtlib.*', logging.DEBUG)
        ]
    ]

    def match(name, pattern):
        '''
        Pseudo globbing that only supports full fields. 'a.*.d' matches 'a.b.d'
        but not 'a.b.c.d'.
        '''
        name_l, pattern_l = name.split('.'), pattern.split('.')
        if len(name_l) != len(pattern_l):
            return False
        for name_f, pattern_f in zip(name_l, pattern_l):
            if pattern_f == '*':
                continue
            if name_f != pattern_f:
                return False
        return True

    def glob(lst, expression):
        return filter(lambda name: match(name, expression), lst)

    # Takes a value and ensures it's in a certain range
    def clamp(val, minimum, maximum):
        return sorted((minimum, val, maximum))[1]

    clamped = clamp(setting, 0, len(levels) - 1)
    for level in range(clamped + 1):
        for pattern, log_level in levels[level]:
            for logger_name in glob(all_loggers, pattern):
                logger = logging.getLogger(logger_name)
                logger.setLevel(log_level)

    manticore_verbosity = clamped
