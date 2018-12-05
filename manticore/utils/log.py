import logging
import sys
import types


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
        return f'{prefix}.{components[-1]}'

    colors_disabled = False

    coloring = {u'DEBUG':u'magenta', u'WARNING':u'yellow',
        u'ERROR':u'red', u'INFO':u'blue'}
    colors =  dict(zip([u'black', u'red', u'green', u'yellow',
        u'blue', u'magenta', u'cyan', u'white'], map(str, range(30, 30 + 8))))

    color_map = {}
    for k, v in coloring.items():
        color_map[k] = colors[v]

    colored_levelname_format = u'\x1b[{}m{}:\x1b[0m'
    plain_levelname_format = u'{}:'

    def colored_level_name(self, levelname):
        '''
        Colors the logging level in the logging record
        '''
        if self.colors_disabled:
            return self.plain_levelname_format.format(levelname)
        else:
            return self.colored_levelname_format.format(self.color_map[levelname], levelname)

    def filter(self, record):
        if hasattr(self, 'stateid') and isinstance(self.stateid, int):
            record.stateid = f'[{self.stateid}]'
        else:
            record.stateid = ''

        record.name = self.summarized_name(record.name)
        record.levelname = self.colored_level_name(record.levelname)
        return True


manticore_verbosity = 0
all_loggers = []


def disable_colors():
    ContextFilter.colors_disabled = True


def init_logging(default_level=logging.WARNING):
    global all_loggers
    loggers = logging.getLogger().manager.loggerDict.keys()

    ctxfilter = ContextFilter()
    logfmt = ("%(asctime)s: [%(process)d]%(stateid)s %(name)s:%(levelname)s"
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
    zero = [(x, logging.WARNING) for x in all_loggers]
    levels = [
        # 0
        zero,
        # 1
        [
            ('manticore.manticore', logging.INFO),
            ('manticore.main', logging.INFO),
            ('manticore.ethereum.*', logging.INFO),
            ('manticore.native.*', logging.INFO),
            ('manticore.core.manticore', logging.INFO)
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
            ('manticore.native.cpu.*', logging.DEBUG)
        ],
        # 4 (-vvv)
        [
            ('manticore.core.memory', logging.DEBUG),
            ('manticore.native.cpu.*', logging.DEBUG),
            ('manticore.native.cpu.*.registers', logging.DEBUG)
        ],
        # 5 (-vvvv)
        [
            ('manticore.manticore', logging.DEBUG),
            ('manticore.ethereum.*', logging.DEBUG),
            ('manticore.native.*', logging.DEBUG),
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
        return [name for name in lst if match(name, expression)]

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
