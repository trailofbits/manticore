import logging
import sys
import types

class ContextFilter(logging.Filter):
    '''
    This is a filter which injects contextual information into the log.
    '''
    def filter(self, record):
        if hasattr(self, 'stateid') and isinstance(self.stateid, int):
            record.stateid = '[%d]' % self.stateid
        else:
            record.stateid = ''
        return True

loggers = ['MANTICORE',
           'VISITOR',
           'EXECUTOR',
           'CPU',
           'REGISTERS',
           'SMT',
           'MEMORY',
           'PLATFORM']
manticore_verbosity = 0

def init_logging():
    ctxfilter = ContextFilter()
    logfmt = ("%(asctime)s: [%(process)d]%(stateid)s %(name)s:%(levelname)s:"
              " %(message)s")
    logging.basicConfig(format=logfmt, stream=sys.stdout, level=logging.ERROR)
    for l in loggers:
        logging.getLogger(l).setLevel(logging.WARNING)
        logging.getLogger(l).addFilter(ctxfilter)
        logging.getLogger(l).setState = types.MethodType(loggerSetState,
                                                         logging.getLogger(l))

def loggerSetState(logger, stateid):
    logger.filters[0].stateid = stateid

def set_verbosity(setting):
    global manticore_verbosity
    zero = map(lambda x: (x, logging.WARNING), loggers)
    levels = [
        # 0
        zero,
        # 1
        [
            ('MANTICORE', logging.INFO)
        ],
        # 2 (-v)
        [
            ('EXECUTOR', logging.INFO),
            ('PLATFORM', logging.DEBUG)
        ],
        # 3 (-vv)
        [
            ('CPU', logging.DEBUG)
        ],
        # 4 (-vvv)
        [
            ('MEMORY', logging.DEBUG),
            ('CPU', logging.DEBUG),
            ('REGISTERS', logging.DEBUG)
        ],
        # 5 (-vvvv)
        [
            ('MANTICORE', logging.DEBUG),
            ('SMT', logging.DEBUG)
         ]
    ]

    # Takes a value and ensures it's in a certain range
    def clamp(val, minimum, maximum):
        return sorted((minimum, val, maximum))[1]

    clamped = clamp(setting, 0, len(levels) - 1)
    for level in range(clamped + 1):
        for log_type, log_level in levels[level]:
            logging.getLogger(log_type).setLevel(log_level)
    manticore_verbosity = clamped
