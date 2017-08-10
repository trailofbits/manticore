from __future__ import absolute_import
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

ctxfilter = ContextFilter()
logfmt = ("%(asctime)s: [%(process)d]%(stateid)s %(name)s:%(levelname)s:"
          " %(message)s")
logging.basicConfig(format=logfmt, stream=sys.stdout, level=logging.ERROR)

def loggerSetState(logger, stateid):
    logger.filters[0].stateid = stateid

for l in loggers:
    logging.getLogger(l).addFilter(ctxfilter)
    logging.getLogger(l).setState = types.MethodType(loggerSetState,
                                                     logging.getLogger(l))

def set_verbosity(setting):
    zero = map(lambda x: (x, logging.ERROR), loggers)
    levels = [
        # 0
        [
            ('MANTICORE', logging.INFO)
        ],
        # 1 (-v)
        [
            ('EXECUTOR', logging.INFO),
            ('PLATFORM', logging.DEBUG)
        ],
        # 2 (-vv)
        [
            ('CPU', logging.DEBUG)
        ],
        # 3 (-vvv)
        [
            ('MEMORY', logging.DEBUG),
            ('CPU', logging.DEBUG),
            ('REGISTERS', logging.DEBUG)
        ],
        # 4 (-vvvv)
        [
            ('MANTICORE', logging.DEBUG),
            ('SMT', logging.DEBUG)
         ]
    ]

    # Takes a value and ensures it's in a certain range
    def clamp(val, minimum, maximum):
        return sorted((minimum, val, maximum))[1]

    clamped = clamp(setting, 0, len(levels) - 1)
    if clamped != setting:
        logger.debug("%s not between 0 and %d, forcing to %d",
                     setting,
                     len(levels) - 1,
                     clamped)
    for level in range(clamped + 1):
        for log_type, log_level in levels[level]:
            logging.getLogger(log_type).setLevel(log_level)
    # manticore_verbosity = clamped

