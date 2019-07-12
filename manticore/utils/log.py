import logging
import sys

manticore_verbosity = 0
DEFAULT_LOG_LEVEL = logging.WARNING
all_loggers = set()
default_factory = logging.getLogRecordFactory()
logfmt = "%(asctime)s: [%(process)d] %(name)s:%(levelname)s %(message)s"
handler = logging.StreamHandler(sys.stdout)
formatter = logging.Formatter(logfmt)
handler.setFormatter(formatter)


class ContextFilter(logging.Filter):
    """
    This is a filter which injects contextual information into the log.
    """

    def summarized_name(self, name):
        """
        Produce a summarized record name
          i.e. manticore.core.executor -> m.c.executor
        """
        components = name.split(".")
        prefix = ".".join(c[0] for c in components[:-1])
        return f"{prefix}.{components[-1]}"

    colors_disabled = False

    coloring = {"DEBUG": "magenta", "WARNING": "yellow", "ERROR": "red", "INFO": "blue"}
    colors = dict(
        zip(
            ["black", "red", "green", "yellow", "blue", "magenta", "cyan", "white"],
            map(str, range(30, 30 + 8)),
        )
    )

    color_map = {}
    for k, v in coloring.items():
        color_map[k] = colors[v]

    colored_levelname_format = "\x1b[{}m{}:\x1b[0m"
    plain_levelname_format = "{}:"

    def colored_level_name(self, levelname):
        """
        Colors the logging level in the logging record
        """
        if self.colors_disabled:
            return self.plain_levelname_format.format(levelname)
        else:
            return self.colored_levelname_format.format(self.color_map[levelname], levelname)

    def filter(self, record):
        record.name = self.summarized_name(record.name)
        record.levelname = self.colored_level_name(record.levelname)
        return True


ctxfilter = ContextFilter()


class CustomLogger(logging.Logger):
    """
    Custom Logger class that can grab the correct verbosity level from this module
    """

    def __init__(self, name, level=DEFAULT_LOG_LEVEL, *args):
        super().__init__(name, min(get_verbosity(name), level), *args)
        all_loggers.add(name)
        self.initialized = False

        if name.startswith("manticore"):
            self.addHandler(handler)
            self.addFilter(ctxfilter)
            self.propagate = False


logging.setLoggerClass(CustomLogger)


def disable_colors():
    ContextFilter.colors_disabled = True


def get_levels():
    return [
        # 0
        [(x, DEFAULT_LOG_LEVEL) for x in all_loggers],
        # 1
        [
            ("manticore.manticore", logging.INFO),
            ("manticore.main", logging.INFO),
            ("manticore.ethereum.*", logging.INFO),
            ("manticore.native.*", logging.INFO),
            ("manticore.core.manticore", logging.INFO),
        ],
        # 2 (-v)
        [
            ("manticore.core.executor", logging.INFO),
            ("manticore.platforms.*", logging.DEBUG),
            ("manticore.ethereum", logging.DEBUG),
            ("manticore.core.plugin", logging.DEBUG),
            ("manticore.util.emulate", logging.INFO),
        ],
        # 3 (-vv)
        [("manticore.native.cpu.*", logging.DEBUG)],
        # 4 (-vvv)
        [
            ("manticore.native.memory", logging.DEBUG),
            ("manticore.native.cpu.*", logging.DEBUG),
            ("manticore.native.cpu.*.registers", logging.DEBUG),
        ],
        # 5 (-vvvv)
        [
            ("manticore.manticore", logging.DEBUG),
            ("manticore.ethereum.*", logging.DEBUG),
            ("manticore.native.*", logging.DEBUG),
            ("manticore.core.smtlib", logging.DEBUG),
            ("manticore.core.smtlib.*", logging.DEBUG),
        ],
    ]


def get_verbosity(logger_name):
    def match(name, pattern):
        """
        Pseudo globbing that only supports full fields. 'a.*.d' matches 'a.b.d'
        but not 'a.b.c.d'.
        """
        name_l, pattern_l = name.split("."), pattern.split(".")
        if len(name_l) != len(pattern_l):
            return False
        for name_f, pattern_f in zip(name_l, pattern_l):
            if pattern_f == "*":
                continue
            if name_f != pattern_f:
                return False
        return True

    for level in range(manticore_verbosity, 0, -1):
        for pattern, log_level in get_levels()[level]:
            if match(logger_name, pattern):
                return log_level
    return DEFAULT_LOG_LEVEL


def set_verbosity(setting):
    global manticore_verbosity
    manticore_verbosity = min(max(setting, 0), len(get_levels()) - 1)
    for logger_name in all_loggers:
        logger = logging.getLogger(logger_name)
        # min because more verbosity == lower numbers
        # This means if you explicitly call setLevel somewhere else in the source, and it's *more*
        # verbose, it'll stay that way even if manticore_verbosity is 0.
        logger.setLevel(min(get_verbosity(logger_name), logger.getEffectiveLevel()))
