import logging
import sys
import io

from typing import List, Tuple, Optional, Callable

manticore_verbosity = 0
DEFAULT_LOG_LEVEL = logging.WARNING
logfmt = "%(asctime)s: [%(process)d] %(name)s:%(levelname)s %(message)s"
formatter = logging.Formatter(logfmt)


def get_manticore_logger_names() -> List[str]:
    return [name for name in logging.root.manager.loggerDict if name.split(".", 1)[0] == "manticore"]  # type: ignore


class CallbackStream(io.StringIO):
    def __init__(self, callback):
        super().__init__()
        self.callback = callback

    def write(self, log_str):
        self.callback(log_str)


class ManticoreContextFilter(logging.Filter):
    """
    This is a filter which injects contextual information into the log.
    """

    def summarized_name(self, name: str) -> str:
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

    def colored_level_name(self, levelname: str) -> str:
        """
        Colors the logging level in the logging record
        """
        if self.colors_disabled:
            return self.plain_levelname_format.format(levelname)
        else:
            return self.colored_levelname_format.format(self.color_map[levelname], levelname)

    def filter(self, record: logging.LogRecord) -> bool:
        if not record.name.startswith("manticore"):
            return True

        record.name = self.summarized_name(record.name)
        record.levelname = self.colored_level_name(record.levelname)
        return True


def disable_colors() -> None:
    ManticoreContextFilter.colors_disabled = True


def get_levels() -> List[List[Tuple[str, int]]]:
    all_loggers = get_manticore_logger_names()
    return [
        # 0
        [(x, DEFAULT_LOG_LEVEL) for x in all_loggers],
        # 1
        [
            ("manticore.main", logging.INFO),
            ("manticore.ethereum.*", logging.INFO),
            ("manticore.native.*", logging.INFO),
            ("manticore.core.manticore", logging.INFO),
        ],
        # 2 (-v)
        [
            ("manticore.core.worker", logging.INFO),
            ("manticore.platforms.*", logging.DEBUG),
            ("manticore.ethereum", logging.DEBUG),
            ("manticore.core.plugin", logging.INFO),
            ("manticore.wasm.*", logging.INFO),
            ("manticore.utils.emulate", logging.INFO),
        ],
        # 3 (-vv)
        [("manticore.native.cpu.*", logging.DEBUG), ("manticore.wasm.*", logging.DEBUG)],
        # 4 (-vvv)
        [
            ("manticore.native.memory", logging.DEBUG),
            ("manticore.native.cpu.*", logging.DEBUG),
            ("manticore.native.cpu.*.registers", logging.DEBUG),
            ("manticore.core.plugin", logging.DEBUG),
            ("manticore.utils.helpers", logging.INFO),
        ],
        # 5 (-vvvv)
        [
            ("manticore.core.manticore", logging.DEBUG),
            ("manticore.ethereum.*", logging.DEBUG),
            ("manticore.native.*", logging.DEBUG),
            ("manticore.core.smtlib", logging.DEBUG),
            ("manticore.core.smtlib.*", logging.DEBUG),
        ],
    ]


def get_verbosity(logger_name: str) -> int:
    def match(name: str, pattern: str):
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


def set_verbosity(setting: int) -> None:
    """Set the global verbosity (0-5)."""
    global manticore_verbosity
    manticore_verbosity = min(max(setting, 0), len(get_levels()) - 1)
    for logger_name in get_manticore_logger_names():
        logger = logging.getLogger(logger_name)
        # min because more verbosity == lower numbers
        # This means if you explicitly call setLevel somewhere else in the source, and it's *more*
        # verbose, it'll stay that way even if manticore_verbosity is 0.
        logger.setLevel(min(get_verbosity(logger_name), logger.getEffectiveLevel()))


def register_log_callback(callback: Callable[[Optional[str]], None]) -> None:
    callback_handler = logging.StreamHandler(CallbackStream(callback))
    callback_handler.setFormatter(formatter)
    callback_handler.addFilter(ManticoreContextFilter())
    init_logging(callback_handler)


def default_handler() -> logging.Handler:
    """Return a default Manticore logger with a nice formatter and filter."""
    handler = logging.StreamHandler(sys.stdout)
    handler.setFormatter(formatter)
    handler.addFilter(ManticoreContextFilter())
    return handler


def init_logging(handler: Optional[logging.Handler] = None) -> None:
    """
    Initialize logging for Manticore, given a handler or by default use `default_logger()`
    """
    logger = logging.getLogger("manticore")
    logger.parent = None  # type: ignore

    # Explicitly set the level so that we don't use root's. If root is at DEBUG,
    # then _a lot_ of logs will be printed if the user forgets to set
    # manticore's logger
    logger.setLevel(DEFAULT_LOG_LEVEL)

    if handler is None:
        handler = default_handler()

    # Finally attach to Manticore
    logger.addHandler(handler)
