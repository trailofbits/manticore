import logging
from psutil import disk_usage, virtual_memory

logger = logging.getLogger(__name__)
logger.setLevel(logging.INFO)

#: Percentage of _used_ memory to warn above
memory_warn_percent = 95.0
#: Number of free bytes to warn below
memory_warn_absolute = (1024 ** 3) // 2
#: Number of free bytes to warn below
disk_warn = 1024 ** 3


def check_memory_usage():
    """
    Print a warning message if the available memory space is below memory_warn
    """
    usage = virtual_memory()
    if usage.percent >= 95.0 or usage.available < memory_warn_absolute:
        logger.warning(
            "System only has %d kib of virtual memory available", usage.available // 1024
        )


def check_disk_usage(path="."):
    """
    Print a warning message if the available disk space is below disk_warn
    :param path: System path to check. Defaults to the current directory.
    """
    usage = disk_usage(path)
    if usage.free < (disk_warn):
        logger.warning("Only %d kib of disk space remaining", usage.free // 1024)
