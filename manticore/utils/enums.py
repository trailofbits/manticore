from enum import Enum


class StateLists(Enum):
    ready = "READY"
    busy = "BUSY"
    terminated = "TERMINATED"
    killed = "KILLED"
