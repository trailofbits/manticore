from enum import Enum


class StateLists(Enum):
    """
    The set of StateLists tracked in ManticoreBase
    """

    ready = "READY"
    busy = "BUSY"
    terminated = "TERMINATED"
    killed = "KILLED"


class StateStatus(Enum):
    """
    Statuses that a StateDescriptor can have
    """

    waiting_for_worker = "waiting_for_worker"
    waiting_for_solver = "waiting_for_solver"
    running = "running"
    #: Killed OR Terminated
    stopped = "stopped"
    #: Removed
    destroyed = "destroyed"


class MProcessingType(Enum):
    """Used as configuration constant for choosing multiprocessing flavor"""

    multiprocessing = "multiprocessing"
    single = "single"
    threading = "threading"

    def title(self):
        return self._name_.title()

    @classmethod
    def from_string(cls, name):
        return cls.__members__[name]

    def to_class(self):
        return globals()[f"Manticore{self.title()}"]


class Sha3Type(Enum):
    """Used as configuration constant for choosing sha3 flavor"""

    concretize = "concretize"
    symbolicate = "symbolicate"
    fake = "fake"

    def title(self):
        return self._name_.title()

    @classmethod
    def from_string(cls, name):
        return cls.__members__[name]


class DetectorClassification(Enum):
    """
    Shall be consistent with
    https://github.com/trailofbits/slither/blob/563d5118298e4cae7f0ea5f2a531f0dcdcebd64d/slither/detectors/abstract_detector.py#L11-L15
    """

    HIGH = 0
    MEDIUM = 1
    LOW = 2
    INFORMATIONAL = 3
