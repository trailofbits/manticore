"""
Public subclasses of Exception
"""


class ManticoreError(Exception):
    """
    Top level Exception object for custom exception hierarchy
    """
    pass


class ExecutorError(ManticoreError):
    pass


# Smtlib

class SmtlibError(ManticoreError):
    pass


class Z3NotFoundError(SmtlibError):
    pass


# TODO: rename to SolverError
class SolverException(SmtlibError):
    pass


class SolverUnknown(SolverException):
    pass


class TooManySolutions(SolverException):
    def __init__(self, solutions):
        super().__init__("Max number of different solutions hit")
        self.solutions = solutions


# Ethereum


class EthereumError(ManticoreError):
    pass


class DependencyError(EthereumError):
    def __init__(self, lib_names):
        super().__init__("You must pre-load and provide libraries addresses{ libname:address, ...} for %r" % lib_names)
        self.lib_names = lib_names


class NoAliveStates(EthereumError):
    pass


