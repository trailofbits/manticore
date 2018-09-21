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


# Ethereum


class EthereumError(ManticoreError):
    pass


class DependencyError(EthereumError):
    def __init__(self, lib_names):
        super().__init__("You must pre-load and provide libraries addresses{ libname:address, ...} for %r" % lib_names)
        self.lib_names = lib_names


class NoAliveStates(EthereumError):
    pass


