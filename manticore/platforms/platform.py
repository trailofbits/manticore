
from manticore.utils.event import Signal
from itertools import islice, imap
import inspect

class OSException(Exception):
    pass


class SyscallNotImplemented(OSException):
    ''' Exception raised when you try to call a not implemented
        system call. Go to linux.py and add it!
    '''
    pass

class ConcretizeSyscallArgument(OSException):
    def __init__(self, reg_num, message='Concretizing syscall argument', policy='SAMPLED'):
        self.reg_num = reg_num
        self.message = message
        self.policy = policy
        super(ConcretizeSyscallArgument, self).__init__(message)


class Platform(object):
    '''
    Base class for all operating system platforms.
    '''
    def __init__(self, path):
        self._path = path

    def invoke_model(self, model, prefix_args=None):
        self._function_abi.invoke(model, prefix_args)
