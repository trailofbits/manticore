
from itertools import islice, imap
import inspect

class Platform(object):
    '''
    Base class for all operating system models.
    '''
    def __init__(self, path):
        self._path = path

    def invoke_model(self, implementation, prefix_args=None, varargs=False):
        self._function_abi.invoke(implementation, prefix_args, varargs)
