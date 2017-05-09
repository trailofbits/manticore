
from itertools import islice, imap
import inspect

class Platform(object):
    '''
    Base class for all operating system platforms.
    '''
    def __init__(self, path):
        self._path = path

    def invoke_model(self, model, prefix_args=None, varargs=False):
        self._function_abi.invoke(model, prefix_args, varargs)
