from manticore.utils.event import Eventful


class OSException(Exception):
    pass


class SyscallNotImplemented(OSException):
    ''' Exception raised when you try to call a not implemented
        system call. Go to linux.py and add it!
    '''

    def __init__(self, idx, name):
        msg = 'Syscall index "{}" ({}) not implemented.'.format(idx, name)
        super(SyscallNotImplemented, self).__init__(msg)


class ConcretizeSyscallArgument(OSException):
    def __init__(self, reg_num, message='Concretizing syscall argument', policy='SAMPLED'):
        self.reg_num = reg_num
        self.message = message
        self.policy = policy
        super(ConcretizeSyscallArgument, self).__init__(message)


class Platform(Eventful):
    '''
    Base class for all operating system platforms.
    '''

    def __init__(self, path, **kwargs):
        super(Platform, self).__init__(**kwargs)

    def invoke_model(self, model, prefix_args=None):
        self._function_abi.invoke(model, prefix_args)

    def __setstate__(self, state):
        super(Platform, self).__setstate__(state)

    def __getstate__(self):
        state = super(Platform, self).__getstate__()
        return state

    def generate_workspace_files(self):
        return {}
