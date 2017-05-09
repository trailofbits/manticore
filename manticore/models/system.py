class OSException(Exception):
    pass


class SyscallNotImplemented(OSException):
    ''' Exception raised when you try to call a not implemented
        system call. Go to linux.py and add it!
    '''
    pass

class ProcessExit(OSException):
    def __init__(self, code):
        super(ProcessExit, self).__init__("Process exited correctly. Code: %s"%code)

class ConcretizeSyscallArgument(OSException):
    def __init__(self, reg_num, message='Concretizing syscall argument', policy='SAMPLED'):
        self.reg_num = reg_num
        self.message = message
        self.policy = policy
        super(ConcretizeSyscallArgument, self).__init__(message)


