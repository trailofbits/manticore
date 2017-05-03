class OSException(Exception):
    pass

class ProcessExit(OSException):
    pass

class ConcretizeSyscallArgument(Exception):
    def __init__(self, reg_num, message='Concretizing syscall argument', policy='SAMPLED'):
        self.reg_num = reg_num
        self.message = message
        self.policy = policy
        super(ConcretizeSyscallArgument, self).__init__(message)

