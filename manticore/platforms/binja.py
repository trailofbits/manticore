import logging

from ..core.cpu.binja import BinjaCpu
from ..core.cpu.cpufactory import CpuFactory
from ..core.cpu.disasm import BinjaILDisasm
from ..core.memory import SMemory64
from ..core.smtlib import ConstraintSet
from .platform import Platform

logger = logging.getLogger("PLATFORM")

class RestartSyscall(Exception):
    pass

class Deadlock(Exception):
    pass

class Binja(Platform):
    def __init__(self, ifile):
        '''
        Builds a BinaryNinja Emulator
        :param ifile: file containing program to analyze
        '''
        # XXX needed
        self.program = ifile
        self.clocks = 0
        self.files = []
        # XXX needed
        self.syscall_trace = []

        # binary view
        self._bv = self._init_bv(ifile)
        self._entry_func = self._bv.get_functions_at(self._bv.entry_point)

        # constraints
        self._constraints = ConstraintSet()
        # FIXME (theo) Just have 64-bit memory for now
        cpu = CpuFactory.get_cpu(SMemory64(self._constraints), 'binja_il')
        # XXX needed
        self.procs = [cpu]
        self._current = 0
        self._function_abi = CpuFactory.get_function_abi(cpu, 'linux', 'amd64')
        self._syscall_abi = CpuFactory.get_syscall_abi(cpu, 'linux', 'amd64')

        # initialize memory with the segments that we have
        for i, segment in enumerate(self._bv.segments):
            cpu.memory.mmap(segment.start,
                            segment.length,
                            #  segment.flags,
                            'rwx',
                            self._bv.read(segment.start, segment.length),
                            name='BinjaSegment_' + str(i))

        # FIXME (theo) Just hardcopy stack settings from x64 for now
        stack_size = 0x21000
        stack_top = 0x800000000000
        stack_base = stack_top - stack_size
        stack = cpu.memory.mmap(stack_base, stack_size, 'rwx', name='stack') + stack_size

        cpu.STACK = stack
        cpu.PC = self._bv.entry_point

        # set the class info now that we know it
        # FIXME (theo) this should be generic
        BinjaCpu.arch = 'linux'
        BinjaCpu.mode = 'amd64'
        BinjaCpu.disasm = BinjaILDisasm(self._bv)
        super(Binja, self).__init__(ifile)

    # XXX needed
    @property
    def constraints(self):
        return self._constraints

    @constraints.setter
    def constraints(self, constraints):
        self._constraints = constraints
        for proc in self.procs:
            proc.memory.constraints = constraints


    # XXX needed -> move to Platform as abstractproperty
    @property
    def current(self):
        return self.procs[self._current]

    # XXX refactor Linux, Windows etc
    def execute(self):
        """
        Execute one cpu instruction in the current thread (only one supported).
        :rtype: bool
        :return: C{True}

        :todo: This is where we could implement a simple schedule.
        """
        self.current.execute()
        return True

    @property
    def bv(self):
        return self._bv

    def __getstate__(self):
        state = {}
        # XXX (theo) required
        state['constraints'] = self.constraints
        state['procs'] = self.procs
        state['current'] = self._current
        state['syscall_trace'] = self.syscall_trace
        return state

    def __setstate__(self, state):
        # XXX (theo) required as a minimum set of params
        self._constraints = state['constraints']
        self.procs = state['procs']
        self._current = state['current']
        self.syscall_trace = state['syscall_trace']

    @staticmethod
    def _init_bv(program_file):
        """
        Reads a binary and returns a binary vieww

        FIXME (theo) this will be replaced by a function that simply loadss
        the IL from a file, but right now this is not serializable
        """
        # XXX do the import here so as to not affect users who don't have
        # BinaryNinja installed
        import binaryninja as bn
        bv = bn.binaryview.BinaryViewType.get_view_of_file(program_file)
        bv.update_analysis_and_wait()
        return bv
