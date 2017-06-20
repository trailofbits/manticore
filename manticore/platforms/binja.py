import binaryninja as bn

from .abstractcpu import (
    Abi, SyscallAbi, Cpu, RegisterFile, Operand, instruction,
    Interruption, Sysenter, Syscall, ConcretizeRegister, ConcretizeArgument
)
from ..core.memory import Memory64
from ..core.smtlib import ConstraintSet
from .platform import Platform

class Binja(Platform):
    def __init__(self, ifile):
        '''
        Builds a BinaryNinja Emulator
        :param ifile: file containing program to analyze
        '''
        # binary view
        self._bv = self._init_bv(ifile)
        self._entry_func = self._bv.get_functions_at(self._bv.entry_point)

        # Just have 64-bit memory for the generic case
        cpu.get_cpu(Memory64(), 'binja_il')

        # constraints
        self._constraints = ConstraintSet()
        super(Binja, self).__init__(ifile)

    @property
    def constraints(self):
        return self._constraints

    @property
    def bv(self):
        return self._bv

    def __getstate__(self):
        state = {}
        state['constraints'] = self.constraints
        return state

    def __setstate__(self, state):
        self._constraints = state['constraints']

    @staticmethod
    def _init_bv(program_file):
        """
        Reads a binary and returns a binary vieww

        FIXME (theo) this will be replaced by a function that simply loadss
        the IL from a file, but right now this is not serializable
        """
        vtypes = filter(lambda x: x.name != "Raw",
                        bn.BinaryView.open(program_file).available_view_types)
        bv = bn.BinaryViewType[vtypes[0].name].open(program_file)
        bv.update_analysis_and_wait()
        return bv
