from abc import abstractmethod

from capstone import Cs

class Disasm(object):
    """Abstact class for different disassembler interfaces"""

    def __init__(self, disasm):
        self.disasm = disasm

    @abstractmethod
    def get_insn(self, code, pc):
        """Get next instruction based on the disassembler in use

        :param code: disassembled code
        :param pc: program counter
        """
        pass

class Capstone(Disasm):

    def __init__(self, arch, mode):
        cs = Cs(arch, mode)
        cs.detail = True
        cs.syntax = 0
        super(Capstone, self).__init__(cs)

    def get_insn(self, code, pc):
        """Get next instruction based on Capstone disassembler

        :param code: disassembled code
        :param pc: program counter
        """
        return next(self.disasm.disasm(code, pc))
