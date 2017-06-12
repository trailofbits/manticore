class Disasm(object):
    """Abstact class for different disassembler interfaces"""

    def __init__(self, disasm):
        self.disasm = disasm


class Capstone(Disasm):

    def __init__(self, arch, mode):
        cs = Cs(arch, mode)
        cs.detail = True
        cs.syntax = 0
        super(Capstone, self).__init__(cs)
