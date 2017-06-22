from abc import abstractproperty, abstractmethod

import capstone as cs


class Instruction(object):
    """Capstone-like instruction to be used internally
    """
    @abstractproperty
    def address(self):
        pass

    @abstractproperty
    def size(self):
        pass

    @abstractproperty
    def operands(self):
        pass

    # FIXME (theo) eliminate one of the two of insn_name, name
    @abstractproperty
    def insn_name(self):
        pass

    @abstractproperty
    def name(self):
        pass

class Disasm(object):
    """Abstact class for different disassembler interfaces"""

    def __init__(self, disasm):
        self.disasm = disasm

    @abstractmethod
    def disassemble_instruction(self, code, pc):
        """Get next instruction based on the disassembler in use

        :param code: disassembled code
        :param pc: program counter
        """
        pass

class CapstoneDisasm(Disasm):
    def __init__(self, arch):
        arch_map = {
            'i386': (cs.CS_ARCH_X86, cs.CS_MODE_32),
            'amd64': (cs.CS_ARCH_X86, cs.CS_MODE_64),
            'armv7': (cs.CS_ARCH_ARM, cs.CS_MODE_ARM)
        }

        arch, mode = arch_map[arch]
        cap = cs.Cs(arch, mode)
        cap.detail = True
        cap.syntax = 0
        super(CapstoneDisasm, self).__init__(cap)

    def disassemble_instruction(self, code, pc):
        """Get next instruction based on Capstone disassembler

        :param code: disassembled code
        :param pc: program counter
        """
        return next(self.disasm.disasm(code, pc))

class BinjaILDisasm(Disasm):

    def __init__(self, view):
        self.bv = view
        # dictionary with llil for each function. This will be consumed
        # using an iterator, so that we don't repeat ourselves whenever
        # we ask for the next IL
        self.func_llil = {}
        super(BinjaILDisasm, self).__init__(view)

    def disassemble_instruction(self, _, pc):
        """Get next instruction based on Capstone disassembler

        :param code: disassembled code
        :param pc: program counter
        """
        #  print(self.bv.get_disassembly(pc))
        blocks = self.bv.get_basic_blocks_at(pc)
        func = blocks[0].function
        fllil = self.func_llil.get(func,
                                   iter([il for block in func.low_level_il
                                         for il in block]))

        il = next(fllil)
        print(il)
        print ("%s %x %x\n") % (il.operation.name, il.instr_index, il.address)
        self.func_llil[func] = fllil
        return self.BinjaILInstruction(il)


    class BinjaILInstruction(Instruction):
        def __init__(self, llil):
            self.llil = llil
            super(BinjaILDisasm.BinjaILInstruction, self).__init__()

        @property
        def size(self):
            return 1

        @property
        def operands(self):
            return self.llil.operands

        @operands.setter
        def operands(self, value):
            self._operands = value

        @property
        def insn_name(self):
            return self.llil.operation.name

        @property
        def name(self):
            return self.llil.operation.name[len("LLIL_"):]

class BinjaDisasm(Disasm):

    def __init__(self, view):
        self.bv = view
        super(BinjaDisasm, self).__init__(view)

    def disassemble_instruction(self, _, pc):
        """Get next instruction based on Capstone disassembler

        :param code: disassembled code
        :param pc: program counter
        """
        return self.bv.get_disassembly(pc)

    class BinjaInstruction(Instruction):
        def __init__(self, insn):
            self.insn = insn
            super(BinjaDisasm.BinjaInstruction, self).__init__()

        @property
        def size(self):
            pass

        @property
        def operands(self):
            pass

        @operands.setter
        def operands(self, value):
            self._operands = value

        @property
        def insn_name(self):
            pass

        @property
        def name(self):
            pass

def init_disassembler(disassembler, arch, program):
    if disassembler == "capstone":
        return CapstoneDisasm(arch)
    elif disassembler == "binja":
        return BinjaDisasm(program)
