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
    def __init__(self, arch, mode):
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
        self.view = view
        # dictionary with llil for each function. This will be consumed
        # using an iterator, so that we don't repeat ourselves whenever
        # we ask for the next IL
        self.func_llil = {}
        self.entry_point_diff = None
        super(BinjaILDisasm, self).__init__(view)

    def _fix_addr(self, addr):
        # FIXME how to deal with discrepancies of binja vs real program
        # entry point addresses? We need to lookup the symbols and
        # we should make sure all offsets are appropriate

        if not self.entry_point_diff:
            # assume that the first time we are called, this is the entry point
            self.entry_point_diff = addr - self.view.entry_point

        return addr - self.entry_point_diff

    def disassemble_instruction(self, _, pc):
        """Get next instruction based on Capstone disassembler

        :param code: disassembled code
        :param pc: program counter
        """
        pc = self._fix_addr(pc)
        blocks = self.view.get_basic_blocks_at(pc)
        # FIXME is this proper? Should we be calling blocks[0](blah?)
        func = blocks[0].function
        il = func.get_lifted_il_at(pc)
        print ("%s %s %x %x\n") % (str(il), il.operation.name, il.instr_index, il.address)
        return self.BinjaILInstruction(self.view, il, self.entry_point_diff)


    class BinjaILInstruction(Instruction):
        def __init__(self, view, llil, offset):
            self.view = view
            self.llil = llil
            self.offset = offset
            super(BinjaILDisasm.BinjaILInstruction, self).__init__()

        def _fix_addr(self, addr):
            return addr + self.offset

        @property
        def size(self):
            next_addr = self.llil.function[self.llil.instr_index + 1].address
            # FIXME what about the end of the function? Should be OK because
            # that should be a CALL or a JMP
            return next_addr - self.llil.address

        @property
        def operands(self):
            return self.llil.operands

        @operands.setter
        def operands(self, value):
            # This will be overloaded by a BinjaILOperand
            self.llil.operands = value

        @property
        def insn_name(self):
            return self.llil.operation.name

        @property
        def name(self):
            return self.llil.operation.name[len("LLIL_"):]

        @property
        def address(self):
            return self._fix_addr(self.llil.address)

class BinjaDisasm(Disasm):

    def __init__(self, view):
        self.view = view
        super(BinjaDisasm, self).__init__(view)

    def disassemble_instruction(self, _, pc):
        """Get next instruction based on Capstone disassembler

        :param code: disassembled code
        :param pc: program counter
        """
        return self.view.get_disassembly(pc)

    class BinjaInstruction(Instruction):
        def __init__(self, insn):
            self.insn = insn
            super(BinjaDisasm.BinjaInstruction, self).__init__()

        @property
        def size(self):
            pass

        @property
        def operands(self):
            return self._operands

        @operands.setter
        def operands(self, value):
            self._operands = value

        @property
        def insn_name(self):
            pass

        @property
        def name(self):
            pass

def init_disassembler(disassembler, arch, mode, view):
    if disassembler == "capstone":
        return CapstoneDisasm(arch, mode)
    elif disassembler == "binja":
        return BinjaDisasm(view)
    elif disassembler == "binja-il":
        return BinjaILDisasm(view)
    else:
        raise NotImplementedError("Disassembler not implemented")
