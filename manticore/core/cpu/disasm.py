from abc import abstractproperty, abstractmethod

from capstone import Cs

class Instruction(object):
    """Capstone-like instruction to be used internally
    """
    # Return instruction's ID.
    @abstractproperty
    def id(self):
        pass

    # Return instruction's address.
    @abstractproperty
    def address(self):
        pass

    # Return instruction's size.
    @abstractproperty
    def size(self):
        pass

    # return instruction's machine bytes (which should have @size bytes).
    @abstractproperty
    def bytes(self):
        pass

    # return instruction's mnemonic.
    @abstractproperty
    def mnemonic(self):
        pass

    # return instruction's operands (in string).
    @abstractproperty
    def op_str(self):
        pass

    # return list of all implicit registers being read.
    @abstractproperty
    def regs_read(self):
        pass

    # return list of all implicit registers being modified
    @abstractproperty
    def regs_write(self):
        pass

    # return list of semantic groups this instruction belongs to.
    @abstractproperty
    def groups(self):
        pass

    # get the register name, given the register id
    @abstractproperty
    def reg_name(self, reg_id):
        pass

    # get the instruction name
    @abstractproperty
    def insn_name(self):
        pass

    # get the group name
    @abstractproperty
    def group_name(self, group_id):
        pass

    # verify if this insn belong to group with id as @group_id
    @abstractproperty
    def group(self, group_id):
        pass

    # verify if this instruction implicitly read register @reg_id
    @abstractproperty
    def reg_read(self, reg_id):
        pass

    # verify if this instruction implicitly modified register @reg_id
    @abstractproperty
    def reg_write(self, reg_id):
        pass

    # return number of operands having same operand type @op_type
    @abstractproperty
    def op_count(self, op_type):
        pass

    # get the operand at position @position of all operands having the same
    # type @op_type
    @abstractproperty
    def op_find(self, op_type, position):
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
        cs = Cs(arch, mode)
        cs.detail = True
        cs.syntax = 0
        super(CapstoneDisasm, self).__init__(cs)

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

    def disassemble_instruction(self, code, pc):
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
            return self.llil.operaation.name

        @property
        def name(self):
            return self.llil.operation.name[len("LLIL_"):]
