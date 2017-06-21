from abc import abstractmethod

from capstone import Cs

class Instruction(object):
    """Capstone-like instruction to be used internally
    """
    # Return instruction's ID.
    @abstractmethod
    def id(self):
        pass

    # Return instruction's address.
    @abstractmethod
    def address(self):
        pass

    # Return instruction's size.
    @abstractmethod
    def size(self):
        pass

    # return instruction's machine bytes (which should have @size bytes).
    @abstractmethod
    def bytes(self):
        pass

    # return instruction's mnemonic.
    @abstractmethod
    def mnemonic(self):
        pass

    # return instruction's operands (in string).
    @abstractmethod
    def op_str(self):
        pass

    # return list of all implicit registers being read.
    @abstractmethod
    def regs_read(self):
        pass

    # return list of all implicit registers being modified
    @abstractmethod
    def regs_write(self):
        pass

    # return list of semantic groups this instruction belongs to.
    @abstractmethod
    def groups(self):
        pass

    # get the register name, given the register id
    @abstractmethod
    def reg_name(self, reg_id):
        pass

    # get the instruction name
    @abstractmethod
    def insn_name(self):
        pass

    # get the group name
    @abstractmethod
    def group_name(self, group_id):
        pass

    # verify if this insn belong to group with id as @group_id
    @abstractmethod
    def group(self, group_id):
        pass

    # verify if this instruction implicitly read register @reg_id
    @abstractmethod
    def reg_read(self, reg_id):
        pass

    # verify if this instruction implicitly modified register @reg_id
    @abstractmethod
    def reg_write(self, reg_id):
        pass

    # return number of operands having same operand type @op_type
    @abstractmethod
    def op_count(self, op_type):
        pass

    # get the operand at position @position of all operands having the same
    # type @op_type
    @abstractmethod
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

class Capstone(Disasm):

    def __init__(self, arch, mode):
        cs = Cs(arch, mode)
        cs.detail = True
        cs.syntax = 0
        super(Capstone, self).__init__(cs)

    def disassemble_instruction(self, code, pc):
        """Get next instruction based on Capstone disassembler

        :param code: disassembled code
        :param pc: program counter
        """
        return next(self.disasm.disasm(code, pc))

class Binja(Disasm):

    def __init__(self, view):
        self.bv = view
        super(Binja, self).__init__(view)

    def disassemble_instruction(self, code, pc):
        """Get next instruction based on Capstone disassembler

        :param code: disassembled code
        :param pc: program counter
        """
        self.bv.get_disassembly(pc)
