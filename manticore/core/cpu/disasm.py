from abc import abstractproperty, abstractmethod

import capstone as cs

class Instruction(object):
    """Capstone-like instruction to be used internally
    """
    @abstractproperty
    def address(self):
        pass

    @abstractproperty
    def mnemonic(self):
        pass

    @abstractproperty
    def op_str(self):
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
        # offset to account for section vs segment view of the binary
        self.entry_point_diff = None
        # current LowLevelILFunction
        self.current_func = None
        # current pc
        self.current_pc = None
        # queue of il instructions at current PC. If we get called again from
        # the same PC, we will pop from the queue
        self.il_queue = []
        # current il
        self.disasm_il = None

        self.insn_size = None

        # for all UNIMPL insn and other hard times
        # FIXME generalize for other archs
        self.fallback_disasm = CapstoneDisasm(cs.CS_ARCH_X86, cs.CS_MODE_64)

        super(BinjaILDisasm, self).__init__(view)

    def _fix_addr(self, addr):
        # FIXME how to deal with discrepancies of binja vs real program
        # entry point addresses? We need to lookup the symbols and
        # we should make sure all offsets are appropriate

        if self.entry_point_diff is None:
            # assume that the first time we are called, this is the entry point
            self.entry_point_diff = addr - self.view.entry_point

        return addr - self.entry_point_diff

    def _pop_from_il_queue(self, pc):
        # queue contains tuples of the form (idx, il_insn)
        if self.il_queue != []:
            # if we have multiple ils for the same pc
            # pop from the front of the queue
            if self.il_queue[0][1].address == pc:
                return self.il_queue.pop(0)[1]
            else:
                # somehow we have a queue but we are now at a different pc,
                # clear the queue (we might be here because of a CALL etc.)
                # FIXME assert that this is legitimate
                del self.il_queue[:]

        # get current il
        il = self.current_func.get_lifted_il_at(pc)

        # add all other instructions with same address to the queue
        next_idx = il.instr_index + 1
        next_il = self.current_func.lifted_il[next_idx]
        if next_il is None:
            return il
        while next_il.address == pc:
            self.il_queue.append((next_idx, next_il))
            next_idx += 1
            try:
                next_il = self.current_func.lifted_il[next_idx]
            except IndexError:
                break

        # return the current instruction
        return il


    def disassemble_instruction(self, code, pc):
        """Get next instruction based on Capstone disassembler

        :param code: disassembled code
        :param pc: program counter
        """
        import binaryninja.enums as enums

        pc = self._fix_addr(pc)
        blocks = self.view.get_basic_blocks_at(pc)
        if not blocks:
            # Looks like Binja did not know about this PC..
            self.view.create_user_function(pc)
            self.view.update_analysis_and_wait()
            self.current_func = self.view.get_function_at(pc)
        else:
            self.current_func = blocks[0].function

        il = self._pop_from_il_queue(pc)
        self.insn_size = il.size
        self.current_pc = pc
        self.disasm_il = il

        o = il.operation
        if (o == enums.LowLevelILOperation.LLIL_UNIMPL or
                o == enums.LowLevelILOperation.LLIL_UNIMPL_MEM):
            return self.fallback_disasm.disassemble_instruction(code, pc)
        return self.BinjaILInstruction(self.view,
                                       il,
                                       self.entry_point_diff,
                                       self.current_func)


    class BinjaILInstruction(Instruction):
        def __init__(self, view, llil, offset, function):
            self.view = view
            self.llil = llil
            self.function = function
            self.offset = offset
            super(BinjaILDisasm.BinjaILInstruction, self).__init__()

        def _fix_addr(self, addr):
            return addr + self.offset

        @property
        def size(self):
            import binaryninja.enums as enums
            assert self.llil.instr_index < len(self.llil.function)
            try:
                if self.sets_pc:
                    return 0
                else:
                    next_il = self.function.lifted_il[self.llil.instr_index + 1]
                    next_addr = next_il.address
                assert next_addr >= self.llil.address
                return next_addr - self.llil.address
            except IndexError:
                if str(self.llil) == "noreturn":
                    return 0
                else:
                    raise NotImplementedError
            except AssertionError:
                print "ASSERTION ERROR FOR SIZE " + str(self.llil)
                raise AssertionError

        @property
        def mnemonic(self):
            return self.llil.operation.name

        @property
        def op_str(self):
            return " ".join([str(x.op) for x in self.llil.operands])

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

        @property
        def sets_pc(self):
            import binaryninja.enums as enums
            op = self.llil.operation
            return (op == enums.LowLevelILOperation.LLIL_CALL or
                    op == enums.LowLevelILOperation.LLIL_JUMP or
                    op == enums.LowLevelILOperation.LLIL_JUMP_TO or
                    op == enums.LowLevelILOperation.LLIL_IF or
                    op == enums.LowLevelILOperation.LLIL_RET or
                    op == enums.LowLevelILOperation.LLIL_SYSCALL or
                    op == enums.LowLevelILOperation.LLIL_GOTO)

        def __repr__(self):
            return ("%d %s\t%s %s %x") % (self.llil.instr_index,
                                          hex(self.llil.address),
                                          str(self.llil),
                                          self.llil.operation.name,
                                          self.llil.address)

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
