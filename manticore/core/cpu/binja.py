import logging
from collections import defaultdict

from .abstractcpu import (
    Abi, SyscallAbi, Cpu, RegisterFile, Operand, instruction,
    ConcretizeRegister, ConcretizeRegister, ConcretizeArgument, Interruption,
    Syscall
)

from ...core.memory import SMemory32, SMemory64
from ...core.cpu.disasm import BinjaILDisasm

logger = logging.getLogger("CPU")

class BinjaRegisterFile(RegisterFile):

    def __init__(self, view):
        '''
        ARM Register file abstraction. GPRs use ints for read/write. APSR
        flags allow writes of bool/{1, 0} but always read bools.
        '''
        self.reg_aliases = {
            'STACK' : str(view.arch.stack_pointer),
            'PC' : self._get_pc(view),
        }

        super(BinjaRegisterFile, self).__init__(aliases=self.reg_aliases)

        # Initialize register values, cache and side-effects
        self._cache = dict()
        self.flags = {f : 0 for f in view.arch.flags}
        all_regs = view.arch.regs.keys() + self.reg_aliases.values()
        self.registers = {reg : 0 for reg in all_regs}
        # FIXME (theo) get side effects

    def write(self, reg, value):
        reg = self._alias(str(reg))
        # FIXME we will need to be calling the appropriate setters as in x86
        self._update_cache(reg, value)
        return value

    def read(self, reg):
        reg = self._alias(str(reg))
        if reg in self._cache:
            return self._cache[reg]

        # FIXME we will need to be calling the appropriate getters as in x86
        value = self.registers[reg]
        # FIXME we should read via get_register
        self._cache[reg] = value
        return value

    def _update_cache(self, reg, value):
        reg = self._alias(str(reg))
        self._cache[reg] = value

    @property
    def all_registers(self):
        return tuple(self.registers.keys() + self._aliases.keys())

    @property
    def canonical_registers(self):
        return tuple(self.registers.keys())

    def __contains__(self, register):
        return register in self.all_registers

    def _get_pc(self, view):
        from binaryninja import Architecture

        if view.arch == Architecture['x86']:
            return 'eip'
        elif view.arch == Architecture['x86_64']:
            return 'rip'
        else:
            raise NotImplementedError

class BinjaOperand(Operand):
    def __init__(self, cpu, op, **kwargs):
        if hasattr(op, "operands") and op.operands:
            op.operands = [BinjaOperand(cpu, x) for x in op.operands]
        super(BinjaOperand, self).__init__(cpu, op, **kwargs)

    @property
    def type(self):
        from binaryninja import lowlevelil as il
        type_map = {
            il.ILRegister: 'register',
            il.LowLevelILInstruction: 'instruction',
        }

        try:
            t = type_map.get(type(self.op), None)
        except Exception as e:
            print "ERROR IN type lookup " + str(type(self.op))
            raise e
        return t

    @property
    def size(self):
        # FIXME (does this assert need to be here? we could be reading memory)
        #  assert self.type == 'register'
        return self.op.info.size

    def read(self):
        #  try:
            #  raise NotImplementedError("READ " + str(self.op))
        #  except Exception as e:
            #  import traceback
            #  traceback.print_stack()
        cpu, op = self.cpu, self.op
        if self.type == 'register':
            value = cpu.read_register(self.op)
            #  print("Reading %d from %s" % (value, op))
            return value
        elif self.type == 'instruction':
            # FIXME change to check the enum instead of doing strcmp
            if op.operation.name[len("LLIL_"):] == "CONST":
                # FIXME ugly hack to see if the CONST is a CONST_PTR
                # It is always the source that might be a const pointer, but
                # this information seems to only be present in LowLevelIL?
                llil = cpu.view.current_func.get_low_level_il_at(op.address)
                if (hasattr(llil, 'src') and
                        llil.src.operation.name == "LLIL_CONST_PTR"):
                    implementation = getattr(cpu, "CONST_PTR")
                    return implementation(*op.operands)

            implementation = getattr(cpu, op.operation.name[len("LLIL_"):])
            if op.operation.name == "LLIL_LOAD":
                return implementation(*op.operands, expr_size=op.size)
            return implementation(*op.operands)

    def write(self, value):
        cpu, op = self.cpu, self.op
        if self.type == 'register':
            #  print("Writing %d to %s" % (value, op))
            cpu.write_register(str(op), value)
        else:
            raise NotImplementedError("write_operand type", o.type)
        return value & ((1 << self.size) - 1)

    def __getattr__(self, name):
        return getattr(self.op, name)

class BinjaCpu(Cpu):
    '''
    A Virtual CPU model for Binary Ninja's IL
    '''

    # Will be initialized based on the underlying Binja Architecture
    max_instr_width = None
    address_bit_size = None
    machine = 'binja_il'
    arch = None
    mode = None
    disasm = None
    view = None
    instr_ptr = None
    stack_ptr = None
    # Keep a virtual stack
    stack = []

    # FIXME
    # FIXME
    # FIXME         NO FLAGS WHATSOEVER IN THE @instruction implementations
    #               XXX perhaps utilize a decorator for this?
    # FIXME
    # FIXME
    # FIXME
    def __init__(self, view, memory):
        '''
        Builds a CPU model.
        :param view: BinaryNinja view.
        '''
        self.__class__.view = view
        self.__class__.max_instr_width = view.arch.max_instr_length
        self.__class__.address_bit_size = 8 * view.arch.address_size
        self.__class__.arch = view.arch
        self.__class__.disasm = BinjaILDisasm(view)
        self._segments = {}
        # initialize the memory and register files
        super(BinjaCpu, self).__init__(BinjaRegisterFile(view), memory)

    @property
    def function_hooks(self):
        return dict(self._function_hooks)

    @property
    def instr_hooks(self):
        return defaultdict(list, self._instr_hooks)

    def __getstate__(self):
        state = super(BinjaCpu, self).__getstate__()
        state['segments'] = self._segments
        return state

    def __setstate__(self, state):
        self._segments = state['segments']
        super(BinjaCpu, self).__setstate__(state)

    # FIXME (theo) that should no longer be necessary once we move everything
    # to using manticore Instruction()
    def canonicalize_instruction_name(self, insn):
        return insn.name

    def set_descriptor(self, selector, base, limit, perms):
        assert selector > 0 and selector < 0xffff
        assert base >= 0 and base < (1 << self.address_bit_size)
        assert limit >= 0 and limit < 0xffff or limit & 0xfff == 0
        self._segments[selector] = (base, limit, perms)

    def get_descriptor(self, selector):
        return self._segments.setdefault(selector, (0, 0xfffff000, 'rwx'))

    def _wrap_operands(self, operands):
        return [BinjaOperand(self, op) for op in operands]

    def push(cpu, value, size):
        '''
        Writes a value in the stack.

        :param value: the value to put in the stack.
        :param size: the size of the value.
        '''
        cpu.STACK -= size / 8
        base, _, _ = cpu.get_descriptor(cpu.ss)
        address = cpu.STACK + base
        cpu.write_int(address, value, size)

    def pop(cpu, size):
        '''
        Gets a value from the stack.

        :rtype: int
        :param size: the size of the value to consume from the stack.
        :return: the value from the stack.
        '''
        base, _, _ = cpu.get_descriptor(cpu.ss)
        address = cpu.STACK + base
        value = cpu.read_int(address, size)
        cpu.STACK += size / 8
        return value

    @instruction
    def ADC(cpu):
        raise NotImplementedError

    @instruction
    def ADD(cpu, left, right):
        return left.read() + right.read()

    @instruction
    def ADD_OVERFLOW(cpu):
        raise NotImplementedError

    @instruction
    def AND(cpu, left, right):
        return left.read() & right.read()

    @instruction
    def ASR(cpu, reg, shift):
        return reg.read() >> shift.read()

    @instruction
    def BOOL_TO_INT(cpu):
        raise NotImplementedError
    @instruction
    def BP(cpu):
        raise NotImplementedError

    @instruction
    def CALL(cpu, expr):
        new_pc = long(str(expr.op), 16) + cpu.disasm.entry_point_diff
        cpu.regfile.write('PC', new_pc)
        cpu.__class__.PC = new_pc
        cpu.push(new_pc, cpu.address_bit_size)

    @instruction
    def CMP_E(cpu):
        raise NotImplementedError
    @instruction
    def CMP_NE(cpu):
        raise NotImplementedError
    @instruction
    def CMP_SGE(cpu):
        raise NotImplementedError
    @instruction
    def CMP_SGT(cpu):
        raise NotImplementedError
    @instruction
    def CMP_SLE(cpu):
        raise NotImplementedError
    @instruction
    def CMP_SLT(cpu):
        raise NotImplementedError
    @instruction
    def CMP_UGE(cpu):
        raise NotImplementedError
    @instruction
    def CMP_UGT(cpu):
        raise NotImplementedError
    @instruction
    def CMP_ULE(cpu):
        raise NotImplementedError
    @instruction
    def CMP_ULT(cpu):
        raise NotImplementedError

    @instruction
    def CONST(cpu, expr):
        return expr.op

    @instruction
    def CONST_PTR(cpu, expr):
        val = expr.op + cpu.disasm.entry_point_diff
        return expr.op + cpu.disasm.entry_point_diff

    @instruction
    def DIVS(cpu):
        raise NotImplementedError
    @instruction
    def DIVS_DP(cpu):
        raise NotImplementedError
    @instruction
    def DIVU(cpu):
        raise NotImplementedError
    @instruction
    def DIVU_DP(cpu):
        raise NotImplementedError
    @instruction
    def FLAG(cpu):
        raise NotImplementedError
    @instruction
    def FLAG_BIT(cpu):
        raise NotImplementedError

    @instruction
    def FLAG_COND(cpu, condition):
        return condition.op

    @instruction
    def GOTO(cpu, expr):
        if isinstance(expr.op, long):
            addr = cpu.view.current_func.lifted_il[expr.op].address
        else:
            raise NotImplementedError
        cpu.__class__.PC = addr + cpu.disasm.entry_point_diff

    @instruction
    def IF(cpu, condition, true, false):
        cond = condition.read()

        import binaryninja.enums as enums

        # FLAGS are ['c', 'p', 'a', 'z', 's', 'd', 'o']
        # FIXME check these for correctness. Probably buggy!!
        if cond == enums.LowLevelILFlagCondition.LLFC_E:
            res = (cpu.regfile.flags['z'] == 1)
        elif cond == enums.LowLevelILFlagCondition.LLFC_NE:
            res = (cpu.regfile.flags['z'] == 0)
        elif cond == enums.LowLevelILFlagCondition.LLFC_NEG:
            print cond
            raise NotImplementedError
        elif cond == enums.LowLevelILFlagCondition.LLFC_NO:
            res = (cpu.regfile.flags['o'] == 0)
        elif cond == enums.LowLevelILFlagCondition.LLFC_O:
            res = (cpu.regfile.flags['o'] == 1)
        elif cond == enums.LowLevelILFlagCondition.LLFC_POS:
            print cond
            raise NotImplementedError
        elif cond == enums.LowLevelILFlagCondition.LLFC_SGE:
            print cond
            raise NotImplementedError
        elif cond == enums.LowLevelILFlagCondition.LLFC_SGT:
            print cond
            raise NotImplementedError
        elif cond == enums.LowLevelILFlagCondition.LLFC_SLE:
            print cond
            raise NotImplementedError
        elif cond == enums.LowLevelILFlagCondition.LLFC_SLT:
            print cond
            raise NotImplementedError
        elif cond == enums.LowLevelILFlagCondition.LLFC_UGE:
            res = (cpu.regfile.flags['c'] == 0)
        elif cond == enums.LowLevelILFlagCondition.LLFC_UGT:
            res = ((cpu.regfile.flags['z'] & cpu.regfile.flags['c']) == 0)
        elif cond == enums.LowLevelILFlagCondition.LLFC_ULE:
            res = ((cpu.regfile.flags['z'] | cpu.regfile.flags['c']) == 1)
        elif cond == enums.LowLevelILFlagCondition.LLFC_ULT:
            res = (cpu.regfile.flags['c'] == 1)
        else:
            print cond
            raise NotImplementedError

        idx = true.op if res else false.op
        assert isinstance(idx, long)
        print false.op
        print true.op
        addr = cpu.view.current_func.lifted_il[idx].address
        assert addr != cpu.disasm.current_pc
        print "JUMPING AT " + hex(addr)
        cpu.__class__.PC = addr + cpu.disasm.entry_point_diff

    @instruction
    def JUMP(cpu, expr):
        addr = expr.read()
        cpu.regfile.write('PC', addr)
        cpu.__class__.PC = addr

    @instruction
    def JUMP_TO(cpu):
        raise NotImplementedError

    @instruction
    def LOAD(cpu, expr, expr_size=None):
        return cpu.read_int(expr.read(), expr_size * 8)

    @instruction
    def LOW_PART(cpu, expr):
        # FIXME account for the size this is currently wrong. should
        # read() handle this or not?
        return expr.read()

    @instruction
    def LSL(cpu, reg, shift):
        # FIXME ALL FLAGS
        return reg.read() << shift.read()

    @instruction
    def LSR(cpu):
        raise NotImplementedError
    @instruction
    def MODS(cpu):
        raise NotImplementedError
    @instruction
    def MODS_DP(cpu):
        raise NotImplementedError
    @instruction
    def MODU(cpu):
        raise NotImplementedError
    @instruction
    def MODU_DP(cpu):
        raise NotImplementedError

    @instruction
    def MUL(cpu, left, right):
        return left.read() * right.read()

    @instruction
    def MULS_DP(cpu):
        raise NotImplementedError
    @instruction
    def MULU_DP(cpu):
        raise NotImplementedError
    @instruction
    def NEG(cpu):
        raise NotImplementedError
    @instruction
    def NOP(cpu):
        return

    @instruction
    def NORET(cpu):
        raise NotImplementedError
    @instruction
    def NOT(cpu):
        raise NotImplementedError

    @instruction
    def OR(cpu, left, right):
        return left.read() | right.read()

    @instruction
    def POP(cpu):
        # FIXME this is wrong! get it from the destination register!
        return cpu.pop(cpu.address_bit_size)

    @instruction
    def PUSH(cpu, src):
        cpu.push(src.read(), src.op.size * 8)

    @instruction
    def REG(cpu, expr):
        return cpu.regfile.read(expr.op)

    @instruction
    def RET(cpu):
        raise NotImplementedError
    @instruction
    def RLC(cpu):
        raise NotImplementedError
    @instruction
    def ROL(cpu):
        raise NotImplementedError
    @instruction
    def ROR(cpu):
        raise NotImplementedError
    @instruction
    def RRC(cpu):
        raise NotImplementedError
    @instruction
    def SBB(cpu):
        raise NotImplementedError
    @instruction
    def SET_FLAG(cpu):
        raise NotImplementedError

    @instruction
    def SET_REG(cpu, dest, src):
        dest.write(src.read())

    @instruction
    def SET_REG_SPLIT(cpu):
        raise NotImplementedError

    @instruction
    def STORE(cpu, dest, src):
        cpu.write_int(dest.read(), src.read(), src.size * 8)

    @instruction
    def SUB(cpu, left, right):
        # FIXME ALL FLAGS AFFECTED
        return left.read() - right.read()

    @instruction
    def SX(cpu):
        raise NotImplementedError
    @instruction
    def SYSCALL(cpu):
        raise NotImplementedError
    @instruction
    def TEST_BIT(cpu):
        raise NotImplementedError
    @instruction
    def TRAP(cpu):
        raise NotImplementedError
    @instruction
    def UNDEF(cpu):
        raise NotImplementedError

    @instruction
    def UNIMPL(cpu):
        # FIXME invoke platform-specific CPU here
        disasm = cpu.view.get_disassembly(cpu.disasm.current_pc)
        if disasm == "rdtsc":
            val = cpu.icount
            cpu.regfile.write('rax', val & 0xffffffff)
            cpu.regfile.write('rdx', (val >> 32) & 0xffffffff)
            return
        raise NotImplementedError

    @instruction
    def UNIMPL_MEM(cpu):
        raise NotImplementedError

    @instruction
    def XOR(cpu, left, right):
        # FIXME Flags?
        if str(left) == str(right):
            return 0
        return left.read() ^ right.read()

    @instruction
    def ZX(cpu, expr):
        # FIXME zero extension
        val = expr.read()
        return val
