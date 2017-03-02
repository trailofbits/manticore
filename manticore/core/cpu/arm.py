import struct
import sys
from .abstractcpu import Cpu, RegisterFile, Operand
from .abstractcpu import SymbolicPCException, InvalidPCException, Interruption
from .abstractcpu import instruction as abstract_instruction
from .register import Register
from ..smtlib import Operators, Expression
from ...utils.helpers import issymbolic
# from ..smtlib import *
from functools import wraps
from bitwise import *

from capstone import *
from capstone.arm import *
from capstone.x86 import *


# no emulator by default
try:
    from unicorn import *
    from unicorn.x86_const import *
    from unicorn.arm_const import *
except:
    pass
MU = None



# Custom Constants (avoid conflicts with capstone's arm constants)
ARM_REG_APSR_N = 1000
ARM_REG_APSR_Z = 1001
ARM_REG_APSR_C = 1002
ARM_REG_APSR_V = 1003

import logging
logger = logging.getLogger("CPU")

# map different instructions to a single impl here
OP_NAME_MAP = {
    'MOVW': 'MOV'
}

def HighBit(n):
    return Bit(n, 31)

def instruction(body):
    @wraps(body)
    def instruction_implementation(cpu, *args, **kwargs):
        ret = None

        should_execute = cpu.shouldExecuteConditional()

        if issymbolic(should_execute):
            i_size = cpu.address_bit_size / 8
            cpu.PC = Operators.ITEBV(cpu.address_bit_size, should_execute, cpu.PC-i_size,
                    cpu.PC)
            return

        if should_execute:
            ret = body(cpu, *args, **kwargs)

        if cpu.shouldCommitFlags():
            cpu.commitFlags()

        return ret

    return abstract_instruction(instruction_implementation)

class Armv7Operand(Operand):
    def __init__(self, cpu, op, **kwargs):
        super(Armv7Operand, self).__init__(cpu, op, **kwargs)

    def size(self):
        assert self.op.type == ARM_OP_REG
        if self.op.reg >= ARM_REG_D0 and self.op.reg <= ARM_REG_D31:
            return 8
        else:
            return 4

    def read(self, nbits=None, withCarry=False):
        carry = self.cpu.regfile.read(ARM_REG_APSR_C)
        if self.op.type == ARM_OP_REG:
            reg = self.cpu.regfile.read(self.op.reg)
            # XXX This can be an offset of 8, depending on ARM mode
            if self.op.reg == ARM_REG_R15:
                reg += 4
            if self.is_shifted():
                shift = self.op.shift
                reg, carry = self.cpu._Shift(reg, shift.type, shift.value, carry)
            if self.op.subtracted:
                reg = -reg
            if withCarry:
                return reg, carry
            return reg
        elif self.op.type == ARM_OP_IMM:
            imm = self.op.imm
            if self.op.subtracted:
                imm = -imm
            if withCarry:
                return imm, self._getExpandImmCarry(carry)
            return imm

        elif self.op.type == ARM_OP_MEM:
            val = self.cpu.read_int(self.address(), nbits)
            if withCarry:
                return (val, carry)
            return val
        else:
            raise NotImplementedError("readOperand unknown type", self.op.type)

    def write(self, value, nbits=None):
        if self.op.type == ARM_OP_REG:
            self.cpu.regfile.write(self.op.reg, value)
        elif self.op.type == ARM_OP_MEM:
            raise NotImplementedError('need to impl arm store mem')
        else:
            raise NotImplementedError("writeOperand unknown type", self.op.type)

    def writeback(self, value):
        if self.op.type == ARM_OP_REG:
            self.write(value)
        elif self.op.type == ARM_OP_MEM:
            self.cpu.regfile.write(self.op.mem.base, value)
        else:
            raise NotImplementedError("writeback Operand unknown type", self.op.type)

    def is_shifted(self):
        return self.op.shift.type != ARM_SFT_INVALID

    def address(self):
        assert self.op.type == ARM_OP_MEM
        mem = self.op.mem
        addr = self.get_mem_base_addr() + self.get_mem_offset()
        return addr & Mask(self.cpu.address_bit_size)

    def get_mem_offset(self):
        assert self.op.type == ARM_OP_MEM

        mem = self.op.mem
        off = 0
        if mem.index:
            idx = mem.scale * self.cpu.regfile.read(mem.index)
            carry = self.cpu.regfile.read(ARM_REG_APSR_C)
            if self.is_shifted():
                shift = self.op.shift
                idx, carry = self.cpu._Shift(idx, shift.type, shift.value,  carry)
            off = idx
        else:
            off = mem.disp
        return -off if self.op.subtracted else off

    def get_mem_base_addr(self):
        assert self.op.type == ARM_OP_MEM

        mem = self.op.mem
        base = self.cpu.regfile.read(mem.base)

        # If pc is the base, we need to correct for the fact that the ARM
        # spec defines PC to point to the current insn + 8, which we are not
        # compliant with (we do current insn + 4)
        return base+4 if mem.base == ARM_REG_PC else base

    def _getExpandImmCarry(self, carryIn):
        '''Manually compute the carry bit produced by expanding an immediate
        operand (see ARMExpandImm_C)
        '''
        insn = struct.unpack('<I', self.cpu.instruction.bytes)[0]
        unrotated = insn & Mask(8)
        shift = Operators.EXTRACT(insn, 8, 4)
        _, carry = self.cpu._Shift(unrotated, ARM_SFT_ROR, 2*shift, carryIn)
        return carry


class Armv7RegisterFile(RegisterFile):
    REGMAP = {
        ARM_REG_R0: 0,
        ARM_REG_R1: 1,
        ARM_REG_R2: 2,
        ARM_REG_R3: 3,
        ARM_REG_R4: 4,
        ARM_REG_R5: 5,
        ARM_REG_R6: 6,
        ARM_REG_R7: 7,
        ARM_REG_R8: 8,
        ARM_REG_R9: 9,
        ARM_REG_R10: 10,
        ARM_REG_R11: 11,
        ARM_REG_R12: 12,
        ARM_REG_R13: 13,  # alias: ARM_REG_SP
        ARM_REG_R14: 14,  # alias: ARM_REG_LR
        ARM_REG_R15: 15,  # alias: ARM_REG_PC

        ARM_REG_D0: 16,
        ARM_REG_D1: 17,
        ARM_REG_D2: 18,
        ARM_REG_D3: 19,
        ARM_REG_D4: 20,
        ARM_REG_D5: 21,
        ARM_REG_D6: 22,
        ARM_REG_D7: 23,
        ARM_REG_D8: 24,
        ARM_REG_D9: 25,
        ARM_REG_D10: 26,
        ARM_REG_D11: 27,
        ARM_REG_D12: 28,
        ARM_REG_D13: 29,
        ARM_REG_D14: 30,
        ARM_REG_D15: 31,
        ARM_REG_D16: 32,
        ARM_REG_D17: 33,
        ARM_REG_D18: 34,
        ARM_REG_D19: 35,
        ARM_REG_D20: 36,
        ARM_REG_D21: 37,
        ARM_REG_D22: 38,
        ARM_REG_D23: 39,
        ARM_REG_D24: 40,
        ARM_REG_D25: 41,
        ARM_REG_D26: 42,
        ARM_REG_D27: 43,
        ARM_REG_D28: 44,
        ARM_REG_D29: 45,
        ARM_REG_D30: 46,
        ARM_REG_D31: 47,

        ARM_REG_APSR_N: 48,
        ARM_REG_APSR_Z: 49,
        ARM_REG_APSR_C: 50,
        ARM_REG_APSR_V: 51
    }

    def __init__(self):
        '''ARM Register file abstraction. GPRs use ints for read/write. APSR
        flags allow writes of bool/{1, 0} but always read bools.
        '''
        super(Armv7RegisterFile, self).__init__(     )                                                    
        self.aliases = { 'STACK': 'SP',
                                                    'PC': 'PC',  # these three lines are technically unnecessary, but explicit is
                                                    'SP': 'SP',  # better than implicit
                                                    'LR': 'LR',  }#) 
        gpr =  [Register(32) for x in xrange(16)]
        vec = [Register(64) for x in xrange(32)]
        bit_flags = [Register(1) for x in xrange(4)]
        self.regs = gpr + vec + bit_flags

    def read(self, reg_id):
        return self.regs[self.REGMAP[reg_id]].read()

    def write(self, reg_id, val):
        reg_offset = self.REGMAP[reg_id]
        reg = self.regs[reg_offset]
        reg.write(val)

    @property
    def all_registers(self):
        return ('R0','R1','R2','R3','R4','R5','R6','R7','R8','R9','R10','R11','R12','R13','R14','R15','D0','D1','D2',
                'D3','D4','D5','D6','D7','D8','D9','D10','D11','D12','D13','D14','D15','D16','D17','D18','D19','D20',
                'D21','D22','D23','D24','D25','D26','D27','D28','D29','D30','D31','APSR_N','APSR_Z','APSR_C','APSR_V') + ('STACK','PC','SP','LR')

    @property
    def canonical_registers(self):
        return ('R0','R1','R2','R3','R4','R5','R6','R7','R8','R9','R10','R11','R12', 'SP', 'LR', 'PC')

    def reg_name(self, reg_id):
        reg_offset = self.REGMAP[reg_id]
        return self.all_registers[reg_offset]

    def reg_id(self, reg_name):
        reg_name = self.aliases.get(reg_name, reg_name)
        return globals()['ARM_REG_'+reg_name]
            
    def __contains__(self, reg_id):
        return reg_id in self.all_registers

class Armv7Cpu(Cpu):
    '''Note: In this implementation, PC contains address of current
    instruction + 4. However, official spec defines PC to be address of
    current instruction + 8 (section A2.3).
    '''

    address_bit_size = 32
    max_instr_width = 4
    machine = 'armv7'
    arch = CS_ARCH_ARM
    mode = CS_MODE_ARM


    def __init__(self, memory, *args, **kwargs):
        super(Armv7Cpu, self).__init__(Armv7RegisterFile(), memory)
        self._last_flags = {'C': 0, 'V': 0, 'N': 0, 'Z': 0}
        self._force_next = False

    def __getstate__(self):
        state = super(Armv7Cpu, self).__getstate__()
        state['_last_flags'] = self._last_flags
        state['_force_next'] = self._force_next
        return state

    def __setstate__(self, state):
        super(Armv7Cpu, self).__setstate__(state)
        self._last_flags = state['_last_flags']
        self._force_next = state['_force_next']

    def _concretize_registers(cpu, instruction):
        reg_values = {}
        if hasattr(instruction, 'regs_access'):
            (regs_read, regs_write) = instruction.regs_access()
            regs = [ instruction.reg_name(r).upper() for r in regs_read ] 
            regs.append('R15')
        else:
            regs = self.canonical_registers

        logger.debug("Emulator wants this regs %r", regs)
        for reg in regs:
            value = cpu.read_register(reg)
            if issymbolic(value):
                raise ConcretizeRegister(reg, "Passing control to emulator") #FIXME improve exception to handle multiple registers at a time 
            reg_values[reg] = value 

        logger.info("Emulator wants this regs %r", reg_values)
        return reg_values

    def stack_get(self):
        return self.STACK

    def stack_set(self, value):
        self.STACK = value


    def pc_get(self):
        return self.PC
    def pc_set(self, value):
        self.PC=value

    def stack_sub(self, value):
        self.STACK -= value
    def stack_add(self, value):
        self.STACK += value

    # Flags that are the result of arithmetic instructions. Unconditionally
    # set, but conditionally committed.
    #
    # Register file has the actual CPU flags
    def setFlags(self, **flags):
        '''
        Note: For any unupdated flags, update _last_flags with the most recent
        committed value. Otherwise, for example, this could happen:

            overflow=0
            instr1 computes overflow=1, updates _last_flags, doesn't commit
            instr2 updates all flags in _last_flags except overflow (overflow remains 1 in _last_flags)
            instr2 commits all in _last_flags
            now overflow=1 even though it should still be 0
        '''
        unupdated_flags = self._last_flags.viewkeys() - flags.viewkeys()
        for flag in unupdated_flags:
            flag_name = globals()['ARM_REG_APSR_%s'%(flag,)]
            self._last_flags[flag] = self.regfile.read(flag_name)
        self._last_flags.update(flags)

    def commitFlags(self):
        # XXX: capstone incorrectly sets .update_flags for adc
        if self.instruction.mnemonic == 'adc':
            return
        for flag, val in self._last_flags.iteritems():
            flag_name = globals()['ARM_REG_APSR_%s'%(flag,)]
            self.regfile.write(flag_name, val)


    def _Shift(cpu, value, _type, amount, carry):
        assert(_type > ARM_SFT_INVALID and _type <= ARM_SFT_RRX_REG)

        # XXX: Capstone should set the value of an RRX shift to 1, which is
        # asserted in the manual, but it sets it to 0, so we have to check
        if _type in (ARM_SFT_RRX, ARM_SFT_RRX_REG) and amount != 1:
            amount = 1

        if _type in range(ARM_SFT_ASR_REG, ARM_SFT_RRX_REG + 1):
            amount = Operators.EXTRACT(cpu.regfile.read(amount), 0, 8)

        if amount == 0:
            return value, carry

        width = cpu.address_bit_size
        
        if   _type in (ARM_SFT_ASR, ARM_SFT_ASR_REG):
            return ASR_C(value, amount, width)
        elif _type in (ARM_SFT_LSL, ARM_SFT_LSL_REG):
            return LSL_C(value, amount, width)
        elif _type in (ARM_SFT_LSR, ARM_SFT_LSR_REG):
            return LSR_C(value, amount, width)
        elif _type in (ARM_SFT_ROR, ARM_SFT_ROR_REG):
            return ROR_C(value, amount, width)
        elif _type in (ARM_SFT_RRX, ARM_SFT_RRX_REG):
            return RRX_C(value, carry, width)

        raise NotImplementedError("Bad shift value")


    # TODO add to abstract cpu, and potentially remove stacksub/add from it?
    def stack_push(self, data):
        if isinstance(data, (int, long)):
            self.stack_sub(self.address_bit_size/8)
            self.write_int(self.stack_get(), data, self.address_bit_size)
        elif isinstance(data, BitVec):
            self.stack_sub(data.size/8)
            self.write_int(self.stack_get(), data, data.size)
        elif isinstance(data, str):
            self.stack_sub(len(data))
            self.write(self.stack_get(), data)
        else:
            raise NotImplementedError('unsupported type for stack push data')
        return self.stack_get()

    def stack_peek(self, nbytes=4):
        return self.read(self.stack_get(), nbytes)

    def stack_pop(self, nbytes=4):
        # TODO is the distinction between load and read really in the op size?
        nbits = nbytes * 8
        if nbits == self.address_bit_size:
            val = self.read_int(self.stack_get(), nbits)
        else:
            val = self.read(self.stack_get(), nbytes)
        self.stack_add(nbytes)
        return val

    def read(self, addr, nbytes):
        return self.read_bytes(addr, nbytes)

    def write(self, addr, data):
        return self.write_bytes(addr, data)

    @staticmethod
    def canonicalize_instruction_name(instr):
        name = instr.insn_name().upper()
        # XXX bypass a capstone bug that incorrectly labels some insns as mov
        if name == 'MOV':
            if instr.mnemonic.startswith('lsr'):
                return 'LSR'
            elif instr.mnemonic.startswith('lsl'):
                return 'LSL'
        return OP_NAME_MAP.get(name, name)

    def readOperand(self, op):
        if op.type == ARM_OP_REG:
            return self.regfile.read(op.reg)
        elif op.type == ARM_OP_IMM:
            return op.imm
        elif op.type == ARM_OP_MEM:
            raise NotImplementedError('need to impl arm load mem')
        else:
            raise NotImplementedError("readOperand unknown type", op.type)

    def writeOperand(self, op, value):
        if op.type == ARM_OP_REG:
            self.regfile.write(op.reg, value)
        elif op.type == ARM_OP_MEM:
            raise NotImplementedError('need to impl arm store mem')
        else:
            raise NotImplementedError("writeOperand unknown type", op.type)

    def getOperandAddress(self, op):
        # TODO IMPLEMENT
        return -1

    def _wrap_operands(self, ops):
        return [Armv7Operand(self, op) for op in ops]

    def shouldCommitFlags(cpu):
        return cpu.instruction.update_flags

    def forceNextInstruction(cpu):
        cpu._force_next = True

    def shouldExecuteConditional(cpu):
        cc = cpu.instruction.cc
        ret = False

        if cpu._force_next:
            cpu._force_next = False
            return True

        C = cpu.regfile.read(ARM_REG_APSR_C)
        N = cpu.regfile.read(ARM_REG_APSR_N)
        V = cpu.regfile.read(ARM_REG_APSR_V)
        Z = cpu.regfile.read(ARM_REG_APSR_Z)

        if   cc == ARM_CC_AL: ret = True
        elif cc == ARM_CC_EQ: ret = Z
        elif cc == ARM_CC_NE: ret = Operators.NOT(Z)
        elif cc == ARM_CC_HS: ret = C
        elif cc == ARM_CC_LO: ret = Operators.NOT(C)
        elif cc == ARM_CC_MI: ret = N
        elif cc == ARM_CC_PL: ret = Operators.NOT(N)
        elif cc == ARM_CC_VS: ret = V
        elif cc == ARM_CC_VC: ret = Operators.NOT(V)
        elif cc == ARM_CC_HI:
            ret = Operators.AND(C, Operators.NOT(Z)) 
        elif cc == ARM_CC_LS:
            ret = Operators.OR(Operators.NOT(C), Z)
        elif cc == ARM_CC_GE: ret = N == V
        elif cc == ARM_CC_LT: ret = N != V
        elif cc == ARM_CC_GT:
            ret = Operators.AND(Operators.NOT(Z), N == V)
        elif cc == ARM_CC_LE:
            ret = Operators.OR(Z, N != V)
        else:
            raise NotImplementedError("Bad conditional tag")

        return ret

    def getCanonicalRegisters(cpu):
        #TODO: Clean up the way this interacts with the regfile
        names = ['r%d'%(i,) for i in range(13)] + ['sp', 'lr', 'pc']
        values = [cpu.regfile.regs[i].read() for i in range(16)]
        d = dict(zip(names, values))
 
        N = cpu.regfile.read(ARM_REG_APSR_N)
        Z = cpu.regfile.read(ARM_REG_APSR_Z)
        C = cpu.regfile.read(ARM_REG_APSR_C)
        V = cpu.regfile.read(ARM_REG_APSR_V)

        cpsr = 0

        def make_cpsr_flag(flag_expr, offset):
            'Helper for constructing an expression for the CPSR register'
            return Operators.ITEBV(cpu.address_bit_size, flag_expr,
                              BitVecConstant(cpu.address_bit_size, 1 << offset),
                              BitVecConstant(cpu.address_bit_size, 0))
        if any(issymbolic(x) for x in [N, Z, C, V]):
            cpsr = (make_cpsr_flag(N, 31) |
                    make_cpsr_flag(Z, 30) |
                    make_cpsr_flag(C, 29) |
                    make_cpsr_flag(V, 28))
        else:
            if N: cpsr |= 1 << 31
            if Z: cpsr |= 1 << 30
            if C: cpsr |= 1 << 29
            if V: cpsr |= 1 << 28
            
        d['cpsr'] = cpsr

        return d

    def getSyscallRetReg(self):
        return 'r0'
    def get_syscall_description(cpu):
        # EABI standards:
        #  syscall # is in R7
        #  arguments are passed in R0-R6
        #  retval is passed in R0
        index = cpu.regfile.read(ARM_REG_R7)

        arg_indeces = [globals()['ARM_REG_R%d' % i] for i in range(0, 7)]
        arguments = [cpu.regfile.read(idx) for idx in arg_indeces]

        def writeResult(result, cpu = cpu):
            cpu.regfile.write(ARM_REG_R0, result)

        return (index, arguments, writeResult)

    def getSyscallResult(self):
        return self.regfile.read(ARM_REG_R0)

    @instruction
    def MOV(cpu, dest, src):
        '''TODO: MOV imm should technically set carry bit.
              XXX: We now set carry bit when it's a shift operation
           Note: If src operand is PC, temporarily release our logical PC
           view and conform to the spec, which dictates PC = curr instr + 8
        '''
        result, carry = src.read(withCarry=True)
        dest.write(result)

        # Setting flags in two separate setFlags calls clears earlier flags, set
        # it once
        flags = {'N' : HighBit(result),
                 'Z': (result == 0)}
        if src.is_shifted():
            flags['C'] = carry
        cpu.setFlags(**flags)

    def _handleWriteback(cpu, src, dest, offset):
        # capstone bug doesn't set writeback correctly for postindex reg
        if cpu.instruction.writeback or offset:
            if offset:
                off = offset.read()
            else:
                off = dest.get_mem_offset()

            wbaddr = dest.get_mem_base_addr() + off
            dest.writeback(wbaddr)

    def _STR(cpu, width, src, dest, offset=None):
        val = src.read()
        cpu.write_int(dest.address(), val, width)
        cpu._handleWriteback(src, dest, offset)

    @instruction
    def STR(cpu, *args): return cpu._STR(cpu.address_bit_size, *args)

    @instruction
    def STRB(cpu, *args): return cpu._STR(8, *args)

    @instruction
    def STRH(cpu, *args): return cpu._STR(16, *args)

    def _LDR(cpu, dest, src, width, is_signed, offset):
        mem = cpu.read_int(src.address(), width)
        if is_signed:
            word = Operators.SEXTEND(mem, width, cpu.address_bit_size)
        else:
            word = Operators.ZEXTEND(mem, cpu.address_bit_size)
        dest.write(word)
        cpu._handleWriteback(dest, src, offset)

    @instruction
    def LDR(cpu, dest, src, offset=None):
        cpu._LDR(dest, src, 32, False, offset)

    @instruction
    def LDRH(cpu, dest, src, offset=None):
        cpu._LDR(dest, src, 16, False, offset)

    @instruction
    def LDRSH(cpu, dest, src, offset=None):
        cpu._LDR(dest, src, 16, True, offset)

    @instruction
    def LDRB(cpu, dest, src, offset=None):
        cpu._LDR(dest, src, 8, False, offset)

    @instruction
    def LDRSB(cpu, dest, src, offset=None):
        cpu._LDR(dest, src, 8, True, offset)

    def _ADD(cpu, _op1, _op2, carry=0):
        W = cpu.address_bit_size
        # masking to 32 because sometimes capstone's op.imm field is negative.
        # this converts it back to unsigned
        _op2 = Operators.ZEXTEND(_op2, W)

        uo1 = UInt(_op1, W*2)
        uo2 = UInt(_op2, W*2)
        c   = UInt(carry, W*2)
        unsigned_sum = uo1 + uo2 + c 

        so1 = SInt(Operators.SEXTEND(_op1, W, W*2), W*2)
        so2 = SInt(Operators.SEXTEND(_op2, W, W*2), W*2)
        signed_sum = so1 + so2 + c

        result = GetNBits(unsigned_sum, W)

        carry_out = UInt(result, W*2) != unsigned_sum 
        overflow  = SInt(Operators.SEXTEND(result,W,W*2), W*2) != signed_sum

        cpu.setFlags(C=carry_out,
                     V=overflow,
                     N=HighBit(result),
                     Z=result == 0)

        return result, carry_out, overflow

    @instruction
    def ADC(cpu, dest, op1, op2):
        carry = cpu.regfile.read(ARM_REG_APSR_C)
        result, carry, overflow = cpu._ADD(op1.read(), op2.read(), carry)
        dest.write(result)
        return result, carry, overflow

    @instruction
    def ADD(cpu, dest, src, add):
        result, carry, overflow = cpu._ADD(src.read(), add.read())
        dest.write(result)
        return result, carry, overflow

    @instruction
    def RSB(cpu, dest, src, add):
        result, carry, overflow = cpu._ADD(~src.read(), add.read(), 1)
        dest.write(result)
        return result, carry, overflow

    @instruction
    def SUB(cpu, dest, src, add):
        result, carry, overflow = cpu._ADD(src.read(), ~add.read(), 1)
        dest.write(result)
        return result, carry, overflow

    @instruction
    def SBC(cpu, dest, src, add):
        carry = cpu.regfile.read(ARM_REG_APSR_C)
        result, carry, overflow = cpu._ADD(src.read(), ~add.read(), carry)
        dest.write(result)
        return result, carry, overflow

    @instruction
    def B(cpu, dest):
        cpu.PC = dest.read()

    # XXX How should we deal with switching Thumb modes?
    @instruction
    def BX(cpu, dest):
        cpu.PC = dest.read() & ~1

    @instruction
    def BLE(cpu, dest):
        cpu.PC = Operators.ITEBV(cpu.address_bit_size,
                       cpu.regfile.read(ARM_REG_APSR_Z), dest.read(), cpu.PC)

    @instruction
    def BL(cpu, label):
        next_instr_addr = cpu.regfile.read(ARM_REG_PC)
        cpu.regfile.write(ARM_REG_LR, next_instr_addr)
        cpu.regfile.write(ARM_REG_PC, label.read())


    @instruction
    def BLX(cpu, dest):
        ## XXX: Technically, this should use the values that are commented (sub
        ## 2 and LSB of LR set, but we currently do not distinguish between
        ## THUMB and regular modes, so we use the addresses as is. TODO: Handle
        ## thumb correctly and fix this
        target = dest.read()
        next_instr_addr = cpu.regfile.read(ARM_REG_PC) #- 2
        cpu.regfile.write(ARM_REG_LR, next_instr_addr) # | 1)
        cpu.regfile.write(ARM_REG_PC, target & ~1)

    @instruction
    def CMP(cpu, reg, cmp):
        notcmp = ~cmp.read() & Mask(cpu.address_bit_size)
        cpu._ADD(reg.read(), notcmp, 1)

    @instruction
    def POP(cpu, *regs):
        sp = cpu.stack_get()
        invalid = 0

        # "The SP can only be in the list before ARMv7. ARM deprecates any use
        # of ARM instructions that include the SP, and the value of the SP after
        # such an instruction is UNKNOWN" (pg A8-537)
        valid = lambda r: r.op.type == ARM_OP_REG and r.op.reg != ARM_REG_SP

        for reg in regs:
            assert valid(reg)
            val = cpu.stack_pop(cpu.address_bit_size / 8)
            reg.write(val)

    @instruction
    def PUSH(cpu, *regs):
        # ARM deprecates the use of ARM instructions that include the PC in the
        # list (pg A8-539)
        valid = lambda r: r.op.type == ARM_OP_REG and r.op.reg != ARM_REG_PC

        high_to_low_regs = regs[::-1]
        for reg in high_to_low_regs:
            assert valid(reg)
            cpu.stack_push(reg.read())


    @instruction
    def CLZ(cpu, dest, src):

        # Check if the |pos| bit is 1, pos being the offset from the MSB
        value = src.read()
        msb = cpu.address_bit_size - 1
        result = 32

        for pos in xrange(cpu.address_bit_size):
            cond = Operators.EXTRACT(value, pos, 1) == 1
            result = Operators.ITEBV(cpu.address_bit_size, cond, msb-pos, result)

        dest.write(result)

    @instruction
    def NOP(cpu):
        pass

    def _LDM(cpu, insn_id, base, regs):
        '''
        It's technically UNKNOWN if you writeback to a register you loaded into,
        but we let it slide.
        '''
        address = base.read()
        if insn_id == ARM_INS_LDMIB:
            address += cpu.address_bit_size/8

        for reg in regs:
            reg.write(cpu.read_int(address, cpu.address_bit_size))
            address += cpu.address_bit_size/8

        if insn_id == ARM_INS_LDMIB:
            address -= cpu.address_bit_size/8

        if cpu.instruction.writeback:
            base.writeback(address)

    @instruction
    def LDM(cpu, base, *regs):
        cpu._LDM(ARM_INS_LDM, base, regs)

    @instruction
    def LDMIB(cpu, base, *regs):
        cpu._LDM(ARM_INS_LDMIB, base, regs)

    def _STM(cpu, insn_id, base, regs):
        address = base.read()
        if insn_id == ARM_INS_STMIB:
            address += 4

        for reg in regs:
            cpu.write_int(address, reg.read(), cpu.address_bit_size)
            address += 4

        # Undo the last addition if we're in STMIB
        if insn_id == ARM_INS_STMIB:
            address -= 4

        if cpu.instruction.writeback:
            base.writeback(address)

    @instruction
    def STM(cpu, base, *regs):
        cpu._STM(ARM_INS_STM, base, regs)

    @instruction
    def STMIB(cpu, base, *regs):
        cpu._STM(ARM_INS_STMIB, base, regs)

    def _bitwise_instruction(cpu, operation, dest, op1, *op2):
        if op2:
            op2_val, carry = op2[0].read(withCarry=True)
            result = operation(op1.read(), op2_val)
        else:
            op1_val, carry = op1.read(withCarry=True)
            result = operation(op1_val)
        if dest is not None:
            dest.write(result)
        cpu.setFlags(C=carry, N=HighBit(result), Z=(result == 0))

    @instruction
    def ORR(cpu, dest, op1, op2):
        cpu._bitwise_instruction(lambda x, y: x | y, dest, op1, op2)

    @instruction
    def EOR(cpu, dest, op1, op2):
        cpu._bitwise_instruction(lambda x, y: x ^ y, dest, op1, op2)

    @instruction
    def AND(cpu, dest, op1, op2):
        cpu._bitwise_instruction(lambda x, y: x & y, dest, op1, op2)

    @instruction
    def TEQ(cpu, *operands):
        cpu._bitwise_instruction(lambda x, y: x ^ y, None, *operands)
        cpu.commitFlags()

    @instruction
    def TST(cpu, Rn, Rm):
        shifted, carry = Rm.read(withCarry=True)
        result = Rn.read() & shifted
        cpu.setFlags(N=HighBit(result), Z=(result==0), C=carry)

    @instruction
    def SVC(cpu, op):
        if (op.read() != 0):
            logger.warning("Bad SVC number: {:08}".format(op.read()))
        raise Interruption(0)

    @instruction
    def CMN(cpu, src, add):
        result, carry, overflow = cpu._ADD(src.read(), add.read())
        return result, carry, overflow

    def _SR(cpu, insn_id, dest, op, *rest):
        '''_SR reg has @rest, but _SR imm does not, its baked into @op
        '''
        assert insn_id in (ARM_INS_ASR, ARM_INS_LSL, ARM_INS_LSR)

        if insn_id == ARM_INS_ASR:
            srtype = ARM_SFT_ASR_REG
        elif insn_id == ARM_INS_LSL:
            srtype = ARM_SFT_LSL_REG
        elif insn_id == ARM_INS_LSR:
            srtype = ARM_SFT_LSR_REG

        carry = cpu.regfile.read(ARM_REG_APSR_C)
        if rest:
            amount_val = rest[0].op.reg
            result, carry = cpu._Shift(op.read(), srtype, amount_val, carry)
        else:
            result, carry = op.read(withCarry=True)
        dest.write(result)

        cpu.setFlags(N=HighBit(result), Z=(result==0), C=carry)

    @instruction
    def ASR(cpu, dest, op, *rest):
        cpu._SR(ARM_INS_ASR, dest, op, *rest)

    @instruction
    def LSL(cpu, dest, op, *rest):
        cpu._SR(ARM_INS_LSL, dest, op, *rest)

    @instruction
    def LSR(cpu, dest, op, *rest):
        cpu._SR(ARM_INS_LSR, dest, op, *rest)

    @instruction
    def UMULL(cpu, rdlo, rdhi, rn, rm):
        result = UInt(rn.read(), cpu.address_bit_size*2) * UInt(rm.read(), cpu.address_bit_size*2)
        rdhi.write(Operators.EXTRACT(result, cpu.address_bit_size, cpu.address_bit_size))
        rdlo.write(GetNBits(result, cpu.address_bit_size))
        cpu.setFlags(N=Bit(result, 63), Z=(result==0))

    @instruction
    def MUL(cpu, dest, src1, src2):
        width = cpu.address_bit_size
        op1 = SInt(src1.read(), width)
        op2 = SInt(src2.read(), width)
        result = op1 * op2
        dest.write(result & Mask(width))
        cpu.setFlags(N=HighBit(result), Z=(result==0))

    @instruction
    def MVN(cpu,dest, op):
        cpu._bitwise_instruction(lambda x: ~x, dest, op)

    @instruction
    def MLA(cpu, dest, op1, op2, addend):
        width = cpu.address_bit_size
        op1_val = SInt(op1.read(), width)
        op2_val = SInt(op2.read(), width)
        add_val = SInt(addend.read(), width)
        result = op1_val * op2_val + add_val

        dest.write(result & Mask(cpu.address_bit_size))
        cpu.setFlags(N=HighBit(result), Z=(result==0))

    @instruction
    def BIC(cpu, dest, reg, imm):
        result = (reg.read() & ~imm.read()) & Mask(cpu.address_bit_size)
        dest.write(result)
        cpu.setFlags(N=HighBit(result), Z=(result==0))

    def _VSTM(cpu, address, *regs):
        for reg in regs:
            size = reg.size()
            cpu.write_int(address, reg.read(), size * 8)
            address += size

        return address

    @instruction
    def VSTMIA(cpu, base, *regs):
        updated_address = cpu._VSTM(base.read(), *regs)
        if cpu.instruction.writeback:
            base.writeback(updated_address)

    @instruction
    def VSTMDB(cpu, base, *regs):
        address = base.read() - (cpu.address_bit_size / 8) * len(regs)
        updated_address = cpu._VSTM(address, *regs)
        if cpu.instruction.writeback:
            base.writeback(updated_address)

    @instruction
    def STCL(cpu, *operands):
        pass
