import struct
import sys
from .abstractcpu import Abi, SyscallAbi, Cpu, RegisterFile, Operand
from .abstractcpu import SymbolicPCException, InvalidPCException, Interruption
from .abstractcpu import instruction as abstract_instruction
from .register import Register
from ..smtlib import Operators, Expression, BitVecConstant
from ...utils.helpers import issymbolic
# from ..smtlib import *
from functools import wraps
from bitwise import *

from capstone import *
from capstone.arm import *

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

    @property
    def type(self):
        type_map = { ARM_OP_REG: 'register',
                     ARM_OP_MEM: 'memory',
                     ARM_OP_IMM: 'immediate',
                     ARM_OP_PIMM:'coprocessor',
                     ARM_OP_CIMM:'immediate'}

        return type_map[self.op.type]

    @property
    def size(self):
        assert self.type == 'register'
        if self.op.reg >= ARM_REG_D0 and self.op.reg <= ARM_REG_D31:
            return 64
        else:
            #FIXME check other types of operand sizes
            return 32

    def read(self, nbits=None, withCarry=False):
        carry = self.cpu.regfile.read('APSR_C')
        if self.type == 'register':
            value = self.cpu.regfile.read(self.reg)
            # XXX This can be an offset of 8, depending on ARM mode
            if self.reg in ('PC', 'R15'):
                value += 4
            if self.is_shifted():
                shift = self.op.shift
                value, carry = self.cpu._Shift(value, shift.type, shift.value, carry)
            if self.op.subtracted:
                value = -value
            if withCarry:
                return value, carry
            return value
        elif self.type == 'immediate':
            imm = self.op.imm
            if self.op.subtracted:
                imm = -imm
            if withCarry:
                return imm, self._getExpandImmCarry(carry)
            return imm
        elif self.type == 'coprocessor':
            imm = self.op.imm
            return imm
        elif self.type == 'memory':
            val = self.cpu.read_int(self.address(), nbits)
            if withCarry:
                return (val, carry)
            return val
        else:
            raise NotImplementedError("readOperand unknown type", self.op.type)

    def write(self, value, nbits=None):
        if self.type == 'register':
            self.cpu.regfile.write(self.reg, value)
        elif self.type == 'memory':
            raise NotImplementedError('need to impl arm store mem')
        else:
            raise NotImplementedError("writeOperand unknown type", self.op.type)

    def writeback(self, value):
        if self.type == 'register':
            self.write(value)
        elif self.type == 'memory':
            self.cpu.regfile.write(self.mem.base, value)
        else:
            raise NotImplementedError("writeback Operand unknown type", self.op.type)

    def is_shifted(self):
        return self.op.shift.type != ARM_SFT_INVALID

    def address(self):
        assert self.type == 'memory'
        addr = self.get_mem_base_addr() + self.get_mem_offset()
        return addr & Mask(self.cpu.address_bit_size)

    def get_mem_offset(self):
        assert self.type == 'memory'

        off = 0
        if self.mem.index is not None:
            idx = self.mem.scale * self.cpu.regfile.read(self.mem.index)
            carry = self.cpu.regfile.read('APSR_C')
            if self.is_shifted():
                shift = self.op.shift
                idx, carry = self.cpu._Shift(idx, shift.type, shift.value,  carry)
            off = -idx if self.op.subtracted else idx
        else:
            off = self.mem.disp
        return off

    def get_mem_base_addr(self):
        assert self.type == 'memory'

        base = self.cpu.regfile.read(self.mem.base)

        # If pc is the base, we need to correct for the fact that the ARM
        # spec defines PC to point to the current insn + 8, which we are not
        # compliant with (we do current insn + 4)
        return base+4 if self.mem.base in ('PC', 'R15')  else base

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
    def __init__(self):
        '''
        ARM Register file abstraction. GPRs use ints for read/write. APSR
        flags allow writes of bool/{1, 0} but always read bools.
        '''
        super(Armv7RegisterFile, self).__init__({  'SB':'R9', 
                                                   'SL':'R10', 
                                                   'FP':'R11', 
                                                   'IP': 'R12',  
                                                   'STACK': 'R13',
                                                   'SP': 'R13',
                                                   'LR': 'R14',
                                                   'PC': 'R15', } )
        self._regs = { }
        #32 bit registers
        for reg_name in ( 'R0', 'R1', 'R2', 'R3', 'R4', 'R5', 'R6', 'R7', 'R8',
                          'R9', 'R10', 'R11', 'R12', 'R13', 'R14', 'R15' ):
            self._regs[reg_name] = Register(32)
        #64 bit registers
        for reg_name in  ( 'D0', 'D1', 'D2', 'D3', 'D4', 'D5', 'D6', 'D7', 'D8', 
                           'D9', 'D10', 'D11', 'D12', 'D13', 'D14', 'D15', 'D16',
                           'D17', 'D18', 'D19', 'D20', 'D21', 'D22', 'D23', 'D24',
                           'D25', 'D26', 'D27', 'D28', 'D29', 'D30', 'D31'):
            self._regs[reg_name] = Register(64)
        #Flags
        self._regs['APSR_N'] = Register(1)
        self._regs['APSR_Z'] = Register(1)
        self._regs['APSR_C'] = Register(1)
        self._regs['APSR_V'] = Register(1) 

        #MMU Coprocessor  -- to support MCR/MRC for TLS
        self._regs['P15_C13'] = Register(32)

    def _read_APSR(self):
        def make_apsr_flag(flag_expr, offset):
            'Helper for constructing an expression for the APSR register'
            return Operators.ITEBV(32, flag_expr,
                              BitVecConstant(32, 1 << offset),
                              BitVecConstant(32, 0))
        apsr = 0
        N = self.read('APSR_N')
        Z = self.read('APSR_Z')
        C = self.read('APSR_C')
        V = self.read('APSR_V')

        if any(issymbolic(x) for x in [N, Z, C, V]):
            apsr = (make_apsr_flag(N, 31) |
                    make_apsr_flag(Z, 30) |
                    make_apsr_flag(C, 29) |
                    make_apsr_flag(V, 28))
        else:
            if N: apsr |= 1 << 31
            if Z: apsr |= 1 << 30
            if C: apsr |= 1 << 29
            if V: apsr |= 1 << 28
        return apsr 


    def _write_APSR(self, apsr):
        ''' Auxiliary function - Writes flags from a full APSR (only 4 msb used) '''
        V = Operators.EXTRACT(apsr, 28, 1)
        C = Operators.EXTRACT(apsr, 29, 1)
        Z = Operators.EXTRACT(apsr, 30, 1)
        N = Operators.EXTRACT(apsr, 31, 1)

        self.write('APSR_V', V)
        self.write('APSR_C', C)
        self.write('APSR_Z', Z)
        self.write('APSR_N', N)

    def read(self, register):
        assert register in self
        if register == 'APSR':
            return self._read_APSR()
        register = self._alias(register)
        return self._regs[register].read()

    def write(self, register, value):
        assert register in self
        if register == 'APSR':
            return self._write_APSR(value)
        register = self._alias(register)
        self._regs[register].write(value)

    @property
    def all_registers(self):
        return super(Armv7RegisterFile, self).all_registers + \
                ('R0','R1','R2','R3','R4','R5','R6','R7','R8','R9','R10','R11','R12','R13','R14','R15','D0','D1','D2',
                'D3','D4','D5','D6','D7','D8','D9','D10','D11','D12','D13','D14','D15','D16','D17','D18','D19','D20',
                'D21','D22','D23','D24','D25','D26','D27','D28','D29','D30','D31','APSR','APSR_N','APSR_Z','APSR_C','APSR_V',
                'P15_C13')

    @property
    def canonical_registers(self):
        return ('R0','R1','R2','R3','R4','R5','R6','R7','R8','R9','R10','R11','R12','R13','R14','R15','APSR')


class Armv7LinuxSyscallAbi(SyscallAbi):
    '''
    ARMv7 Linux system call ABI
    '''
    # EABI standards:
    #  syscall # is in R7
    #  arguments are passed in R0-R6
    #  retval is passed in R0
    def syscall_number(self):
        return self._cpu.R7

    def get_arguments(self):
        for i in range(6):
            yield 'R{}'.format(i)

    def write_result(self, result):
        self._cpu.R0 = result

class Armv7CdeclAbi(Abi):
    '''
    ARMv7 Cdecl function call ABI
    '''
    def get_arguments(self):
        # First four passed via R0-R3, then on stack
        for reg in ('R0', 'R1', 'R2', 'R3'):
            yield reg

        for address in self.values_from(self._cpu.STACK):
            yield address

    def write_result(self, result):
        self._cpu.R0 = result

    def ret(self):
        self._cpu.PC = self._cpu.LR 

class Armv7Cpu(Cpu):
    '''
    Cpu specialization handling the ARMv7 architecture.

    Note: In this implementation, PC contains address of current
    instruction + 4. However, official spec defines PC to be address of
    current instruction + 8 (section A2.3).
    '''

    address_bit_size = 32
    max_instr_width = 4
    machine = 'armv7'
    arch = CS_ARCH_ARM
    mode = CS_MODE_ARM


    def __init__(self, memory):
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

    def _set_mode(self, new_mode):
		assert new_mode in (CS_MODE_ARM, CS_MODE_THUMB)
		self.mode = new_mode
		self._md.mode = new_mode

    # Flags that are the result of arithmetic instructions. Unconditionally
    # set, but conditionally committed.
    #
    # Register file has the actual CPU flags
    def setFlags(self, **flags):
        '''
        Note: For any unmodified flags, update _last_flags with the most recent
        committed value. Otherwise, for example, this could happen:

            overflow=0
            instr1 computes overflow=1, updates _last_flags, doesn't commit
            instr2 updates all flags in _last_flags except overflow (overflow remains 1 in _last_flags)
            instr2 commits all in _last_flags
            now overflow=1 even though it should still be 0
        '''
        unupdated_flags = self._last_flags.viewkeys() - flags.viewkeys()
        for flag in unupdated_flags:
            flag_name = 'APSR_{}'.format(flag)
            self._last_flags[flag] = self.regfile.read(flag_name)
        self._last_flags.update(flags)

    def commitFlags(self):
        # XXX: capstone incorrectly sets .update_flags for adc
        if self.instruction.mnemonic == 'adc':
            return
        for flag, val in self._last_flags.iteritems():
            flag_name = 'APSR_{}'.format(flag)
            self.regfile.write(flag_name, val)


    def _Shift(cpu, value, _type, amount, carry):
        assert(_type > ARM_SFT_INVALID and _type <= ARM_SFT_RRX_REG)

        # XXX: Capstone should set the value of an RRX shift to 1, which is
        # asserted in the manual, but it sets it to 0, so we have to check
        if _type in (ARM_SFT_RRX, ARM_SFT_RRX_REG) and amount != 1:
            amount = 1

        elif _type in range(ARM_SFT_ASR_REG, ARM_SFT_RRX_REG + 1):
            amount = cpu.instruction.reg_name(amount).upper()
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
    def stack_push(self, data, nbytes=None):
        if isinstance(data, (int, long)):
            nbytes = nbytes or self.address_bit_size/8
            self.SP -= nbytes
            self.write_int(self.SP, data, nbytes * 8)
        elif isinstance(data, BitVec):
            self.SP -= data.size/8
            self.write_int(self.SP, data, data.size)
        elif isinstance(data, str):
            self.SP -= len(data)
            self.write(self.SP, data)
        else:
            raise NotImplementedError('unsupported type for stack push data')
        return self.SP

    def stack_peek(self, nbytes=4):
        return self.read(self.SP, nbytes)

    def stack_pop(self, nbytes=4):
        # TODO is the distinction between load and read really in the op size?
        nbits = nbytes * 8
        if nbits == self.address_bit_size:
            val = self.read_int(self.SP, nbits)
        else:
            val = self.read(self.SP, nbytes)
        self.SP += nbytes
        return val

    def read(self, addr, nbytes):
        return self.read_bytes(addr, nbytes)

    def write(self, addr, data):
        return self.write_bytes(addr, data)

    def set_arm_tls(self, data):
        self.regfile.write('P15_C13', data)

    @staticmethod
    def canonicalize_instruction_name(instr):
        name = instr.insn_name().upper()
        # XXX bypass a capstone bug that incorrectly labels some insns as mov
        if name == 'MOV':
            if instr.mnemonic.startswith('lsr'):
                return 'LSR'
            elif instr.mnemonic.startswith('lsl'):
                return 'LSL'
            elif instr.mnemonic.startswith('asr'):
                return 'ASR'
        return OP_NAME_MAP.get(name, name)

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

        C = cpu.regfile.read('APSR_C')
        N = cpu.regfile.read('APSR_N')
        V = cpu.regfile.read('APSR_V')
        Z = cpu.regfile.read('APSR_Z')

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

    @instruction
    def MOV(cpu, dest, src):
        '''
        Implement the MOV{S} instruction.

        Note: If src operand is PC, temporarily release our logical PC
        view and conform to the spec, which dictates PC = curr instr + 8

        :param Armv7Operand dest: The destination operand; register.
        :param Armv7Operand src: The source operand; register or immediate.
        '''
        result, carry_out = src.read(withCarry=True)
        dest.write(result)
        cpu.setFlags(C=carry_out, N=HighBit(result), Z=(result == 0))

    @instruction
    def MOVT(cpu, dest, src):
        '''
        MOVT writes imm16 to Rd[31:16]. The write does not affect Rd[15:0].

        :param Armv7Operand dest: The destination operand; register
        :param Armv7Operand src: The source operand; 16-bit immediate
        '''
        assert src.type == 'immediate'
        imm = src.read()
        low_halfword = dest.read() & Mask(16)
        dest.write((imm << 16) | low_halfword)

    @instruction
    def MRC(cpu, coprocessor, opcode1, dest, coprocessor_reg_n, coprocessor_reg_m, opcode2):
        '''
        MRC moves to ARM register from coprocessor.

        :param Armv7Operand coprocessor: The name of the coprocessor; immediate
        :param Armv7Operand opcode1: coprocessor specific opcode; 3-bit immediate
        :param Armv7Operand dest: the destination operand: register
        :param Armv7Operand coprocessor_reg_n: the coprocessor register; immediate
        :param Armv7Operand coprocessor_reg_m: the coprocessor register; immediate
        :param Armv7Operand opcode2: coprocessor specific opcode; 3-bit immediate
        '''
        assert coprocessor.type == 'coprocessor'
        assert opcode1.type == 'immediate'
        assert opcode2.type == 'immediate'
        assert dest.type == 'register'
        imm_coprocessor = coprocessor.read()
        imm_opcode1 = opcode1.read()
        imm_opcode2 = opcode2.read()
        coprocessor_n_name = coprocessor_reg_n.read()
        coprocessor_m_name = coprocessor_reg_m.read()

        if 15 == imm_coprocessor: #MMU
            if 0 == imm_opcode1:
                if 13 == coprocessor_n_name:
                    if 3 == imm_opcode2:
                        dest.write(cpu.regfile.read('P15_C13'))
                        return
        raise NotImplementedError("MRC: unimplemented combination of coprocessor, opcode, and coprocessor register")

    @instruction
    def LDREX(cpu, dest, src, offset=None):
        '''
        LDREX loads data from memory.
        * If the physical address has the shared TLB attribute, LDREX
          tags the physical address as exclusive access for the current
          processor, and clears any exclusive access tag for this
          processor for any other physical address.
        * Otherwise, it tags the fact that the executing processor has
          an outstanding tagged physical address.

        :param Armv7Operand dest: the destination register; register
        :param Armv7Operand src: the source operand: register
        '''
        #TODO: add lock mechanism to underlying memory --GR, 2017-06-06
        cpu._LDR(dest, src, 32, False, offset)

    @instruction
    def STREX(cpu, status, *args):
        '''
        STREX performs a conditional store to memory.
        :param Armv7Operand status: the destination register for the returned status; register
        '''
        #TODO: implement conditional return with appropriate status --GR, 2017-06-06
        status.write(0)
        return cpu._STR(cpu.address_bit_size, *args)

    @instruction
    def UXTB(cpu, dest, src):
        '''
        UXTB extracts an 8-bit value from a register, zero-extends
        it to the size of the register, and writes the result to the destination register.

        :param ARMv7Operand dest: the destination register; register
        :param ARMv7Operand dest: the source register; register
        '''
        val = GetNBits(src.read(), 8)
        word = Operators.ZEXTEND(val, cpu.address_bit_size)
        dest.write(word)

    @instruction
    def PLD(cpu, addr, offset=None):
        '''
        PLD instructs the cpu that the address at addr might be loaded soon.
        '''
        pass

    def _compute_writeback(cpu, operand, offset):
        if offset:
            off = offset.read()
        else:
            off = operand.get_mem_offset()
        wbaddr = operand.get_mem_base_addr() + off
        return wbaddr

    def _cs_hack_ldr_str_writeback(cpu, operand, offset, val):
        # capstone bug doesn't set writeback correctly for postindex reg
        if cpu.instruction.writeback or offset:
            operand.writeback(val)

    def _STR(cpu, width, src, dest, offset=None):
        val = src.read()
        writeback = cpu._compute_writeback(dest, offset)
        cpu.write_int(dest.address(), val, width)
        cpu._cs_hack_ldr_str_writeback(dest, offset, writeback)

    @instruction
    def STR(cpu, *args): return cpu._STR(cpu.address_bit_size, *args)

    @instruction
    def STRB(cpu, *args): return cpu._STR(8, *args)

    @instruction
    def STRH(cpu, *args): return cpu._STR(16, *args)

    def _LDR(cpu, dest, src, width, is_signed, offset):
        mem = cpu.read_int(src.address(), width)
        writeback = cpu._compute_writeback(src, offset)
        if is_signed:
            word = Operators.SEXTEND(mem, width, cpu.address_bit_size)
        else:
            word = Operators.ZEXTEND(mem, cpu.address_bit_size)
        dest.write(word)
        cpu._cs_hack_ldr_str_writeback(src, offset, writeback)

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
        carry = cpu.regfile.read('APSR_C')
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
        inv_src = GetNBits(~src.read(), cpu.address_bit_size)
        result, carry, overflow = cpu._ADD(inv_src, add.read(), 1)
        dest.write(result)
        return result, carry, overflow

    @instruction
    def RSC(cpu, dest, src, add):
        carry = cpu.regfile.read('APSR_C')
        inv_src = GetNBits(~src.read(), cpu.address_bit_size)
        result, carry, overflow = cpu._ADD(inv_src, add.read(), carry)
        dest.write(result)
        return result, carry, overflow

    @instruction
    def SUB(cpu, dest, src, add):
        result, carry, overflow = cpu._ADD(src.read(), ~add.read(), 1)
        dest.write(result)
        return result, carry, overflow

    @instruction
    def SBC(cpu, dest, src, add):
        carry = cpu.regfile.read('APSR_C')
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
                       cpu.regfile.read('APSR_Z'), dest.read(), cpu.PC)

    @instruction
    def BL(cpu, label):
        next_instr_addr = cpu.regfile.read('PC')
        cpu.regfile.write('LR', next_instr_addr)
        cpu.regfile.write('PC', label.read())


    @instruction
    def BLX(cpu, dest):
        ## XXX: Technically, this should use the values that are commented (sub
        ## 2 and LSB of LR set, but we currently do not distinguish between
        ## THUMB and regular modes, so we use the addresses as is. TODO: Handle
        ## thumb correctly and fix this
        address = cpu.PC
        target = dest.read()
        next_instr_addr = cpu.regfile.read('PC') #- 2
        cpu.regfile.write('LR', next_instr_addr) # | 1)
        cpu.regfile.write('PC', target & ~1)

        ## The `blx <label>` form of this instruction forces a state swap
        if dest.type=='immediate':
            logger.debug("swapping ds mode due to BLX at inst 0x{:x}".format(address))
            #swap from arm to thumb or back
            assert cpu.mode in (CS_MODE_ARM, CS_MODE_THUMB)
            if cpu.mode == CS_MODE_ARM:
                cpu._set_mode(CS_MODE_THUMB)
            else:
                cpu._set_mode(CS_MODE_ARM)

    @instruction
    def CMP(cpu, reg, cmp):
        notcmp = ~cmp.read() & Mask(cpu.address_bit_size)
        cpu._ADD(reg.read(), notcmp, 1)

    @instruction
    def POP(cpu, *regs):
        for reg in regs:
            val = cpu.stack_pop(cpu.address_bit_size / 8)
            reg.write(val)

    @instruction
    def PUSH(cpu, *regs):
        high_to_low_regs = [r.read() for r in regs[::-1]]
        for reg in high_to_low_regs:
            cpu.stack_push(reg)


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
            address += reg.size/8

        if insn_id == ARM_INS_LDMIB:
            address -= reg.size/8

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
        if op.read() != 0:
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

        carry = cpu.regfile.read('APSR_C')
        if rest:
            #FIXME we should make Operand.op private (and not accessible)
            result, carry = cpu._Shift(op.read(), srtype, rest[0].op.reg, carry)
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
            cpu.write_int(address, reg.read(), reg.size)
            address += reg.size/8

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
    def VLDMIA(cpu, base, *regs):
        cpu._LDM(ARM_INS_VLDMIA, base, regs)

    @instruction
    def STCL(cpu, *operands):
        pass

    @instruction
    def DMB(cpu, *operands):
        '''
        Used by the the __kuser_dmb ARM Linux user-space handler. This is a nop
        under Manticore's memory and execution model.
        '''
        pass

    @instruction
    def LDCL(cpu, *operands):
        '''
        Occasionally used in glibc (longjmp in ld.so). Nop under our execution model.
        '''
        pass
