
import unittest
from manticore.core.cpu.x86 import *
from manticore.core.smtlib import Operators
from manticore.core.memory import *


class CPUTest(unittest.TestCase):
    _multiprocess_can_split_ = True
    class ROOperand(object):
        ''' Mocking class for operand ronly '''
        def __init__(self, size, value):
            self.size = size
            self.value = value
        def read(self):
            return self.value & ((1<<self.size)-1)

    class RWOperand(ROOperand):
        ''' Mocking class for operand rw '''
        def write(self, value):
            self.value = value & ((1<<self.size)-1)
            return self.value



    def test_MOVHPD_1(self):
        ''' Instruction MOVHPD_1
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a24000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df294e] = b'f'
        mem[0x7ffff7df294f] = b'\x0f'
        mem[0x7ffff7df2950] = b'\x16'
        mem[0x7ffff7a249d1] = b'I'
        mem[0x7ffff7a249d2] = b'V'
        mem[0x7ffff7a249d3] = b'A'
        mem[0x7ffff7a249d4] = b'T'
        mem[0x7ffff7a249d5] = b'E'
        mem[0x7ffff7a249d6] = b'\x00'
        mem[0x7ffff7a249d7] = b'\x00'
        mem[0x7ffff7a249d8] = b'\x00'
        mem[0x7ffff7df2951] = b'O'
        mem[0x7ffff7df2952] = b'\x08'
        cpu.XMM1 = 0xffffffffffff00ff52505f4342494c47
        cpu.RDI = 0x7ffff7a249c9
        cpu.RIP = 0x7ffff7df294e
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df294e],  b'f')
        self.assertEqual(mem[0x7ffff7df294f],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df2950],  b'\x16')
        self.assertEqual(mem[0x7ffff7df2951],  b'O')
        self.assertEqual(mem[0x7ffff7df2952],  b'\x08')
        self.assertEqual(mem[0x7ffff7a249d3],  b'A')
        self.assertEqual(mem[0x7ffff7a249d4],  b'T')
        self.assertEqual(mem[0x7ffff7a249d5],  b'E')
        self.assertEqual(mem[0x7ffff7a249d6],  b'\x00')
        self.assertEqual(mem[0x7ffff7a249d7],  b'\x00')
        self.assertEqual(mem[0x7ffff7a249d8],  b'\x00')
        self.assertEqual(mem[0x7ffff7a249d1],  b'I')
        self.assertEqual(mem[0x7ffff7a249d2],  b'V')
        self.assertEqual(cpu.XMM1, 5492818941963568420245782219847)
        self.assertEqual(cpu.RDI, 140737347996105)
        self.assertEqual(cpu.RIP, 140737351985491)

    def test_MOVHPD_10(self):
        ''' Instruction MOVHPD_10
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a24000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df294e] = b'f'
        mem[0x7ffff7df294f] = b'\x0f'
        mem[0x7ffff7df2950] = b'\x16'
        mem[0x7ffff7df2951] = b'O'
        mem[0x7ffff7df2952] = b'\x08'
        mem[0x7ffff7a248d6] = b'2'
        mem[0x7ffff7a248d7] = b'.'
        mem[0x7ffff7a248d8] = b'5'
        mem[0x7ffff7a248d9] = b'\x00'
        mem[0x7ffff7a248da] = b'G'
        mem[0x7ffff7a248db] = b'L'
        mem[0x7ffff7a248dc] = b'I'
        mem[0x7ffff7a248dd] = b'B'
        cpu.XMM1 = 0xffffffff00ffffff2e325f4342494c47
        cpu.RDI = 0x7ffff7a248ce
        cpu.RIP = 0x7ffff7df294e
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df294e],  b'f')
        self.assertEqual(mem[0x7ffff7df294f],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df2950],  b'\x16')
        self.assertEqual(mem[0x7ffff7df2951],  b'O')
        self.assertEqual(mem[0x7ffff7df2952],  b'\x08')
        self.assertEqual(mem[0x7ffff7a248d6],  b'2')
        self.assertEqual(mem[0x7ffff7a248d7],  b'.')
        self.assertEqual(mem[0x7ffff7a248d8],  b'5')
        self.assertEqual(mem[0x7ffff7a248d9],  b'\x00')
        self.assertEqual(mem[0x7ffff7a248da],  b'G')
        self.assertEqual(mem[0x7ffff7a248db],  b'L')
        self.assertEqual(mem[0x7ffff7a248dc],  b'I')
        self.assertEqual(mem[0x7ffff7a248dd],  b'B')
        self.assertEqual(cpu.XMM1, 88109632480871197291218000195730623559)
        self.assertEqual(cpu.RDI, 140737347995854)
        self.assertEqual(cpu.RIP, 140737351985491)

    def test_MOVHPD_11(self):
        ''' Instruction MOVHPD_11
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a24000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df2956] = b'V'
        mem[0x7ffff7df2957] = b'\x08'
        mem[0x7ffff7df2953] = b'f'
        mem[0x7ffff7df2954] = b'\x0f'
        mem[0x7ffff7df2955] = b'\x16'
        mem[0x7ffff7a248d6] = b'2'
        mem[0x7ffff7a248d7] = b'.'
        mem[0x7ffff7a248d8] = b'5'
        mem[0x7ffff7a248d9] = b'\x00'
        mem[0x7ffff7a248da] = b'G'
        mem[0x7ffff7a248db] = b'L'
        mem[0x7ffff7a248dc] = b'I'
        mem[0x7ffff7a248dd] = b'B'
        cpu.XMM2 = 0x42494c4700352e322e325f4342494c47
        cpu.RSI = 0x7ffff7a248ce
        cpu.RIP = 0x7ffff7df2953
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df2956],  b'V')
        self.assertEqual(mem[0x7ffff7a248d7],  b'.')
        self.assertEqual(mem[0x7ffff7df2953],  b'f')
        self.assertEqual(mem[0x7ffff7df2954],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df2955],  b'\x16')
        self.assertEqual(mem[0x7ffff7a248d6],  b'2')
        self.assertEqual(mem[0x7ffff7df2957],  b'\x08')
        self.assertEqual(mem[0x7ffff7a248d8],  b'5')
        self.assertEqual(mem[0x7ffff7a248d9],  b'\x00')
        self.assertEqual(mem[0x7ffff7a248da],  b'G')
        self.assertEqual(mem[0x7ffff7a248db],  b'L')
        self.assertEqual(mem[0x7ffff7a248dc],  b'I')
        self.assertEqual(mem[0x7ffff7a248dd],  b'B')
        self.assertEqual(cpu.XMM2, 88109632480871197291218000195730623559)
        self.assertEqual(cpu.RSI, 140737347995854)
        self.assertEqual(cpu.RIP, 140737351985496)

    def test_MOVHPD_12(self):
        ''' Instruction MOVHPD_12
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a24000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df294e] = b'f'
        mem[0x7ffff7df294f] = b'\x0f'
        mem[0x7ffff7df2950] = b'\x16'
        mem[0x7ffff7df2951] = b'O'
        mem[0x7ffff7df2952] = b'\x08'
        mem[0x7ffff7a248d6] = b'2'
        mem[0x7ffff7a248d7] = b'.'
        mem[0x7ffff7a248d8] = b'5'
        mem[0x7ffff7a248d9] = b'\x00'
        mem[0x7ffff7a248da] = b'G'
        mem[0x7ffff7a248db] = b'L'
        mem[0x7ffff7a248dc] = b'I'
        mem[0x7ffff7a248dd] = b'B'
        cpu.XMM1 = 0xffffffff00ffffff2e325f4342494c47
        cpu.RDI = 0x7ffff7a248ce
        cpu.RIP = 0x7ffff7df294e
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df294e],  b'f')
        self.assertEqual(mem[0x7ffff7df294f],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df2950],  b'\x16')
        self.assertEqual(mem[0x7ffff7df2951],  b'O')
        self.assertEqual(mem[0x7ffff7df2952],  b'\x08')
        self.assertEqual(mem[0x7ffff7a248d6],  b'2')
        self.assertEqual(mem[0x7ffff7a248d7],  b'.')
        self.assertEqual(mem[0x7ffff7a248d8],  b'5')
        self.assertEqual(mem[0x7ffff7a248d9],  b'\x00')
        self.assertEqual(mem[0x7ffff7a248da],  b'G')
        self.assertEqual(mem[0x7ffff7a248db],  b'L')
        self.assertEqual(mem[0x7ffff7a248dc],  b'I')
        self.assertEqual(mem[0x7ffff7a248dd],  b'B')
        self.assertEqual(cpu.XMM1, 88109632480871197291218000195730623559)
        self.assertEqual(cpu.RDI, 140737347995854)
        self.assertEqual(cpu.RIP, 140737351985491)

    def test_MOVHPD_13(self):
        ''' Instruction MOVHPD_13
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a21000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df294e] = b'f'
        mem[0x7ffff7df294f] = b'\x0f'
        mem[0x7ffff7df2950] = b'\x16'
        mem[0x7ffff7df2951] = b'O'
        mem[0x7ffff7df2952] = b'\x08'
        mem[0x7ffff7a218da] = b't'
        mem[0x7ffff7a218db] = b'a'
        mem[0x7ffff7a218dc] = b'r'
        mem[0x7ffff7a218dd] = b't'
        mem[0x7ffff7a218de] = b'_'
        mem[0x7ffff7a218df] = b'm'
        mem[0x7ffff7a218e0] = b'a'
        mem[0x7ffff7a218e1] = b'i'
        cpu.XMM1 = 0x735f6362696c5f5f
        cpu.RDI = 0x7ffff7a218d2
        cpu.RIP = 0x7ffff7df294e
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df294e],  b'f')
        self.assertEqual(mem[0x7ffff7df294f],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df2950],  b'\x16')
        self.assertEqual(mem[0x7ffff7df2951],  b'O')
        self.assertEqual(mem[0x7ffff7df2952],  b'\x08')
        self.assertEqual(mem[0x7ffff7a218da],  b't')
        self.assertEqual(mem[0x7ffff7a218db],  b'a')
        self.assertEqual(mem[0x7ffff7a218dc],  b'r')
        self.assertEqual(mem[0x7ffff7a218dd],  b't')
        self.assertEqual(mem[0x7ffff7a218de],  b'_')
        self.assertEqual(mem[0x7ffff7a218df],  b'm')
        self.assertEqual(mem[0x7ffff7a218e0],  b'a')
        self.assertEqual(mem[0x7ffff7a218e1],  b'i')
        self.assertEqual(cpu.XMM1, 140074810698054820722452200425796689759)
        self.assertEqual(cpu.RDI, 140737347983570)
        self.assertEqual(cpu.RIP, 140737351985491)

    def test_MOVHPD_14(self):
        ''' Instruction MOVHPD_14
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a20000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df2953] = b'f'
        mem[0x7ffff7df2954] = b'\x0f'
        mem[0x7ffff7df2955] = b'\x16'
        mem[0x7ffff7df2956] = b'V'
        mem[0x7ffff7df2957] = b'\x08'
        mem[0x7ffff7a20a9b] = b'\x00'
        mem[0x7ffff7a20a9c] = b'a'
        mem[0x7ffff7a20a9d] = b'c'
        mem[0x7ffff7a20a9e] = b'c'
        mem[0x7ffff7a20a9f] = b't'
        mem[0x7ffff7a20aa0] = b'\x00'
        mem[0x7ffff7a20aa1] = b'_'
        mem[0x7ffff7a20aa2] = b'n'
        cpu.XMM2 = 0x36766772615f6c645f
        cpu.RSI = 0x7ffff7a20a93
        cpu.RIP = 0x7ffff7df2953
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df2953],  b'f')
        self.assertEqual(mem[0x7ffff7df2954],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df2955],  b'\x16')
        self.assertEqual(mem[0x7ffff7df2956],  b'V')
        self.assertEqual(mem[0x7ffff7df2957],  b'\x08')
        self.assertEqual(mem[0x7ffff7a20a9b],  b'\x00')
        self.assertEqual(mem[0x7ffff7a20a9c],  b'a')
        self.assertEqual(mem[0x7ffff7a20a9d],  b'c')
        self.assertEqual(mem[0x7ffff7a20a9e],  b'c')
        self.assertEqual(mem[0x7ffff7a20a9f],  b't')
        self.assertEqual(mem[0x7ffff7a20aa0],  b'\x00')
        self.assertEqual(mem[0x7ffff7a20aa1],  b'_')
        self.assertEqual(mem[0x7ffff7a20aa2],  b'n')
        self.assertEqual(cpu.XMM2, 146708356959127564005328096862462043231)
        self.assertEqual(cpu.RSI, 140737347979923)
        self.assertEqual(cpu.RIP, 140737351985496)

    def test_MOVHPD_15(self):
        ''' Instruction MOVHPD_15
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a23000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df2953] = b'f'
        mem[0x7ffff7df2954] = b'\x0f'
        mem[0x7ffff7df2955] = b'\x16'
        mem[0x7ffff7df2956] = b'V'
        mem[0x7ffff7df2957] = b'\x08'
        mem[0x7ffff7a232ee] = b'n'
        mem[0x7ffff7a232ef] = b'a'
        mem[0x7ffff7a232f0] = b'b'
        mem[0x7ffff7a232f1] = b'l'
        mem[0x7ffff7a232f2] = b'e'
        mem[0x7ffff7a232f3] = b'_'
        mem[0x7ffff7a232f4] = b's'
        mem[0x7ffff7a232f5] = b'e'
        cpu.XMM2 = 0x36655f6362696c5f5f
        cpu.RSI = 0x7ffff7a232e6
        cpu.RIP = 0x7ffff7df2953
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df2953],  b'f')
        self.assertEqual(mem[0x7ffff7df2954],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df2955],  b'\x16')
        self.assertEqual(mem[0x7ffff7df2956],  b'V')
        self.assertEqual(mem[0x7ffff7df2957],  b'\x08')
        self.assertEqual(mem[0x7ffff7a232ee],  b'n')
        self.assertEqual(mem[0x7ffff7a232ef],  b'a')
        self.assertEqual(mem[0x7ffff7a232f0],  b'b')
        self.assertEqual(mem[0x7ffff7a232f1],  b'l')
        self.assertEqual(mem[0x7ffff7a232f2],  b'e')
        self.assertEqual(mem[0x7ffff7a232f3],  b'_')
        self.assertEqual(mem[0x7ffff7a232f4],  b's')
        self.assertEqual(mem[0x7ffff7a232f5],  b'e')
        self.assertEqual(cpu.XMM2, 134851076577508085086976746042965122911)
        self.assertEqual(cpu.RSI, 140737347990246)
        self.assertEqual(cpu.RIP, 140737351985496)

    def test_MOVHPD_16(self):
        ''' Instruction MOVHPD_16
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a24000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df2956] = b'V'
        mem[0x7ffff7df2957] = b'\x08'
        mem[0x7ffff7df2953] = b'f'
        mem[0x7ffff7df2954] = b'\x0f'
        mem[0x7ffff7df2955] = b'\x16'
        mem[0x7ffff7a248d6] = b'2'
        mem[0x7ffff7a248d7] = b'.'
        mem[0x7ffff7a248d8] = b'5'
        mem[0x7ffff7a248d9] = b'\x00'
        mem[0x7ffff7a248da] = b'G'
        mem[0x7ffff7a248db] = b'L'
        mem[0x7ffff7a248dc] = b'I'
        mem[0x7ffff7a248dd] = b'B'
        cpu.XMM2 = 0x42494c4700352e322e325f4342494c47
        cpu.RSI = 0x7ffff7a248ce
        cpu.RIP = 0x7ffff7df2953
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df2956],  b'V')
        self.assertEqual(mem[0x7ffff7a248d7],  b'.')
        self.assertEqual(mem[0x7ffff7df2953],  b'f')
        self.assertEqual(mem[0x7ffff7df2954],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df2955],  b'\x16')
        self.assertEqual(mem[0x7ffff7a248d6],  b'2')
        self.assertEqual(mem[0x7ffff7df2957],  b'\x08')
        self.assertEqual(mem[0x7ffff7a248d8],  b'5')
        self.assertEqual(mem[0x7ffff7a248d9],  b'\x00')
        self.assertEqual(mem[0x7ffff7a248da],  b'G')
        self.assertEqual(mem[0x7ffff7a248db],  b'L')
        self.assertEqual(mem[0x7ffff7a248dc],  b'I')
        self.assertEqual(mem[0x7ffff7a248dd],  b'B')
        self.assertEqual(cpu.XMM2, 88109632480871197291218000195730623559)
        self.assertEqual(cpu.RSI, 140737347995854)
        self.assertEqual(cpu.RIP, 140737351985496)

    def test_MOVHPD_17(self):
        ''' Instruction MOVHPD_17
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7dd7000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df294e] = b'f'
        mem[0x7ffff7df294f] = b'\x0f'
        mem[0x7ffff7df2950] = b'\x16'
        mem[0x7ffff7df2951] = b'O'
        mem[0x7ffff7df2952] = b'\x08'
        mem[0x7ffff7dd7671] = b'_'
        mem[0x7ffff7dd7672] = b'd'
        mem[0x7ffff7dd7673] = b's'
        mem[0x7ffff7dd7674] = b'o'
        mem[0x7ffff7dd7675] = b'_'
        mem[0x7ffff7dd7676] = b'f'
        mem[0x7ffff7dd7677] = b'o'
        mem[0x7ffff7dd7678] = b'r'
        cpu.XMM1 = 0x646e69665f6c645f
        cpu.RDI = 0x7ffff7dd7669
        cpu.RIP = 0x7ffff7df294e
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df294e],  b'f')
        self.assertEqual(mem[0x7ffff7df294f],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df2950],  b'\x16')
        self.assertEqual(mem[0x7ffff7df2951],  b'O')
        self.assertEqual(mem[0x7ffff7df2952],  b'\x08')
        self.assertEqual(mem[0x7ffff7dd7671],  b'_')
        self.assertEqual(mem[0x7ffff7dd7672],  b'd')
        self.assertEqual(mem[0x7ffff7dd7673],  b's')
        self.assertEqual(mem[0x7ffff7dd7674],  b'o')
        self.assertEqual(mem[0x7ffff7dd7675],  b'_')
        self.assertEqual(mem[0x7ffff7dd7676],  b'f')
        self.assertEqual(mem[0x7ffff7dd7677],  b'o')
        self.assertEqual(mem[0x7ffff7dd7678],  b'r')
        self.assertEqual(cpu.XMM1, 152110412837725123259047000460919333983)
        self.assertEqual(cpu.RDI, 140737351874153)
        self.assertEqual(cpu.RIP, 140737351985491)

    def test_MOVHPD_18(self):
        ''' Instruction MOVHPD_18
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a24000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df2956] = b'V'
        mem[0x7ffff7df2957] = b'\x08'
        mem[0x7ffff7df2953] = b'f'
        mem[0x7ffff7df2954] = b'\x0f'
        mem[0x7ffff7df2955] = b'\x16'
        mem[0x7ffff7a248d6] = b'2'
        mem[0x7ffff7a248d7] = b'.'
        mem[0x7ffff7a248d8] = b'5'
        mem[0x7ffff7a248d9] = b'\x00'
        mem[0x7ffff7a248da] = b'G'
        mem[0x7ffff7a248db] = b'L'
        mem[0x7ffff7a248dc] = b'I'
        mem[0x7ffff7a248dd] = b'B'
        cpu.XMM2 = 0x42494c4700352e322e325f4342494c47
        cpu.RSI = 0x7ffff7a248ce
        cpu.RIP = 0x7ffff7df2953
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df2956],  b'V')
        self.assertEqual(mem[0x7ffff7a248d7],  b'.')
        self.assertEqual(mem[0x7ffff7df2953],  b'f')
        self.assertEqual(mem[0x7ffff7df2954],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df2955],  b'\x16')
        self.assertEqual(mem[0x7ffff7a248d6],  b'2')
        self.assertEqual(mem[0x7ffff7df2957],  b'\x08')
        self.assertEqual(mem[0x7ffff7a248d8],  b'5')
        self.assertEqual(mem[0x7ffff7a248d9],  b'\x00')
        self.assertEqual(mem[0x7ffff7a248da],  b'G')
        self.assertEqual(mem[0x7ffff7a248db],  b'L')
        self.assertEqual(mem[0x7ffff7a248dc],  b'I')
        self.assertEqual(mem[0x7ffff7a248dd],  b'B')
        self.assertEqual(cpu.XMM2, 88109632480871197291218000195730623559)
        self.assertEqual(cpu.RSI, 140737347995854)
        self.assertEqual(cpu.RIP, 140737351985496)

    def test_MOVHPD_19(self):
        ''' Instruction MOVHPD_19
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7dd7000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df294e] = b'f'
        mem[0x7ffff7df294f] = b'\x0f'
        mem[0x7ffff7dd7750] = b'o'
        mem[0x7ffff7dd7751] = b'b'
        mem[0x7ffff7dd7752] = b'a'
        mem[0x7ffff7dd7753] = b'l'
        mem[0x7ffff7dd7754] = b'_'
        mem[0x7ffff7dd7755] = b'r'
        mem[0x7ffff7dd7756] = b'o'
        mem[0x7ffff7dd7757] = b'\x00'
        mem[0x7ffff7df2950] = b'\x16'
        mem[0x7ffff7df2951] = b'O'
        mem[0x7ffff7df2952] = b'\x08'
        cpu.XMM1 = 0x6c675f646c74725f
        cpu.RDI = 0x7ffff7dd7748
        cpu.RIP = 0x7ffff7df294e
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df294e],  b'f')
        self.assertEqual(mem[0x7ffff7df294f],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df2950],  b'\x16')
        self.assertEqual(mem[0x7ffff7df2951],  b'O')
        self.assertEqual(mem[0x7ffff7df2952],  b'\x08')
        self.assertEqual(mem[0x7ffff7dd7753],  b'l')
        self.assertEqual(mem[0x7ffff7dd7754],  b'_')
        self.assertEqual(mem[0x7ffff7dd7755],  b'r')
        self.assertEqual(mem[0x7ffff7dd7756],  b'o')
        self.assertEqual(mem[0x7ffff7dd7757],  b'\x00')
        self.assertEqual(mem[0x7ffff7dd7750],  b'o')
        self.assertEqual(mem[0x7ffff7dd7751],  b'b')
        self.assertEqual(mem[0x7ffff7dd7752],  b'a')
        self.assertEqual(cpu.XMM1, 578664706209732724830403288697696863)
        self.assertEqual(cpu.RDI, 140737351874376)
        self.assertEqual(cpu.RIP, 140737351985491)

    def test_MOVHPD_2(self):
        ''' Instruction MOVHPD_2
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a24000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df294e] = b'f'
        mem[0x7ffff7df294f] = b'\x0f'
        mem[0x7ffff7df2950] = b'\x16'
        mem[0x7ffff7df2951] = b'O'
        mem[0x7ffff7df2952] = b'\x08'
        mem[0x7ffff7a248d6] = b'2'
        mem[0x7ffff7a248d7] = b'.'
        mem[0x7ffff7a248d8] = b'5'
        mem[0x7ffff7a248d9] = b'\x00'
        mem[0x7ffff7a248da] = b'G'
        mem[0x7ffff7a248db] = b'L'
        mem[0x7ffff7a248dc] = b'I'
        mem[0x7ffff7a248dd] = b'B'
        cpu.XMM1 = 0xffffffff00ffffff2e325f4342494c47
        cpu.RDI = 0x7ffff7a248ce
        cpu.RIP = 0x7ffff7df294e
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df294e],  b'f')
        self.assertEqual(mem[0x7ffff7df294f],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df2950],  b'\x16')
        self.assertEqual(mem[0x7ffff7df2951],  b'O')
        self.assertEqual(mem[0x7ffff7df2952],  b'\x08')
        self.assertEqual(mem[0x7ffff7a248d6],  b'2')
        self.assertEqual(mem[0x7ffff7a248d7],  b'.')
        self.assertEqual(mem[0x7ffff7a248d8],  b'5')
        self.assertEqual(mem[0x7ffff7a248d9],  b'\x00')
        self.assertEqual(mem[0x7ffff7a248da],  b'G')
        self.assertEqual(mem[0x7ffff7a248db],  b'L')
        self.assertEqual(mem[0x7ffff7a248dc],  b'I')
        self.assertEqual(mem[0x7ffff7a248dd],  b'B')
        self.assertEqual(cpu.XMM1, 88109632480871197291218000195730623559)
        self.assertEqual(cpu.RDI, 140737347995854)
        self.assertEqual(cpu.RIP, 140737351985491)

    def test_MOVHPD_20(self):
        ''' Instruction MOVHPD_20
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a24000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df294e] = b'f'
        mem[0x7ffff7df294f] = b'\x0f'
        mem[0x7ffff7df2950] = b'\x16'
        mem[0x7ffff7df2951] = b'O'
        mem[0x7ffff7df2952] = b'\x08'
        mem[0x7ffff7a248b7] = b'-'
        mem[0x7ffff7a248b8] = b'x'
        mem[0x7ffff7a248b9] = b'8'
        mem[0x7ffff7a248ba] = b'6'
        mem[0x7ffff7a248bb] = b'-'
        mem[0x7ffff7a248bc] = b'6'
        mem[0x7ffff7a248bd] = b'4'
        mem[0x7ffff7a248be] = b'.'
        cpu.XMM1 = 0x78756e696c2d646c
        cpu.RDI = 0x7ffff7a248af
        cpu.RIP = 0x7ffff7df294e
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df294e],  b'f')
        self.assertEqual(mem[0x7ffff7df294f],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df2950],  b'\x16')
        self.assertEqual(mem[0x7ffff7df2951],  b'O')
        self.assertEqual(mem[0x7ffff7df2952],  b'\x08')
        self.assertEqual(mem[0x7ffff7a248b7],  b'-')
        self.assertEqual(mem[0x7ffff7a248b8],  b'x')
        self.assertEqual(mem[0x7ffff7a248b9],  b'8')
        self.assertEqual(mem[0x7ffff7a248ba],  b'6')
        self.assertEqual(mem[0x7ffff7a248bb],  b'-')
        self.assertEqual(mem[0x7ffff7a248bc],  b'6')
        self.assertEqual(mem[0x7ffff7a248bd],  b'4')
        self.assertEqual(mem[0x7ffff7a248be],  b'.')
        self.assertEqual(cpu.XMM1, 61415586074916309421369241318231729260)
        self.assertEqual(cpu.RDI, 140737347995823)
        self.assertEqual(cpu.RIP, 140737351985491)

    def test_MOVHPD_21(self):
        ''' Instruction MOVHPD_21
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7b99000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df2953] = b'f'
        mem[0x7ffff7df2954] = b'\x0f'
        mem[0x7ffff7df2955] = b'\x16'
        mem[0x7ffff7df2956] = b'V'
        mem[0x7ffff7df2957] = b'\x08'
        mem[0x7ffff7b99a30] = b'6'
        mem[0x7ffff7b99a31] = b'\x00'
        mem[0x7ffff7b99a32] = b'_'
        mem[0x7ffff7b99a33] = b'_'
        mem[0x7ffff7b99a34] = b'v'
        mem[0x7ffff7b99a35] = b'd'
        mem[0x7ffff7b99a36] = b's'
        mem[0x7ffff7b99a37] = b'o'
        cpu.XMM2 = 0x64765f5f00656d692e325f58554e494c
        cpu.RSI = 0x7ffff7b99a28
        cpu.RIP = 0x7ffff7df2953
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df2953],  b'f')
        self.assertEqual(mem[0x7ffff7df2954],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df2955],  b'\x16')
        self.assertEqual(mem[0x7ffff7df2956],  b'V')
        self.assertEqual(mem[0x7ffff7df2957],  b'\x08')
        self.assertEqual(mem[0x7ffff7b99a30],  b'6')
        self.assertEqual(mem[0x7ffff7b99a31],  b'\x00')
        self.assertEqual(mem[0x7ffff7b99a32],  b'_')
        self.assertEqual(mem[0x7ffff7b99a33],  b'_')
        self.assertEqual(mem[0x7ffff7b99a34],  b'v')
        self.assertEqual(mem[0x7ffff7b99a35],  b'd')
        self.assertEqual(mem[0x7ffff7b99a36],  b's')
        self.assertEqual(mem[0x7ffff7b99a37],  b'o')
        self.assertEqual(cpu.XMM2, 148143459290256633805182000720633547084)
        self.assertEqual(cpu.RSI, 140737349524008)
        self.assertEqual(cpu.RIP, 140737351985496)

    def test_MOVHPD_3(self):
        ''' Instruction MOVHPD_3
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a24000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df294e] = b'f'
        mem[0x7ffff7df294f] = b'\x0f'
        mem[0x7ffff7df2950] = b'\x16'
        mem[0x7ffff7df2951] = b'O'
        mem[0x7ffff7df2952] = b'\x08'
        mem[0x7ffff7a248d6] = b'2'
        mem[0x7ffff7a248d7] = b'.'
        mem[0x7ffff7a248d8] = b'5'
        mem[0x7ffff7a248d9] = b'\x00'
        mem[0x7ffff7a248da] = b'G'
        mem[0x7ffff7a248db] = b'L'
        mem[0x7ffff7a248dc] = b'I'
        mem[0x7ffff7a248dd] = b'B'
        cpu.XMM1 = 0xffffffff00ffffff2e325f4342494c47
        cpu.RDI = 0x7ffff7a248ce
        cpu.RIP = 0x7ffff7df294e
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df294e],  b'f')
        self.assertEqual(mem[0x7ffff7df294f],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df2950],  b'\x16')
        self.assertEqual(mem[0x7ffff7df2951],  b'O')
        self.assertEqual(mem[0x7ffff7df2952],  b'\x08')
        self.assertEqual(mem[0x7ffff7a248d6],  b'2')
        self.assertEqual(mem[0x7ffff7a248d7],  b'.')
        self.assertEqual(mem[0x7ffff7a248d8],  b'5')
        self.assertEqual(mem[0x7ffff7a248d9],  b'\x00')
        self.assertEqual(mem[0x7ffff7a248da],  b'G')
        self.assertEqual(mem[0x7ffff7a248db],  b'L')
        self.assertEqual(mem[0x7ffff7a248dc],  b'I')
        self.assertEqual(mem[0x7ffff7a248dd],  b'B')
        self.assertEqual(cpu.XMM1, 88109632480871197291218000195730623559)
        self.assertEqual(cpu.RDI, 140737347995854)
        self.assertEqual(cpu.RIP, 140737351985491)

    def test_MOVHPD_4(self):
        ''' Instruction MOVHPD_4
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a24000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df2956] = b'V'
        mem[0x7ffff7df2957] = b'\x08'
        mem[0x7ffff7df2953] = b'f'
        mem[0x7ffff7df2954] = b'\x0f'
        mem[0x7ffff7df2955] = b'\x16'
        mem[0x7ffff7a248d6] = b'2'
        mem[0x7ffff7a248d7] = b'.'
        mem[0x7ffff7a248d8] = b'5'
        mem[0x7ffff7a248d9] = b'\x00'
        mem[0x7ffff7a248da] = b'G'
        mem[0x7ffff7a248db] = b'L'
        mem[0x7ffff7a248dc] = b'I'
        mem[0x7ffff7a248dd] = b'B'
        cpu.XMM2 = 0x42494c4700352e322e325f4342494c47
        cpu.RSI = 0x7ffff7a248ce
        cpu.RIP = 0x7ffff7df2953
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df2956],  b'V')
        self.assertEqual(mem[0x7ffff7a248d7],  b'.')
        self.assertEqual(mem[0x7ffff7df2953],  b'f')
        self.assertEqual(mem[0x7ffff7df2954],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df2955],  b'\x16')
        self.assertEqual(mem[0x7ffff7a248d6],  b'2')
        self.assertEqual(mem[0x7ffff7df2957],  b'\x08')
        self.assertEqual(mem[0x7ffff7a248d8],  b'5')
        self.assertEqual(mem[0x7ffff7a248d9],  b'\x00')
        self.assertEqual(mem[0x7ffff7a248da],  b'G')
        self.assertEqual(mem[0x7ffff7a248db],  b'L')
        self.assertEqual(mem[0x7ffff7a248dc],  b'I')
        self.assertEqual(mem[0x7ffff7a248dd],  b'B')
        self.assertEqual(cpu.XMM2, 88109632480871197291218000195730623559)
        self.assertEqual(cpu.RSI, 140737347995854)
        self.assertEqual(cpu.RIP, 140737351985496)

    def test_MOVHPD_5(self):
        ''' Instruction MOVHPD_5
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7ffa000, 0x1000, 'rwx')
        mem[0x7ffff7ffa30c] = b'6'
        mem[0x7ffff7ffa30d] = b'\x00'
        mem[0x7ffff7ffa30e] = b'\x00'
        mem[0x7ffff7df294f] = b'\x0f'
        mem[0x7ffff7ffa310] = b'\x00'
        mem[0x7ffff7ffa311] = b'\x00'
        mem[0x7ffff7df2952] = b'\x08'
        mem[0x7ffff7ffa313] = b'\x00'
        mem[0x7ffff7df294e] = b'f'
        mem[0x7ffff7ffa30f] = b'\x00'
        mem[0x7ffff7df2950] = b'\x16'
        mem[0x7ffff7df2951] = b'O'
        mem[0x7ffff7ffa312] = b'\x02'
        cpu.XMM1 = 0xffffffff00ffffff2e325f58554e494c
        cpu.RDI = 0x7ffff7ffa304
        cpu.RIP = 0x7ffff7df294e
        cpu.execute()

        self.assertEqual(mem[0x7ffff7ffa30c],  b'6')
        self.assertEqual(mem[0x7ffff7ffa30d],  b'\x00')
        self.assertEqual(mem[0x7ffff7ffa30e],  b'\x00')
        self.assertEqual(mem[0x7ffff7df294f],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df2950],  b'\x16')
        self.assertEqual(mem[0x7ffff7df2951],  b'O')
        self.assertEqual(mem[0x7ffff7df2952],  b'\x08')
        self.assertEqual(mem[0x7ffff7ffa313],  b'\x00')
        self.assertEqual(mem[0x7ffff7df294e],  b'f')
        self.assertEqual(mem[0x7ffff7ffa30f],  b'\x00')
        self.assertEqual(mem[0x7ffff7ffa310],  b'\x00')
        self.assertEqual(mem[0x7ffff7ffa311],  b'\x00')
        self.assertEqual(mem[0x7ffff7ffa312],  b'\x02')
        self.assertEqual(cpu.XMM1, 10384593717070654710068880547400012)
        self.assertEqual(cpu.RDI, 140737354113796)
        self.assertEqual(cpu.RIP, 140737351985491)

    def test_MOVHPD_6(self):
        ''' Instruction MOVHPD_6
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a24000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df2956] = b'V'
        mem[0x7ffff7df2957] = b'\x08'
        mem[0x7ffff7df2953] = b'f'
        mem[0x7ffff7df2954] = b'\x0f'
        mem[0x7ffff7df2955] = b'\x16'
        mem[0x7ffff7a248d6] = b'2'
        mem[0x7ffff7a248d7] = b'.'
        mem[0x7ffff7a248d8] = b'5'
        mem[0x7ffff7a248d9] = b'\x00'
        mem[0x7ffff7a248da] = b'G'
        mem[0x7ffff7a248db] = b'L'
        mem[0x7ffff7a248dc] = b'I'
        mem[0x7ffff7a248dd] = b'B'
        cpu.XMM2 = 0x42494c4700352e322e325f4342494c47
        cpu.RSI = 0x7ffff7a248ce
        cpu.RIP = 0x7ffff7df2953
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df2956],  b'V')
        self.assertEqual(mem[0x7ffff7a248d7],  b'.')
        self.assertEqual(mem[0x7ffff7df2953],  b'f')
        self.assertEqual(mem[0x7ffff7df2954],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df2955],  b'\x16')
        self.assertEqual(mem[0x7ffff7a248d6],  b'2')
        self.assertEqual(mem[0x7ffff7df2957],  b'\x08')
        self.assertEqual(mem[0x7ffff7a248d8],  b'5')
        self.assertEqual(mem[0x7ffff7a248d9],  b'\x00')
        self.assertEqual(mem[0x7ffff7a248da],  b'G')
        self.assertEqual(mem[0x7ffff7a248db],  b'L')
        self.assertEqual(mem[0x7ffff7a248dc],  b'I')
        self.assertEqual(mem[0x7ffff7a248dd],  b'B')
        self.assertEqual(cpu.XMM2, 88109632480871197291218000195730623559)
        self.assertEqual(cpu.RSI, 140737347995854)
        self.assertEqual(cpu.RIP, 140737351985496)

    def test_MOVHPD_7(self):
        ''' Instruction MOVHPD_7
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a24000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df2956] = b'V'
        mem[0x7ffff7df2957] = b'\x08'
        mem[0x7ffff7df2953] = b'f'
        mem[0x7ffff7df2954] = b'\x0f'
        mem[0x7ffff7df2955] = b'\x16'
        mem[0x7ffff7a248d6] = b'2'
        mem[0x7ffff7a248d7] = b'.'
        mem[0x7ffff7a248d8] = b'5'
        mem[0x7ffff7a248d9] = b'\x00'
        mem[0x7ffff7a248da] = b'G'
        mem[0x7ffff7a248db] = b'L'
        mem[0x7ffff7a248dc] = b'I'
        mem[0x7ffff7a248dd] = b'B'
        cpu.XMM2 = 0x42494c4700352e322e325f4342494c47
        cpu.RSI = 0x7ffff7a248ce
        cpu.RIP = 0x7ffff7df2953
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df2956],  b'V')
        self.assertEqual(mem[0x7ffff7a248d7],  b'.')
        self.assertEqual(mem[0x7ffff7df2953],  b'f')
        self.assertEqual(mem[0x7ffff7df2954],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df2955],  b'\x16')
        self.assertEqual(mem[0x7ffff7a248d6],  b'2')
        self.assertEqual(mem[0x7ffff7df2957],  b'\x08')
        self.assertEqual(mem[0x7ffff7a248d8],  b'5')
        self.assertEqual(mem[0x7ffff7a248d9],  b'\x00')
        self.assertEqual(mem[0x7ffff7a248da],  b'G')
        self.assertEqual(mem[0x7ffff7a248db],  b'L')
        self.assertEqual(mem[0x7ffff7a248dc],  b'I')
        self.assertEqual(mem[0x7ffff7a248dd],  b'B')
        self.assertEqual(cpu.XMM2, 88109632480871197291218000195730623559)
        self.assertEqual(cpu.RSI, 140737347995854)
        self.assertEqual(cpu.RIP, 140737351985496)

    def test_MOVHPD_8(self):
        ''' Instruction MOVHPD_8
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7ff7000, 0x1000, 'rwx')
        mem[0x7ffff7df2953] = b'f'
        mem[0x7ffff7df2954] = b'\x0f'
        mem[0x7ffff7df2955] = b'\x16'
        mem[0x7ffff7df2956] = b'V'
        mem[0x7ffff7df2957] = b'\x08'
        mem[0x7ffff7ff74a8] = b'_'
        mem[0x7ffff7ff74a9] = b'6'
        mem[0x7ffff7ff74aa] = b'4'
        mem[0x7ffff7ff74ab] = b'-'
        mem[0x7ffff7ff74ac] = b'l'
        mem[0x7ffff7ff74ad] = b'i'
        mem[0x7ffff7ff74ae] = b'n'
        mem[0x7ffff7ff74af] = b'u'
        cpu.XMM2 = 0x3638782f62696c2f
        cpu.RSI = 0x7ffff7ff74a0
        cpu.RIP = 0x7ffff7df2953
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df2953],  b'f')
        self.assertEqual(mem[0x7ffff7df2954],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df2955],  b'\x16')
        self.assertEqual(mem[0x7ffff7df2956],  b'V')
        self.assertEqual(mem[0x7ffff7df2957],  b'\x08')
        self.assertEqual(mem[0x7ffff7ff74a8],  b'_')
        self.assertEqual(mem[0x7ffff7ff74a9],  b'6')
        self.assertEqual(mem[0x7ffff7ff74aa],  b'4')
        self.assertEqual(mem[0x7ffff7ff74ab],  b'-')
        self.assertEqual(mem[0x7ffff7ff74ac],  b'l')
        self.assertEqual(mem[0x7ffff7ff74ad],  b'i')
        self.assertEqual(mem[0x7ffff7ff74ae],  b'n')
        self.assertEqual(mem[0x7ffff7ff74af],  b'u')
        self.assertEqual(cpu.XMM2, 156092966384913869483545010807748783151)
        self.assertEqual(cpu.RSI, 140737354101920)
        self.assertEqual(cpu.RIP, 140737351985496)

    def test_MOVHPD_9(self):
        ''' Instruction MOVHPD_9
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a21000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df294e] = b'f'
        mem[0x7ffff7df294f] = b'\x0f'
        mem[0x7ffff7df2950] = b'\x16'
        mem[0x7ffff7df2951] = b'O'
        mem[0x7ffff7df2952] = b'\x08'
        mem[0x7ffff7a21315] = b'e'
        mem[0x7ffff7a21316] = b'm'
        mem[0x7ffff7a21317] = b'a'
        mem[0x7ffff7a21318] = b'l'
        mem[0x7ffff7a21319] = b'i'
        mem[0x7ffff7a2131a] = b'g'
        mem[0x7ffff7a2131b] = b'n'
        mem[0x7ffff7a2131c] = b'\x00'
        cpu.XMM1 = 0xffffffff00ffffff6d5f6362696c5f5f
        cpu.RDI = 0x7ffff7a2130d
        cpu.RIP = 0x7ffff7df294e
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df294e],  b'f')
        self.assertEqual(mem[0x7ffff7df294f],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df2950],  b'\x16')
        self.assertEqual(mem[0x7ffff7df2951],  b'O')
        self.assertEqual(mem[0x7ffff7df2952],  b'\x08')
        self.assertEqual(mem[0x7ffff7a21315],  b'e')
        self.assertEqual(mem[0x7ffff7a21316],  b'm')
        self.assertEqual(mem[0x7ffff7a21317],  b'a')
        self.assertEqual(mem[0x7ffff7a21318],  b'l')
        self.assertEqual(mem[0x7ffff7a21319],  b'i')
        self.assertEqual(mem[0x7ffff7a2131a],  b'g')
        self.assertEqual(mem[0x7ffff7a2131b],  b'n')
        self.assertEqual(mem[0x7ffff7a2131c],  b'\x00')
        self.assertEqual(cpu.XMM1, 573250095127234633104266320675626847)
        self.assertEqual(cpu.RDI, 140737347982093)
        self.assertEqual(cpu.RIP, 140737351985491)

    def test_PSLLDQ_1(self):
        ''' Instruction PSLLDQ_1
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3470] = b'f'
        mem[0x7ffff7df3471] = b'\x0f'
        mem[0x7ffff7df3472] = b's'
        mem[0x7ffff7df3473] = b'\xfa'
        mem[0x7ffff7df3474] = b'\x07'
        cpu.XMM2 = 0x1
        cpu.RIP = 0x7ffff7df3470
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df3470],  b'f')
        self.assertEqual(mem[0x7ffff7df3471],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df3472],  b's')
        self.assertEqual(mem[0x7ffff7df3473],  b'\xfa')
        self.assertEqual(mem[0x7ffff7df3474],  b'\x07')
        self.assertEqual(cpu.XMM2, 72057594037927936)
        self.assertEqual(cpu.RIP, 140737351988341)

    def test_PSLLDQ_10(self):
        ''' Instruction PSLLDQ_10
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3470] = b'f'
        mem[0x7ffff7df3471] = b'\x0f'
        mem[0x7ffff7df3472] = b's'
        mem[0x7ffff7df3473] = b'\xfa'
        mem[0x7ffff7df3474] = b'\x07'
        cpu.XMM2 = 0x6972705f5f00362e6f732e6362696c00
        cpu.RIP = 0x7ffff7df3470
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df3470],  b'f')
        self.assertEqual(mem[0x7ffff7df3471],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df3472],  b's')
        self.assertEqual(mem[0x7ffff7df3473],  b'\xfa')
        self.assertEqual(mem[0x7ffff7df3474],  b'\x07')
        self.assertEqual(cpu.XMM2, 61723168909761380161964749838612430848)
        self.assertEqual(cpu.RIP, 140737351988341)

    def test_PSLLDQ_11(self):
        ''' Instruction PSLLDQ_11
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3470] = b'f'
        mem[0x7ffff7df3471] = b'\x0f'
        mem[0x7ffff7df3472] = b's'
        mem[0x7ffff7df3473] = b'\xfa'
        mem[0x7ffff7df3474] = b'\x07'
        cpu.XMM2 = 0x6972705f5f00362e6f732e6362696c00
        cpu.RIP = 0x7ffff7df3470
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df3470],  b'f')
        self.assertEqual(mem[0x7ffff7df3471],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df3472],  b's')
        self.assertEqual(mem[0x7ffff7df3473],  b'\xfa')
        self.assertEqual(mem[0x7ffff7df3474],  b'\x07')
        self.assertEqual(cpu.XMM2, 61723168909761380161964749838612430848)
        self.assertEqual(cpu.RIP, 140737351988341)

    def test_PSLLDQ_12(self):
        ''' Instruction PSLLDQ_12
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3470] = b'f'
        mem[0x7ffff7df3471] = b'\x0f'
        mem[0x7ffff7df3472] = b's'
        mem[0x7ffff7df3473] = b'\xfa'
        mem[0x7ffff7df3474] = b'\x07'
        cpu.XMM2 = 0x6972705f5f00362e6f732e6362696c00
        cpu.RIP = 0x7ffff7df3470
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df3470],  b'f')
        self.assertEqual(mem[0x7ffff7df3471],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df3472],  b's')
        self.assertEqual(mem[0x7ffff7df3473],  b'\xfa')
        self.assertEqual(mem[0x7ffff7df3474],  b'\x07')
        self.assertEqual(cpu.XMM2, 61723168909761380161964749838612430848)
        self.assertEqual(cpu.RIP, 140737351988341)

    def test_PSLLDQ_13(self):
        ''' Instruction PSLLDQ_13
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3470] = b'f'
        mem[0x7ffff7df3471] = b'\x0f'
        mem[0x7ffff7df3472] = b's'
        mem[0x7ffff7df3473] = b'\xfa'
        mem[0x7ffff7df3474] = b'\x07'
        cpu.XMM2 = 0x1
        cpu.RIP = 0x7ffff7df3470
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df3470],  b'f')
        self.assertEqual(mem[0x7ffff7df3471],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df3472],  b's')
        self.assertEqual(mem[0x7ffff7df3473],  b'\xfa')
        self.assertEqual(mem[0x7ffff7df3474],  b'\x07')
        self.assertEqual(cpu.XMM2, 72057594037927936)
        self.assertEqual(cpu.RIP, 140737351988341)

    def test_PSLLDQ_14(self):
        ''' Instruction PSLLDQ_14
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3470] = b'f'
        mem[0x7ffff7df3471] = b'\x0f'
        mem[0x7ffff7df3472] = b's'
        mem[0x7ffff7df3473] = b'\xfa'
        mem[0x7ffff7df3474] = b'\x07'
        cpu.XMM2 = 0x6972705f5f00362e6f732e6362696c00
        cpu.RIP = 0x7ffff7df3470
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df3470],  b'f')
        self.assertEqual(mem[0x7ffff7df3471],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df3472],  b's')
        self.assertEqual(mem[0x7ffff7df3473],  b'\xfa')
        self.assertEqual(mem[0x7ffff7df3474],  b'\x07')
        self.assertEqual(cpu.XMM2, 61723168909761380161964749838612430848)
        self.assertEqual(cpu.RIP, 140737351988341)

    def test_PSLLDQ_15(self):
        ''' Instruction PSLLDQ_15
            Groups: sse2
            0x7ffff7df389d:	pslldq	xmm2, 4
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df38a0] = b'\xfa'
        mem[0x7ffff7df38a1] = b'\x04'
        mem[0x7ffff7df389d] = b'f'
        mem[0x7ffff7df389e] = b'\x0f'
        mem[0x7ffff7df389f] = b's'
        cpu.XMM2 = 0x3000000020002000000352e322e32
        cpu.RIP = 0x7ffff7df389d
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df38a0],  b'\xfa')
        self.assertEqual(mem[0x7ffff7df38a1],  b'\x04')
        self.assertEqual(mem[0x7ffff7df389d],  b'f')
        self.assertEqual(mem[0x7ffff7df389e],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df389f],  b's')
        self.assertEqual(cpu.XMM2, 10384752173395664791945953216036864)
        self.assertEqual(cpu.RIP, 140737351989410)

    def test_PSLLDQ_16(self):
        ''' Instruction PSLLDQ_16
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3470] = b'f'
        mem[0x7ffff7df3471] = b'\x0f'
        mem[0x7ffff7df3472] = b's'
        mem[0x7ffff7df3473] = b'\xfa'
        mem[0x7ffff7df3474] = b'\x07'
        cpu.XMM2 = 0x6972705f5f00362e6f732e6362696c00
        cpu.RIP = 0x7ffff7df3470
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df3470],  b'f')
        self.assertEqual(mem[0x7ffff7df3471],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df3472],  b's')
        self.assertEqual(mem[0x7ffff7df3473],  b'\xfa')
        self.assertEqual(mem[0x7ffff7df3474],  b'\x07')
        self.assertEqual(cpu.XMM2, 61723168909761380161964749838612430848)
        self.assertEqual(cpu.RIP, 140737351988341)

    def test_PSLLDQ_17(self):
        ''' Instruction PSLLDQ_17
            Groups: sse2
            0x7ffff7df39dd:	pslldq	xmm2, 3
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df39e0] = b'\xfa'
        mem[0x7ffff7df39e1] = b'\x03'
        mem[0x7ffff7df39dd] = b'f'
        mem[0x7ffff7df39de] = b'\x0f'
        mem[0x7ffff7df39df] = b's'
        cpu.XMM2 = 0x494c4700352e322e325f4342494c4700
        cpu.RIP = 0x7ffff7df39dd
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df39e0],  b'\xfa')
        self.assertEqual(mem[0x7ffff7df39e1],  b'\x03')
        self.assertEqual(mem[0x7ffff7df39dd],  b'f')
        self.assertEqual(mem[0x7ffff7df39de],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df39df],  b's')
        self.assertEqual(cpu.XMM2, 276128700049446162655260478745346048)
        self.assertEqual(cpu.RIP, 140737351989730)

    def test_PSLLDQ_18(self):
        ''' Instruction PSLLDQ_18
            Groups: sse2
            0x7ffff7df389d:	pslldq	xmm2, 4
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df38a0] = b'\xfa'
        mem[0x7ffff7df38a1] = b'\x04'
        mem[0x7ffff7df389d] = b'f'
        mem[0x7ffff7df389e] = b'\x0f'
        mem[0x7ffff7df389f] = b's'
        cpu.XMM2 = 0x665f4f495f006f6c6c657466006b6863
        cpu.RIP = 0x7ffff7df389d
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df38a0],  b'\xfa')
        self.assertEqual(mem[0x7ffff7df38a1],  b'\x04')
        self.assertEqual(mem[0x7ffff7df389d],  b'f')
        self.assertEqual(mem[0x7ffff7df389e],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df389f],  b's')
        self.assertEqual(cpu.XMM2, 126278919537221597046423674937331941376)
        self.assertEqual(cpu.RIP, 140737351989410)

    def test_PSLLDQ_19(self):
        ''' Instruction PSLLDQ_19
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3470] = b'f'
        mem[0x7ffff7df3471] = b'\x0f'
        mem[0x7ffff7df3472] = b's'
        mem[0x7ffff7df3473] = b'\xfa'
        mem[0x7ffff7df3474] = b'\x07'
        cpu.XMM2 = 0x1
        cpu.RIP = 0x7ffff7df3470
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df3470],  b'f')
        self.assertEqual(mem[0x7ffff7df3471],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df3472],  b's')
        self.assertEqual(mem[0x7ffff7df3473],  b'\xfa')
        self.assertEqual(mem[0x7ffff7df3474],  b'\x07')
        self.assertEqual(cpu.XMM2, 72057594037927936)
        self.assertEqual(cpu.RIP, 140737351988341)

    def test_PSLLDQ_2(self):
        ''' Instruction PSLLDQ_2
            Groups: sse2
            0x7ffff7df2f70:	pslldq	xmm2, 0xb
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df2f70] = b'f'
        mem[0x7ffff7df2f71] = b'\x0f'
        mem[0x7ffff7df2f72] = b's'
        mem[0x7ffff7df2f73] = b'\xfa'
        mem[0x7ffff7df2f74] = b'\x0b'
        cpu.XMM2 = 0x6972705f5f00362e6f732e6362696c00
        cpu.RIP = 0x7ffff7df2f70
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df2f70],  b'f')
        self.assertEqual(mem[0x7ffff7df2f71],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df2f72],  b's')
        self.assertEqual(mem[0x7ffff7df2f73],  b'\xfa')
        self.assertEqual(mem[0x7ffff7df2f74],  b'\x0b')
        self.assertEqual(cpu.XMM2, 132104554884493019491015862172149350400)
        self.assertEqual(cpu.RIP, 140737351987061)

    def test_PSLLDQ_20(self):
        ''' Instruction PSLLDQ_20
            Groups: sse2
            0x7ffff7df3970:	pslldq	xmm2, 3
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3970] = b'f'
        mem[0x7ffff7df3971] = b'\x0f'
        mem[0x7ffff7df3972] = b's'
        mem[0x7ffff7df3973] = b'\xfa'
        mem[0x7ffff7df3974] = b'\x03'
        cpu.XMM2 = 0x322e6f732e34362d3638782d78756e69
        cpu.RIP = 0x7ffff7df3970
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df3970],  b'f')
        self.assertEqual(mem[0x7ffff7df3971],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df3972],  b's')
        self.assertEqual(mem[0x7ffff7df3973],  b'\xfa')
        self.assertEqual(mem[0x7ffff7df3974],  b'\x03')
        self.assertEqual(cpu.XMM2, 153101124148370467217615035531131879424)
        self.assertEqual(cpu.RIP, 140737351989621)

    def test_PSLLDQ_21(self):
        ''' Instruction PSLLDQ_21
            Groups: sse2
            0x7ffff7df3830:	pslldq	xmm2, 4
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3830] = b'f'
        mem[0x7ffff7df3831] = b'\x0f'
        mem[0x7ffff7df3832] = b's'
        mem[0x7ffff7df3833] = b'\xfa'
        mem[0x7ffff7df3834] = b'\x04'
        cpu.XMM2 = 0x5f4342494c4700342e332e325f434249
        cpu.RIP = 0x7ffff7df3830
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df3830],  b'f')
        self.assertEqual(mem[0x7ffff7df3831],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df3832],  b's')
        self.assertEqual(mem[0x7ffff7df3833],  b'\xfa')
        self.assertEqual(mem[0x7ffff7df3834],  b'\x04')
        self.assertEqual(cpu.XMM2, 101389984890772213670702594761716400128)
        self.assertEqual(cpu.RIP, 140737351989301)

    def test_PSLLDQ_3(self):
        ''' Instruction PSLLDQ_3
            Groups: sse2
            0x7ffff7df3ab0:	pslldq	xmm2, 2
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3ab0] = b'f'
        mem[0x7ffff7df3ab1] = b'\x0f'
        mem[0x7ffff7df3ab2] = b's'
        mem[0x7ffff7df3ab3] = b'\xfa'
        mem[0x7ffff7df3ab4] = b'\x02'
        cpu.XMM2 = 0x63007463656a626f5f726f665f6f7364
        cpu.RIP = 0x7ffff7df3ab0
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df3ab0],  b'f')
        self.assertEqual(mem[0x7ffff7df3ab1],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df3ab2],  b's')
        self.assertEqual(mem[0x7ffff7df3ab3],  b'\xfa')
        self.assertEqual(mem[0x7ffff7df3ab4],  b'\x02')
        self.assertEqual(cpu.XMM2, 154706541852064556987039687627872927744)
        self.assertEqual(cpu.RIP, 140737351989941)

    def test_PSLLDQ_4(self):
        ''' Instruction PSLLDQ_4
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3470] = b'f'
        mem[0x7ffff7df3471] = b'\x0f'
        mem[0x7ffff7df3472] = b's'
        mem[0x7ffff7df3473] = b'\xfa'
        mem[0x7ffff7df3474] = b'\x07'
        cpu.XMM2 = 0x6972705f5f00362e6f732e6362696c00
        cpu.RIP = 0x7ffff7df3470
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df3470],  b'f')
        self.assertEqual(mem[0x7ffff7df3471],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df3472],  b's')
        self.assertEqual(mem[0x7ffff7df3473],  b'\xfa')
        self.assertEqual(mem[0x7ffff7df3474],  b'\x07')
        self.assertEqual(cpu.XMM2, 61723168909761380161964749838612430848)
        self.assertEqual(cpu.RIP, 140737351988341)

    def test_PSLLDQ_5(self):
        ''' Instruction PSLLDQ_5
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3470] = b'f'
        mem[0x7ffff7df3471] = b'\x0f'
        mem[0x7ffff7df3472] = b's'
        mem[0x7ffff7df3473] = b'\xfa'
        mem[0x7ffff7df3474] = b'\x07'
        cpu.XMM2 = 0x6972705f5f00362e6f732e6362696c00
        cpu.RIP = 0x7ffff7df3470
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df3470],  b'f')
        self.assertEqual(mem[0x7ffff7df3471],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df3472],  b's')
        self.assertEqual(mem[0x7ffff7df3473],  b'\xfa')
        self.assertEqual(mem[0x7ffff7df3474],  b'\x07')
        self.assertEqual(cpu.XMM2, 61723168909761380161964749838612430848)
        self.assertEqual(cpu.RIP, 140737351988341)

    def test_PSLLDQ_6(self):
        ''' Instruction PSLLDQ_6
            Groups: sse2
            0x7ffff7df389d:	pslldq	xmm2, 4
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df38a0] = b'\xfa'
        mem[0x7ffff7df38a1] = b'\x04'
        mem[0x7ffff7df389d] = b'f'
        mem[0x7ffff7df389e] = b'\x0f'
        mem[0x7ffff7df389f] = b's'
        cpu.XMM2 = 0x3000000020002000000352e322e32
        cpu.RIP = 0x7ffff7df389d
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df38a0],  b'\xfa')
        self.assertEqual(mem[0x7ffff7df38a1],  b'\x04')
        self.assertEqual(mem[0x7ffff7df389d],  b'f')
        self.assertEqual(mem[0x7ffff7df389e],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df389f],  b's')
        self.assertEqual(cpu.XMM2, 10384752173395664791945953216036864)
        self.assertEqual(cpu.RIP, 140737351989410)

    def test_PSLLDQ_7(self):
        ''' Instruction PSLLDQ_7
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3470] = b'f'
        mem[0x7ffff7df3471] = b'\x0f'
        mem[0x7ffff7df3472] = b's'
        mem[0x7ffff7df3473] = b'\xfa'
        mem[0x7ffff7df3474] = b'\x07'
        cpu.XMM2 = 0x1
        cpu.RIP = 0x7ffff7df3470
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df3470],  b'f')
        self.assertEqual(mem[0x7ffff7df3471],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df3472],  b's')
        self.assertEqual(mem[0x7ffff7df3473],  b'\xfa')
        self.assertEqual(mem[0x7ffff7df3474],  b'\x07')
        self.assertEqual(cpu.XMM2, 72057594037927936)
        self.assertEqual(cpu.RIP, 140737351988341)

    def test_PSLLDQ_8(self):
        ''' Instruction PSLLDQ_8
            Groups: sse2
            0x7ffff7df39dd:	pslldq	xmm2, 3
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df39e0] = b'\xfa'
        mem[0x7ffff7df39e1] = b'\x03'
        mem[0x7ffff7df39dd] = b'f'
        mem[0x7ffff7df39de] = b'\x0f'
        mem[0x7ffff7df39df] = b's'
        cpu.XMM2 = 0x7461636f6c6c6165645f6c645f00636f
        cpu.RIP = 0x7ffff7df39dd
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df39e0],  b'\xfa')
        self.assertEqual(mem[0x7ffff7df39e1],  b'\x03')
        self.assertEqual(mem[0x7ffff7df39dd],  b'f')
        self.assertEqual(mem[0x7ffff7df39de],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df39df],  b's')
        self.assertEqual(cpu.XMM2, 148107273809595710738464457560820809728)
        self.assertEqual(cpu.RIP, 140737351989730)

    def test_PSLLDQ_9(self):
        ''' Instruction PSLLDQ_9
            Groups: sse2
            0x7ffff7df3c5d:	pslldq	xmm2, 1
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3c60] = b'\xfa'
        mem[0x7ffff7df3c61] = b'\x01'
        mem[0x7ffff7df3c5d] = b'f'
        mem[0x7ffff7df3c5e] = b'\x0f'
        mem[0x7ffff7df3c5f] = b's'
        cpu.XMM2 = 0x68252e7568254d00796164666f656d69
        cpu.RIP = 0x7ffff7df3c5d
        cpu.execute()

        self.assertEqual(mem[0x7ffff7df3c60],  b'\xfa')
        self.assertEqual(mem[0x7ffff7df3c61],  b'\x01')
        self.assertEqual(mem[0x7ffff7df3c5d],  b'f')
        self.assertEqual(mem[0x7ffff7df3c5e],  b'\x0f')
        self.assertEqual(mem[0x7ffff7df3c5f],  b's')
        self.assertEqual(cpu.XMM2, 49422662792731052987857949274592340224)
        self.assertEqual(cpu.RIP, 140737351990370)

    def test_MOVHPD_1_symbolic(self):
        ''' Instruction MOVHPD_1
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a24000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df294e] = b'f'
        mem[0x7ffff7df294f] = b'\x0f'
        mem[0x7ffff7df2950] = b'\x16'
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a249d1)
        value = cs.new_bitvec(8)
        cs.add(value == 0x49)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a249d2)
        value = cs.new_bitvec(8)
        cs.add(value == 0x56)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a249d3)
        value = cs.new_bitvec(8)
        cs.add(value == 0x41)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a249d4)
        value = cs.new_bitvec(8)
        cs.add(value == 0x54)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a249d5)
        value = cs.new_bitvec(8)
        cs.add(value == 0x45)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a249d6)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a249d7)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a249d8)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        mem[0x7ffff7df2951] = b'O'
        mem[0x7ffff7df2952] = b'\x08'
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xffffffffffff00ff52505f4342494c47)
        cpu.RDI = cs.new_bitvec(64)
        cs.add(cpu.RDI == 0x7ffff7a249c9)
        cpu.RIP = 0x7ffff7df294e

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df294e, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df294f, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2950, 8)== ord('\x16'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2951, 8)== ord('O'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2952, 8)== ord('\x08'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a249d3, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a249d4, 8)== ord('T'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a249d5, 8)== ord('E'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a249d6, 8)== ord('\x00'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a249d7, 8)== ord('\x00'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a249d8, 8)== ord('\x00'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a249d1, 8)== ord('I'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a249d2, 8)== ord('V'))
        condition = Operators.AND(condition, cpu.XMM1 == 0x455441564952505f4342494c47)
        condition = Operators.AND(condition, cpu.RDI == 0x7ffff7a249c9)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df2953)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_MOVHPD_10_symbolic(self):
        ''' Instruction MOVHPD_10
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a24000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df294e] = b'f'
        mem[0x7ffff7df294f] = b'\x0f'
        mem[0x7ffff7df2950] = b'\x16'
        mem[0x7ffff7df2951] = b'O'
        mem[0x7ffff7df2952] = b'\x08'
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d6)
        value = cs.new_bitvec(8)
        cs.add(value == 0x32)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d7)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2e)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d8)
        value = cs.new_bitvec(8)
        cs.add(value == 0x35)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d9)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248da)
        value = cs.new_bitvec(8)
        cs.add(value == 0x47)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248db)
        value = cs.new_bitvec(8)
        cs.add(value == 0x4c)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248dc)
        value = cs.new_bitvec(8)
        cs.add(value == 0x49)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248dd)
        value = cs.new_bitvec(8)
        cs.add(value == 0x42)
        mem[addr] = value
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xffffffff00ffffff2e325f4342494c47)
        cpu.RDI = cs.new_bitvec(64)
        cs.add(cpu.RDI == 0x7ffff7a248ce)
        cpu.RIP = 0x7ffff7df294e

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df294e, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df294f, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2950, 8)== ord('\x16'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2951, 8)== ord('O'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2952, 8)== ord('\x08'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d6, 8)== ord('2'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d7, 8)== ord('.'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d8, 8)== ord('5'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d9, 8)== ord('\x00'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248da, 8)== ord('G'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248db, 8)== ord('L'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248dc, 8)== ord('I'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248dd, 8)== ord('B'))
        condition = Operators.AND(condition, cpu.XMM1 == 0x42494c4700352e322e325f4342494c47)
        condition = Operators.AND(condition, cpu.RDI == 0x7ffff7a248ce)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df2953)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_MOVHPD_11_symbolic(self):
        ''' Instruction MOVHPD_11
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a24000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df2956] = b'V'
        mem[0x7ffff7df2957] = b'\x08'
        mem[0x7ffff7df2953] = b'f'
        mem[0x7ffff7df2954] = b'\x0f'
        mem[0x7ffff7df2955] = b'\x16'
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d6)
        value = cs.new_bitvec(8)
        cs.add(value == 0x32)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d7)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2e)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d8)
        value = cs.new_bitvec(8)
        cs.add(value == 0x35)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d9)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248da)
        value = cs.new_bitvec(8)
        cs.add(value == 0x47)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248db)
        value = cs.new_bitvec(8)
        cs.add(value == 0x4c)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248dc)
        value = cs.new_bitvec(8)
        cs.add(value == 0x49)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248dd)
        value = cs.new_bitvec(8)
        cs.add(value == 0x42)
        mem[addr] = value
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x42494c4700352e322e325f4342494c47)
        cpu.RSI = cs.new_bitvec(64)
        cs.add(cpu.RSI == 0x7ffff7a248ce)
        cpu.RIP = 0x7ffff7df2953

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2956, 8)== ord('V'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d7, 8)== ord('.'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2953, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2954, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2955, 8)== ord('\x16'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d6, 8)== ord('2'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2957, 8)== ord('\x08'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d8, 8)== ord('5'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d9, 8)== ord('\x00'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248da, 8)== ord('G'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248db, 8)== ord('L'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248dc, 8)== ord('I'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248dd, 8)== ord('B'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x42494c4700352e322e325f4342494c47)
        condition = Operators.AND(condition, cpu.RSI == 0x7ffff7a248ce)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df2958)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_MOVHPD_12_symbolic(self):
        ''' Instruction MOVHPD_12
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a24000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df294e] = b'f'
        mem[0x7ffff7df294f] = b'\x0f'
        mem[0x7ffff7df2950] = b'\x16'
        mem[0x7ffff7df2951] = b'O'
        mem[0x7ffff7df2952] = b'\x08'
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d6)
        value = cs.new_bitvec(8)
        cs.add(value == 0x32)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d7)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2e)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d8)
        value = cs.new_bitvec(8)
        cs.add(value == 0x35)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d9)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248da)
        value = cs.new_bitvec(8)
        cs.add(value == 0x47)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248db)
        value = cs.new_bitvec(8)
        cs.add(value == 0x4c)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248dc)
        value = cs.new_bitvec(8)
        cs.add(value == 0x49)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248dd)
        value = cs.new_bitvec(8)
        cs.add(value == 0x42)
        mem[addr] = value
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xffffffff00ffffff2e325f4342494c47)
        cpu.RDI = cs.new_bitvec(64)
        cs.add(cpu.RDI == 0x7ffff7a248ce)
        cpu.RIP = 0x7ffff7df294e

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df294e, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df294f, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2950, 8)== ord('\x16'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2951, 8)== ord('O'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2952, 8)== ord('\x08'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d6, 8)== ord('2'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d7, 8)== ord('.'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d8, 8)== ord('5'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d9, 8)== ord('\x00'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248da, 8)== ord('G'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248db, 8)== ord('L'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248dc, 8)== ord('I'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248dd, 8)== ord('B'))
        condition = Operators.AND(condition, cpu.XMM1 == 0x42494c4700352e322e325f4342494c47)
        condition = Operators.AND(condition, cpu.RDI == 0x7ffff7a248ce)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df2953)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_MOVHPD_13_symbolic(self):
        ''' Instruction MOVHPD_13
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a21000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df294e] = b'f'
        mem[0x7ffff7df294f] = b'\x0f'
        mem[0x7ffff7df2950] = b'\x16'
        mem[0x7ffff7df2951] = b'O'
        mem[0x7ffff7df2952] = b'\x08'
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a218da)
        value = cs.new_bitvec(8)
        cs.add(value == 0x74)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a218db)
        value = cs.new_bitvec(8)
        cs.add(value == 0x61)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a218dc)
        value = cs.new_bitvec(8)
        cs.add(value == 0x72)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a218dd)
        value = cs.new_bitvec(8)
        cs.add(value == 0x74)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a218de)
        value = cs.new_bitvec(8)
        cs.add(value == 0x5f)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a218df)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6d)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a218e0)
        value = cs.new_bitvec(8)
        cs.add(value == 0x61)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a218e1)
        value = cs.new_bitvec(8)
        cs.add(value == 0x69)
        mem[addr] = value
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x735f6362696c5f5f)
        cpu.RDI = cs.new_bitvec(64)
        cs.add(cpu.RDI == 0x7ffff7a218d2)
        cpu.RIP = 0x7ffff7df294e

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df294e, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df294f, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2950, 8)== ord('\x16'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2951, 8)== ord('O'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2952, 8)== ord('\x08'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a218da, 8)== ord('t'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a218db, 8)== ord('a'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a218dc, 8)== ord('r'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a218dd, 8)== ord('t'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a218de, 8)== ord('_'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a218df, 8)== ord('m'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a218e0, 8)== ord('a'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a218e1, 8)== ord('i'))
        condition = Operators.AND(condition, cpu.XMM1 == 0x69616d5f74726174735f6362696c5f5f)
        condition = Operators.AND(condition, cpu.RDI == 0x7ffff7a218d2)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df2953)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_MOVHPD_14_symbolic(self):
        ''' Instruction MOVHPD_14
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a20000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df2953] = b'f'
        mem[0x7ffff7df2954] = b'\x0f'
        mem[0x7ffff7df2955] = b'\x16'
        mem[0x7ffff7df2956] = b'V'
        mem[0x7ffff7df2957] = b'\x08'
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a20a9b)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a20a9c)
        value = cs.new_bitvec(8)
        cs.add(value == 0x61)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a20a9d)
        value = cs.new_bitvec(8)
        cs.add(value == 0x63)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a20a9e)
        value = cs.new_bitvec(8)
        cs.add(value == 0x63)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a20a9f)
        value = cs.new_bitvec(8)
        cs.add(value == 0x74)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a20aa0)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a20aa1)
        value = cs.new_bitvec(8)
        cs.add(value == 0x5f)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a20aa2)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6e)
        mem[addr] = value
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x36766772615f6c645f)
        cpu.RSI = cs.new_bitvec(64)
        cs.add(cpu.RSI == 0x7ffff7a20a93)
        cpu.RIP = 0x7ffff7df2953

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2953, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2954, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2955, 8)== ord('\x16'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2956, 8)== ord('V'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2957, 8)== ord('\x08'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a20a9b, 8)== ord('\x00'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a20a9c, 8)== ord('a'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a20a9d, 8)== ord('c'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a20a9e, 8)== ord('c'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a20a9f, 8)== ord('t'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a20aa0, 8)== ord('\x00'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a20aa1, 8)== ord('_'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a20aa2, 8)== ord('n'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x6e5f007463636100766772615f6c645f)
        condition = Operators.AND(condition, cpu.RSI == 0x7ffff7a20a93)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df2958)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_MOVHPD_15_symbolic(self):
        ''' Instruction MOVHPD_15
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a23000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df2953] = b'f'
        mem[0x7ffff7df2954] = b'\x0f'
        mem[0x7ffff7df2955] = b'\x16'
        mem[0x7ffff7df2956] = b'V'
        mem[0x7ffff7df2957] = b'\x08'
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a232ee)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6e)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a232ef)
        value = cs.new_bitvec(8)
        cs.add(value == 0x61)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a232f0)
        value = cs.new_bitvec(8)
        cs.add(value == 0x62)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a232f1)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6c)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a232f2)
        value = cs.new_bitvec(8)
        cs.add(value == 0x65)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a232f3)
        value = cs.new_bitvec(8)
        cs.add(value == 0x5f)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a232f4)
        value = cs.new_bitvec(8)
        cs.add(value == 0x73)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a232f5)
        value = cs.new_bitvec(8)
        cs.add(value == 0x65)
        mem[addr] = value
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x36655f6362696c5f5f)
        cpu.RSI = cs.new_bitvec(64)
        cs.add(cpu.RSI == 0x7ffff7a232e6)
        cpu.RIP = 0x7ffff7df2953

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2953, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2954, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2955, 8)== ord('\x16'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2956, 8)== ord('V'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2957, 8)== ord('\x08'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a232ee, 8)== ord('n'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a232ef, 8)== ord('a'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a232f0, 8)== ord('b'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a232f1, 8)== ord('l'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a232f2, 8)== ord('e'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a232f3, 8)== ord('_'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a232f4, 8)== ord('s'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a232f5, 8)== ord('e'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x65735f656c62616e655f6362696c5f5f)
        condition = Operators.AND(condition, cpu.RSI == 0x7ffff7a232e6)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df2958)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_MOVHPD_16_symbolic(self):
        ''' Instruction MOVHPD_16
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a24000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df2956] = b'V'
        mem[0x7ffff7df2957] = b'\x08'
        mem[0x7ffff7df2953] = b'f'
        mem[0x7ffff7df2954] = b'\x0f'
        mem[0x7ffff7df2955] = b'\x16'
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d6)
        value = cs.new_bitvec(8)
        cs.add(value == 0x32)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d7)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2e)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d8)
        value = cs.new_bitvec(8)
        cs.add(value == 0x35)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d9)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248da)
        value = cs.new_bitvec(8)
        cs.add(value == 0x47)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248db)
        value = cs.new_bitvec(8)
        cs.add(value == 0x4c)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248dc)
        value = cs.new_bitvec(8)
        cs.add(value == 0x49)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248dd)
        value = cs.new_bitvec(8)
        cs.add(value == 0x42)
        mem[addr] = value
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x42494c4700352e322e325f4342494c47)
        cpu.RSI = cs.new_bitvec(64)
        cs.add(cpu.RSI == 0x7ffff7a248ce)
        cpu.RIP = 0x7ffff7df2953

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2956, 8)== ord('V'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d7, 8)== ord('.'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2953, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2954, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2955, 8)== ord('\x16'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d6, 8)== ord('2'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2957, 8)== ord('\x08'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d8, 8)== ord('5'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d9, 8)== ord('\x00'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248da, 8)== ord('G'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248db, 8)== ord('L'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248dc, 8)== ord('I'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248dd, 8)== ord('B'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x42494c4700352e322e325f4342494c47)
        condition = Operators.AND(condition, cpu.RSI == 0x7ffff7a248ce)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df2958)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_MOVHPD_17_symbolic(self):
        ''' Instruction MOVHPD_17
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7dd7000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df294e] = b'f'
        mem[0x7ffff7df294f] = b'\x0f'
        mem[0x7ffff7df2950] = b'\x16'
        mem[0x7ffff7df2951] = b'O'
        mem[0x7ffff7df2952] = b'\x08'
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7dd7671)
        value = cs.new_bitvec(8)
        cs.add(value == 0x5f)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7dd7672)
        value = cs.new_bitvec(8)
        cs.add(value == 0x64)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7dd7673)
        value = cs.new_bitvec(8)
        cs.add(value == 0x73)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7dd7674)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6f)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7dd7675)
        value = cs.new_bitvec(8)
        cs.add(value == 0x5f)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7dd7676)
        value = cs.new_bitvec(8)
        cs.add(value == 0x66)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7dd7677)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6f)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7dd7678)
        value = cs.new_bitvec(8)
        cs.add(value == 0x72)
        mem[addr] = value
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x646e69665f6c645f)
        cpu.RDI = cs.new_bitvec(64)
        cs.add(cpu.RDI == 0x7ffff7dd7669)
        cpu.RIP = 0x7ffff7df294e

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df294e, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df294f, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2950, 8)== ord('\x16'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2951, 8)== ord('O'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2952, 8)== ord('\x08'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7dd7671, 8)== ord('_'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7dd7672, 8)== ord('d'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7dd7673, 8)== ord('s'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7dd7674, 8)== ord('o'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7dd7675, 8)== ord('_'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7dd7676, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7dd7677, 8)== ord('o'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7dd7678, 8)== ord('r'))
        condition = Operators.AND(condition, cpu.XMM1 == 0x726f665f6f73645f646e69665f6c645f)
        condition = Operators.AND(condition, cpu.RDI == 0x7ffff7dd7669)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df2953)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_MOVHPD_18_symbolic(self):
        ''' Instruction MOVHPD_18
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a24000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df2956] = b'V'
        mem[0x7ffff7df2957] = b'\x08'
        mem[0x7ffff7df2953] = b'f'
        mem[0x7ffff7df2954] = b'\x0f'
        mem[0x7ffff7df2955] = b'\x16'
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d6)
        value = cs.new_bitvec(8)
        cs.add(value == 0x32)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d7)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2e)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d8)
        value = cs.new_bitvec(8)
        cs.add(value == 0x35)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d9)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248da)
        value = cs.new_bitvec(8)
        cs.add(value == 0x47)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248db)
        value = cs.new_bitvec(8)
        cs.add(value == 0x4c)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248dc)
        value = cs.new_bitvec(8)
        cs.add(value == 0x49)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248dd)
        value = cs.new_bitvec(8)
        cs.add(value == 0x42)
        mem[addr] = value
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x42494c4700352e322e325f4342494c47)
        cpu.RSI = cs.new_bitvec(64)
        cs.add(cpu.RSI == 0x7ffff7a248ce)
        cpu.RIP = 0x7ffff7df2953

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2956, 8)== ord('V'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d7, 8)== ord('.'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2953, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2954, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2955, 8)== ord('\x16'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d6, 8)== ord('2'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2957, 8)== ord('\x08'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d8, 8)== ord('5'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d9, 8)== ord('\x00'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248da, 8)== ord('G'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248db, 8)== ord('L'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248dc, 8)== ord('I'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248dd, 8)== ord('B'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x42494c4700352e322e325f4342494c47)
        condition = Operators.AND(condition, cpu.RSI == 0x7ffff7a248ce)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df2958)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_MOVHPD_19_symbolic(self):
        ''' Instruction MOVHPD_19
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7dd7000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df294e] = b'f'
        mem[0x7ffff7df294f] = b'\x0f'
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7dd7750)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6f)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7dd7751)
        value = cs.new_bitvec(8)
        cs.add(value == 0x62)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7dd7752)
        value = cs.new_bitvec(8)
        cs.add(value == 0x61)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7dd7753)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6c)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7dd7754)
        value = cs.new_bitvec(8)
        cs.add(value == 0x5f)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7dd7755)
        value = cs.new_bitvec(8)
        cs.add(value == 0x72)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7dd7756)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6f)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7dd7757)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        mem[0x7ffff7df2950] = b'\x16'
        mem[0x7ffff7df2951] = b'O'
        mem[0x7ffff7df2952] = b'\x08'
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6c675f646c74725f)
        cpu.RDI = cs.new_bitvec(64)
        cs.add(cpu.RDI == 0x7ffff7dd7748)
        cpu.RIP = 0x7ffff7df294e

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df294e, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df294f, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2950, 8)== ord('\x16'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2951, 8)== ord('O'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2952, 8)== ord('\x08'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7dd7753, 8)== ord('l'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7dd7754, 8)== ord('_'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7dd7755, 8)== ord('r'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7dd7756, 8)== ord('o'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7dd7757, 8)== ord('\x00'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7dd7750, 8)== ord('o'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7dd7751, 8)== ord('b'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7dd7752, 8)== ord('a'))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6f725f6c61626f6c675f646c74725f)
        condition = Operators.AND(condition, cpu.RDI == 0x7ffff7dd7748)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df2953)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_MOVHPD_2_symbolic(self):
        ''' Instruction MOVHPD_2
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a24000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df294e] = b'f'
        mem[0x7ffff7df294f] = b'\x0f'
        mem[0x7ffff7df2950] = b'\x16'
        mem[0x7ffff7df2951] = b'O'
        mem[0x7ffff7df2952] = b'\x08'
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d6)
        value = cs.new_bitvec(8)
        cs.add(value == 0x32)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d7)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2e)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d8)
        value = cs.new_bitvec(8)
        cs.add(value == 0x35)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d9)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248da)
        value = cs.new_bitvec(8)
        cs.add(value == 0x47)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248db)
        value = cs.new_bitvec(8)
        cs.add(value == 0x4c)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248dc)
        value = cs.new_bitvec(8)
        cs.add(value == 0x49)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248dd)
        value = cs.new_bitvec(8)
        cs.add(value == 0x42)
        mem[addr] = value
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xffffffff00ffffff2e325f4342494c47)
        cpu.RDI = cs.new_bitvec(64)
        cs.add(cpu.RDI == 0x7ffff7a248ce)
        cpu.RIP = 0x7ffff7df294e

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df294e, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df294f, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2950, 8)== ord('\x16'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2951, 8)== ord('O'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2952, 8)== ord('\x08'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d6, 8)== ord('2'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d7, 8)== ord('.'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d8, 8)== ord('5'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d9, 8)== ord('\x00'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248da, 8)== ord('G'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248db, 8)== ord('L'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248dc, 8)== ord('I'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248dd, 8)== ord('B'))
        condition = Operators.AND(condition, cpu.XMM1 == 0x42494c4700352e322e325f4342494c47)
        condition = Operators.AND(condition, cpu.RDI == 0x7ffff7a248ce)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df2953)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_MOVHPD_20_symbolic(self):
        ''' Instruction MOVHPD_20
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a24000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df294e] = b'f'
        mem[0x7ffff7df294f] = b'\x0f'
        mem[0x7ffff7df2950] = b'\x16'
        mem[0x7ffff7df2951] = b'O'
        mem[0x7ffff7df2952] = b'\x08'
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248b7)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2d)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248b8)
        value = cs.new_bitvec(8)
        cs.add(value == 0x78)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248b9)
        value = cs.new_bitvec(8)
        cs.add(value == 0x38)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248ba)
        value = cs.new_bitvec(8)
        cs.add(value == 0x36)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248bb)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2d)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248bc)
        value = cs.new_bitvec(8)
        cs.add(value == 0x36)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248bd)
        value = cs.new_bitvec(8)
        cs.add(value == 0x34)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248be)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2e)
        mem[addr] = value
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x78756e696c2d646c)
        cpu.RDI = cs.new_bitvec(64)
        cs.add(cpu.RDI == 0x7ffff7a248af)
        cpu.RIP = 0x7ffff7df294e

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df294e, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df294f, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2950, 8)== ord('\x16'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2951, 8)== ord('O'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2952, 8)== ord('\x08'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248b7, 8)== ord('-'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248b8, 8)== ord('x'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248b9, 8)== ord('8'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248ba, 8)== ord('6'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248bb, 8)== ord('-'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248bc, 8)== ord('6'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248bd, 8)== ord('4'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248be, 8)== ord('.'))
        condition = Operators.AND(condition, cpu.XMM1 == 0x2e34362d3638782d78756e696c2d646c)
        condition = Operators.AND(condition, cpu.RDI == 0x7ffff7a248af)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df2953)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_MOVHPD_21_symbolic(self):
        ''' Instruction MOVHPD_21
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7b99000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df2953] = b'f'
        mem[0x7ffff7df2954] = b'\x0f'
        mem[0x7ffff7df2955] = b'\x16'
        mem[0x7ffff7df2956] = b'V'
        mem[0x7ffff7df2957] = b'\x08'
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7b99a30)
        value = cs.new_bitvec(8)
        cs.add(value == 0x36)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7b99a31)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7b99a32)
        value = cs.new_bitvec(8)
        cs.add(value == 0x5f)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7b99a33)
        value = cs.new_bitvec(8)
        cs.add(value == 0x5f)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7b99a34)
        value = cs.new_bitvec(8)
        cs.add(value == 0x76)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7b99a35)
        value = cs.new_bitvec(8)
        cs.add(value == 0x64)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7b99a36)
        value = cs.new_bitvec(8)
        cs.add(value == 0x73)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7b99a37)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6f)
        mem[addr] = value
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x64765f5f00656d692e325f58554e494c)
        cpu.RSI = cs.new_bitvec(64)
        cs.add(cpu.RSI == 0x7ffff7b99a28)
        cpu.RIP = 0x7ffff7df2953

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2953, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2954, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2955, 8)== ord('\x16'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2956, 8)== ord('V'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2957, 8)== ord('\x08'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7b99a30, 8)== ord('6'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7b99a31, 8)== ord('\x00'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7b99a32, 8)== ord('_'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7b99a33, 8)== ord('_'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7b99a34, 8)== ord('v'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7b99a35, 8)== ord('d'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7b99a36, 8)== ord('s'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7b99a37, 8)== ord('o'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x6f7364765f5f00362e325f58554e494c)
        condition = Operators.AND(condition, cpu.RSI == 0x7ffff7b99a28)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df2958)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_MOVHPD_3_symbolic(self):
        ''' Instruction MOVHPD_3
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a24000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df294e] = b'f'
        mem[0x7ffff7df294f] = b'\x0f'
        mem[0x7ffff7df2950] = b'\x16'
        mem[0x7ffff7df2951] = b'O'
        mem[0x7ffff7df2952] = b'\x08'
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d6)
        value = cs.new_bitvec(8)
        cs.add(value == 0x32)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d7)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2e)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d8)
        value = cs.new_bitvec(8)
        cs.add(value == 0x35)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d9)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248da)
        value = cs.new_bitvec(8)
        cs.add(value == 0x47)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248db)
        value = cs.new_bitvec(8)
        cs.add(value == 0x4c)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248dc)
        value = cs.new_bitvec(8)
        cs.add(value == 0x49)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248dd)
        value = cs.new_bitvec(8)
        cs.add(value == 0x42)
        mem[addr] = value
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xffffffff00ffffff2e325f4342494c47)
        cpu.RDI = cs.new_bitvec(64)
        cs.add(cpu.RDI == 0x7ffff7a248ce)
        cpu.RIP = 0x7ffff7df294e

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df294e, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df294f, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2950, 8)== ord('\x16'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2951, 8)== ord('O'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2952, 8)== ord('\x08'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d6, 8)== ord('2'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d7, 8)== ord('.'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d8, 8)== ord('5'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d9, 8)== ord('\x00'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248da, 8)== ord('G'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248db, 8)== ord('L'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248dc, 8)== ord('I'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248dd, 8)== ord('B'))
        condition = Operators.AND(condition, cpu.XMM1 == 0x42494c4700352e322e325f4342494c47)
        condition = Operators.AND(condition, cpu.RDI == 0x7ffff7a248ce)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df2953)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_MOVHPD_4_symbolic(self):
        ''' Instruction MOVHPD_4
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a24000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df2956] = b'V'
        mem[0x7ffff7df2957] = b'\x08'
        mem[0x7ffff7df2953] = b'f'
        mem[0x7ffff7df2954] = b'\x0f'
        mem[0x7ffff7df2955] = b'\x16'
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d6)
        value = cs.new_bitvec(8)
        cs.add(value == 0x32)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d7)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2e)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d8)
        value = cs.new_bitvec(8)
        cs.add(value == 0x35)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d9)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248da)
        value = cs.new_bitvec(8)
        cs.add(value == 0x47)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248db)
        value = cs.new_bitvec(8)
        cs.add(value == 0x4c)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248dc)
        value = cs.new_bitvec(8)
        cs.add(value == 0x49)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248dd)
        value = cs.new_bitvec(8)
        cs.add(value == 0x42)
        mem[addr] = value
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x42494c4700352e322e325f4342494c47)
        cpu.RSI = cs.new_bitvec(64)
        cs.add(cpu.RSI == 0x7ffff7a248ce)
        cpu.RIP = 0x7ffff7df2953

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2956, 8)== ord('V'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d7, 8)== ord('.'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2953, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2954, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2955, 8)== ord('\x16'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d6, 8)== ord('2'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2957, 8)== ord('\x08'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d8, 8)== ord('5'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d9, 8)== ord('\x00'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248da, 8)== ord('G'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248db, 8)== ord('L'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248dc, 8)== ord('I'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248dd, 8)== ord('B'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x42494c4700352e322e325f4342494c47)
        condition = Operators.AND(condition, cpu.RSI == 0x7ffff7a248ce)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df2958)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_MOVHPD_5_symbolic(self):
        ''' Instruction MOVHPD_5
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7ffa000, 0x1000, 'rwx')
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7ffa30c)
        value = cs.new_bitvec(8)
        cs.add(value == 0x36)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7ffa30d)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7ffa30e)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        mem[0x7ffff7df294f] = b'\x0f'
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7ffa310)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7ffa311)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        mem[0x7ffff7df2952] = b'\x08'
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7ffa313)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        mem[0x7ffff7df294e] = b'f'
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7ffa30f)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        mem[0x7ffff7df2950] = b'\x16'
        mem[0x7ffff7df2951] = b'O'
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7ffa312)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2)
        mem[addr] = value
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xffffffff00ffffff2e325f58554e494c)
        cpu.RDI = cs.new_bitvec(64)
        cs.add(cpu.RDI == 0x7ffff7ffa304)
        cpu.RIP = 0x7ffff7df294e

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7ffa30c, 8)== ord('6'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7ffa30d, 8)== ord('\x00'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7ffa30e, 8)== ord('\x00'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df294f, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2950, 8)== ord('\x16'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2951, 8)== ord('O'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2952, 8)== ord('\x08'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7ffa313, 8)== ord('\x00'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df294e, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7ffa30f, 8)== ord('\x00'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7ffa310, 8)== ord('\x00'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7ffa311, 8)== ord('\x00'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7ffa312, 8)== ord('\x02'))
        condition = Operators.AND(condition, cpu.XMM1 == 0x20000000000362e325f58554e494c)
        condition = Operators.AND(condition, cpu.RDI == 0x7ffff7ffa304)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df2953)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_MOVHPD_6_symbolic(self):
        ''' Instruction MOVHPD_6
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a24000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df2956] = b'V'
        mem[0x7ffff7df2957] = b'\x08'
        mem[0x7ffff7df2953] = b'f'
        mem[0x7ffff7df2954] = b'\x0f'
        mem[0x7ffff7df2955] = b'\x16'
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d6)
        value = cs.new_bitvec(8)
        cs.add(value == 0x32)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d7)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2e)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d8)
        value = cs.new_bitvec(8)
        cs.add(value == 0x35)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d9)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248da)
        value = cs.new_bitvec(8)
        cs.add(value == 0x47)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248db)
        value = cs.new_bitvec(8)
        cs.add(value == 0x4c)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248dc)
        value = cs.new_bitvec(8)
        cs.add(value == 0x49)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248dd)
        value = cs.new_bitvec(8)
        cs.add(value == 0x42)
        mem[addr] = value
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x42494c4700352e322e325f4342494c47)
        cpu.RSI = cs.new_bitvec(64)
        cs.add(cpu.RSI == 0x7ffff7a248ce)
        cpu.RIP = 0x7ffff7df2953

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2956, 8)== ord('V'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d7, 8)== ord('.'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2953, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2954, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2955, 8)== ord('\x16'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d6, 8)== ord('2'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2957, 8)== ord('\x08'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d8, 8)== ord('5'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d9, 8)== ord('\x00'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248da, 8)== ord('G'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248db, 8)== ord('L'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248dc, 8)== ord('I'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248dd, 8)== ord('B'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x42494c4700352e322e325f4342494c47)
        condition = Operators.AND(condition, cpu.RSI == 0x7ffff7a248ce)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df2958)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_MOVHPD_7_symbolic(self):
        ''' Instruction MOVHPD_7
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a24000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df2956] = b'V'
        mem[0x7ffff7df2957] = b'\x08'
        mem[0x7ffff7df2953] = b'f'
        mem[0x7ffff7df2954] = b'\x0f'
        mem[0x7ffff7df2955] = b'\x16'
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d6)
        value = cs.new_bitvec(8)
        cs.add(value == 0x32)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d7)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2e)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d8)
        value = cs.new_bitvec(8)
        cs.add(value == 0x35)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248d9)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248da)
        value = cs.new_bitvec(8)
        cs.add(value == 0x47)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248db)
        value = cs.new_bitvec(8)
        cs.add(value == 0x4c)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248dc)
        value = cs.new_bitvec(8)
        cs.add(value == 0x49)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a248dd)
        value = cs.new_bitvec(8)
        cs.add(value == 0x42)
        mem[addr] = value
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x42494c4700352e322e325f4342494c47)
        cpu.RSI = cs.new_bitvec(64)
        cs.add(cpu.RSI == 0x7ffff7a248ce)
        cpu.RIP = 0x7ffff7df2953

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2956, 8)== ord('V'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d7, 8)== ord('.'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2953, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2954, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2955, 8)== ord('\x16'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d6, 8)== ord('2'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2957, 8)== ord('\x08'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d8, 8)== ord('5'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248d9, 8)== ord('\x00'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248da, 8)== ord('G'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248db, 8)== ord('L'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248dc, 8)== ord('I'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a248dd, 8)== ord('B'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x42494c4700352e322e325f4342494c47)
        condition = Operators.AND(condition, cpu.RSI == 0x7ffff7a248ce)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df2958)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_MOVHPD_8_symbolic(self):
        ''' Instruction MOVHPD_8
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7ff7000, 0x1000, 'rwx')
        mem[0x7ffff7df2953] = b'f'
        mem[0x7ffff7df2954] = b'\x0f'
        mem[0x7ffff7df2955] = b'\x16'
        mem[0x7ffff7df2956] = b'V'
        mem[0x7ffff7df2957] = b'\x08'
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7ff74a8)
        value = cs.new_bitvec(8)
        cs.add(value == 0x5f)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7ff74a9)
        value = cs.new_bitvec(8)
        cs.add(value == 0x36)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7ff74aa)
        value = cs.new_bitvec(8)
        cs.add(value == 0x34)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7ff74ab)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2d)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7ff74ac)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6c)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7ff74ad)
        value = cs.new_bitvec(8)
        cs.add(value == 0x69)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7ff74ae)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6e)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7ff74af)
        value = cs.new_bitvec(8)
        cs.add(value == 0x75)
        mem[addr] = value
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x3638782f62696c2f)
        cpu.RSI = cs.new_bitvec(64)
        cs.add(cpu.RSI == 0x7ffff7ff74a0)
        cpu.RIP = 0x7ffff7df2953

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2953, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2954, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2955, 8)== ord('\x16'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2956, 8)== ord('V'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2957, 8)== ord('\x08'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7ff74a8, 8)== ord('_'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7ff74a9, 8)== ord('6'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7ff74aa, 8)== ord('4'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7ff74ab, 8)== ord('-'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7ff74ac, 8)== ord('l'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7ff74ad, 8)== ord('i'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7ff74ae, 8)== ord('n'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7ff74af, 8)== ord('u'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x756e696c2d34365f3638782f62696c2f)
        condition = Operators.AND(condition, cpu.RSI == 0x7ffff7ff74a0)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df2958)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_MOVHPD_9_symbolic(self):
        ''' Instruction MOVHPD_9
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7a21000, 0x1000, 'rwx')
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df294e] = b'f'
        mem[0x7ffff7df294f] = b'\x0f'
        mem[0x7ffff7df2950] = b'\x16'
        mem[0x7ffff7df2951] = b'O'
        mem[0x7ffff7df2952] = b'\x08'
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a21315)
        value = cs.new_bitvec(8)
        cs.add(value == 0x65)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a21316)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6d)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a21317)
        value = cs.new_bitvec(8)
        cs.add(value == 0x61)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a21318)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6c)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a21319)
        value = cs.new_bitvec(8)
        cs.add(value == 0x69)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a2131a)
        value = cs.new_bitvec(8)
        cs.add(value == 0x67)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a2131b)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6e)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7ffff7a2131c)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xffffffff00ffffff6d5f6362696c5f5f)
        cpu.RDI = cs.new_bitvec(64)
        cs.add(cpu.RDI == 0x7ffff7a2130d)
        cpu.RIP = 0x7ffff7df294e

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df294e, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df294f, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2950, 8)== ord('\x16'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2951, 8)== ord('O'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2952, 8)== ord('\x08'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a21315, 8)== ord('e'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a21316, 8)== ord('m'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a21317, 8)== ord('a'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a21318, 8)== ord('l'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a21319, 8)== ord('i'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a2131a, 8)== ord('g'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a2131b, 8)== ord('n'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7a2131c, 8)== ord('\x00'))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6e67696c616d656d5f6362696c5f5f)
        condition = Operators.AND(condition, cpu.RDI == 0x7ffff7a2130d)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df2953)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_PSLLDQ_1_symbolic(self):
        ''' Instruction PSLLDQ_1
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3470] = b'f'
        mem[0x7ffff7df3471] = b'\x0f'
        mem[0x7ffff7df3472] = b's'
        mem[0x7ffff7df3473] = b'\xfa'
        mem[0x7ffff7df3474] = b'\x07'
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x1)
        cpu.RIP = 0x7ffff7df3470

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3470, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3471, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3472, 8)== ord('s'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3473, 8)== ord('\xfa'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3474, 8)== ord('\x07'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x100000000000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df3475)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_PSLLDQ_10_symbolic(self):
        ''' Instruction PSLLDQ_10
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3470] = b'f'
        mem[0x7ffff7df3471] = b'\x0f'
        mem[0x7ffff7df3472] = b's'
        mem[0x7ffff7df3473] = b'\xfa'
        mem[0x7ffff7df3474] = b'\x07'
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x6972705f5f00362e6f732e6362696c00)
        cpu.RIP = 0x7ffff7df3470

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3470, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3471, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3472, 8)== ord('s'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3473, 8)== ord('\xfa'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3474, 8)== ord('\x07'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x2e6f732e6362696c0000000000000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df3475)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_PSLLDQ_11_symbolic(self):
        ''' Instruction PSLLDQ_11
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3470] = b'f'
        mem[0x7ffff7df3471] = b'\x0f'
        mem[0x7ffff7df3472] = b's'
        mem[0x7ffff7df3473] = b'\xfa'
        mem[0x7ffff7df3474] = b'\x07'
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x6972705f5f00362e6f732e6362696c00)
        cpu.RIP = 0x7ffff7df3470

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3470, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3471, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3472, 8)== ord('s'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3473, 8)== ord('\xfa'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3474, 8)== ord('\x07'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x2e6f732e6362696c0000000000000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df3475)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_PSLLDQ_12_symbolic(self):
        ''' Instruction PSLLDQ_12
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3470] = b'f'
        mem[0x7ffff7df3471] = b'\x0f'
        mem[0x7ffff7df3472] = b's'
        mem[0x7ffff7df3473] = b'\xfa'
        mem[0x7ffff7df3474] = b'\x07'
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x6972705f5f00362e6f732e6362696c00)
        cpu.RIP = 0x7ffff7df3470

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3470, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3471, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3472, 8)== ord('s'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3473, 8)== ord('\xfa'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3474, 8)== ord('\x07'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x2e6f732e6362696c0000000000000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df3475)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_PSLLDQ_13_symbolic(self):
        ''' Instruction PSLLDQ_13
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3470] = b'f'
        mem[0x7ffff7df3471] = b'\x0f'
        mem[0x7ffff7df3472] = b's'
        mem[0x7ffff7df3473] = b'\xfa'
        mem[0x7ffff7df3474] = b'\x07'
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x1)
        cpu.RIP = 0x7ffff7df3470

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3470, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3471, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3472, 8)== ord('s'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3473, 8)== ord('\xfa'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3474, 8)== ord('\x07'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x100000000000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df3475)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_PSLLDQ_14_symbolic(self):
        ''' Instruction PSLLDQ_14
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3470] = b'f'
        mem[0x7ffff7df3471] = b'\x0f'
        mem[0x7ffff7df3472] = b's'
        mem[0x7ffff7df3473] = b'\xfa'
        mem[0x7ffff7df3474] = b'\x07'
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x6972705f5f00362e6f732e6362696c00)
        cpu.RIP = 0x7ffff7df3470

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3470, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3471, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3472, 8)== ord('s'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3473, 8)== ord('\xfa'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3474, 8)== ord('\x07'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x2e6f732e6362696c0000000000000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df3475)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_PSLLDQ_15_symbolic(self):
        ''' Instruction PSLLDQ_15
            Groups: sse2
            0x7ffff7df389d:	pslldq	xmm2, 4
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df38a0] = b'\xfa'
        mem[0x7ffff7df38a1] = b'\x04'
        mem[0x7ffff7df389d] = b'f'
        mem[0x7ffff7df389e] = b'\x0f'
        mem[0x7ffff7df389f] = b's'
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x3000000020002000000352e322e32)
        cpu.RIP = 0x7ffff7df389d

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df38a0, 8)== ord('\xfa'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df38a1, 8)== ord('\x04'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df389d, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df389e, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df389f, 8)== ord('s'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x20002000000352e322e3200000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df38a2)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_PSLLDQ_16_symbolic(self):
        ''' Instruction PSLLDQ_16
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3470] = b'f'
        mem[0x7ffff7df3471] = b'\x0f'
        mem[0x7ffff7df3472] = b's'
        mem[0x7ffff7df3473] = b'\xfa'
        mem[0x7ffff7df3474] = b'\x07'
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x6972705f5f00362e6f732e6362696c00)
        cpu.RIP = 0x7ffff7df3470

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3470, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3471, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3472, 8)== ord('s'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3473, 8)== ord('\xfa'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3474, 8)== ord('\x07'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x2e6f732e6362696c0000000000000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df3475)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_PSLLDQ_17_symbolic(self):
        ''' Instruction PSLLDQ_17
            Groups: sse2
            0x7ffff7df39dd:	pslldq	xmm2, 3
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df39e0] = b'\xfa'
        mem[0x7ffff7df39e1] = b'\x03'
        mem[0x7ffff7df39dd] = b'f'
        mem[0x7ffff7df39de] = b'\x0f'
        mem[0x7ffff7df39df] = b's'
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x494c4700352e322e325f4342494c4700)
        cpu.RIP = 0x7ffff7df39dd

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df39e0, 8)== ord('\xfa'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df39e1, 8)== ord('\x03'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df39dd, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df39de, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df39df, 8)== ord('s'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x352e322e325f4342494c4700000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df39e2)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_PSLLDQ_18_symbolic(self):
        ''' Instruction PSLLDQ_18
            Groups: sse2
            0x7ffff7df389d:	pslldq	xmm2, 4
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df38a0] = b'\xfa'
        mem[0x7ffff7df38a1] = b'\x04'
        mem[0x7ffff7df389d] = b'f'
        mem[0x7ffff7df389e] = b'\x0f'
        mem[0x7ffff7df389f] = b's'
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x665f4f495f006f6c6c657466006b6863)
        cpu.RIP = 0x7ffff7df389d

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df38a0, 8)== ord('\xfa'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df38a1, 8)== ord('\x04'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df389d, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df389e, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df389f, 8)== ord('s'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x5f006f6c6c657466006b686300000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df38a2)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_PSLLDQ_19_symbolic(self):
        ''' Instruction PSLLDQ_19
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3470] = b'f'
        mem[0x7ffff7df3471] = b'\x0f'
        mem[0x7ffff7df3472] = b's'
        mem[0x7ffff7df3473] = b'\xfa'
        mem[0x7ffff7df3474] = b'\x07'
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x1)
        cpu.RIP = 0x7ffff7df3470

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3470, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3471, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3472, 8)== ord('s'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3473, 8)== ord('\xfa'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3474, 8)== ord('\x07'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x100000000000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df3475)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_PSLLDQ_2_symbolic(self):
        ''' Instruction PSLLDQ_2
            Groups: sse2
            0x7ffff7df2f70:	pslldq	xmm2, 0xb
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df2000, 0x1000, 'rwx')
        mem[0x7ffff7df2f70] = b'f'
        mem[0x7ffff7df2f71] = b'\x0f'
        mem[0x7ffff7df2f72] = b's'
        mem[0x7ffff7df2f73] = b'\xfa'
        mem[0x7ffff7df2f74] = b'\x0b'
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x6972705f5f00362e6f732e6362696c00)
        cpu.RIP = 0x7ffff7df2f70

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2f70, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2f71, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2f72, 8)== ord('s'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2f73, 8)== ord('\xfa'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df2f74, 8)== ord('\x0b'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x6362696c000000000000000000000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df2f75)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_PSLLDQ_20_symbolic(self):
        ''' Instruction PSLLDQ_20
            Groups: sse2
            0x7ffff7df3970:	pslldq	xmm2, 3
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3970] = b'f'
        mem[0x7ffff7df3971] = b'\x0f'
        mem[0x7ffff7df3972] = b's'
        mem[0x7ffff7df3973] = b'\xfa'
        mem[0x7ffff7df3974] = b'\x03'
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x322e6f732e34362d3638782d78756e69)
        cpu.RIP = 0x7ffff7df3970

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3970, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3971, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3972, 8)== ord('s'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3973, 8)== ord('\xfa'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3974, 8)== ord('\x03'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x732e34362d3638782d78756e69000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df3975)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_PSLLDQ_21_symbolic(self):
        ''' Instruction PSLLDQ_21
            Groups: sse2
            0x7ffff7df3830:	pslldq	xmm2, 4
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3830] = b'f'
        mem[0x7ffff7df3831] = b'\x0f'
        mem[0x7ffff7df3832] = b's'
        mem[0x7ffff7df3833] = b'\xfa'
        mem[0x7ffff7df3834] = b'\x04'
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x5f4342494c4700342e332e325f434249)
        cpu.RIP = 0x7ffff7df3830

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3830, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3831, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3832, 8)== ord('s'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3833, 8)== ord('\xfa'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3834, 8)== ord('\x04'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x4c4700342e332e325f43424900000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df3835)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_PSLLDQ_3_symbolic(self):
        ''' Instruction PSLLDQ_3
            Groups: sse2
            0x7ffff7df3ab0:	pslldq	xmm2, 2
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3ab0] = b'f'
        mem[0x7ffff7df3ab1] = b'\x0f'
        mem[0x7ffff7df3ab2] = b's'
        mem[0x7ffff7df3ab3] = b'\xfa'
        mem[0x7ffff7df3ab4] = b'\x02'
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x63007463656a626f5f726f665f6f7364)
        cpu.RIP = 0x7ffff7df3ab0

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3ab0, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3ab1, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3ab2, 8)== ord('s'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3ab3, 8)== ord('\xfa'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3ab4, 8)== ord('\x02'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x7463656a626f5f726f665f6f73640000)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df3ab5)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_PSLLDQ_4_symbolic(self):
        ''' Instruction PSLLDQ_4
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3470] = b'f'
        mem[0x7ffff7df3471] = b'\x0f'
        mem[0x7ffff7df3472] = b's'
        mem[0x7ffff7df3473] = b'\xfa'
        mem[0x7ffff7df3474] = b'\x07'
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x6972705f5f00362e6f732e6362696c00)
        cpu.RIP = 0x7ffff7df3470

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3470, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3471, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3472, 8)== ord('s'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3473, 8)== ord('\xfa'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3474, 8)== ord('\x07'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x2e6f732e6362696c0000000000000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df3475)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_PSLLDQ_5_symbolic(self):
        ''' Instruction PSLLDQ_5
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3470] = b'f'
        mem[0x7ffff7df3471] = b'\x0f'
        mem[0x7ffff7df3472] = b's'
        mem[0x7ffff7df3473] = b'\xfa'
        mem[0x7ffff7df3474] = b'\x07'
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x6972705f5f00362e6f732e6362696c00)
        cpu.RIP = 0x7ffff7df3470

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3470, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3471, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3472, 8)== ord('s'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3473, 8)== ord('\xfa'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3474, 8)== ord('\x07'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x2e6f732e6362696c0000000000000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df3475)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_PSLLDQ_6_symbolic(self):
        ''' Instruction PSLLDQ_6
            Groups: sse2
            0x7ffff7df389d:	pslldq	xmm2, 4
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df38a0] = b'\xfa'
        mem[0x7ffff7df38a1] = b'\x04'
        mem[0x7ffff7df389d] = b'f'
        mem[0x7ffff7df389e] = b'\x0f'
        mem[0x7ffff7df389f] = b's'
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x3000000020002000000352e322e32)
        cpu.RIP = 0x7ffff7df389d

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df38a0, 8)== ord('\xfa'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df38a1, 8)== ord('\x04'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df389d, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df389e, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df389f, 8)== ord('s'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x20002000000352e322e3200000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df38a2)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_PSLLDQ_7_symbolic(self):
        ''' Instruction PSLLDQ_7
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3470] = b'f'
        mem[0x7ffff7df3471] = b'\x0f'
        mem[0x7ffff7df3472] = b's'
        mem[0x7ffff7df3473] = b'\xfa'
        mem[0x7ffff7df3474] = b'\x07'
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x1)
        cpu.RIP = 0x7ffff7df3470

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3470, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3471, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3472, 8)== ord('s'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3473, 8)== ord('\xfa'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3474, 8)== ord('\x07'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x100000000000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df3475)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_PSLLDQ_8_symbolic(self):
        ''' Instruction PSLLDQ_8
            Groups: sse2
            0x7ffff7df39dd:	pslldq	xmm2, 3
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df39e0] = b'\xfa'
        mem[0x7ffff7df39e1] = b'\x03'
        mem[0x7ffff7df39dd] = b'f'
        mem[0x7ffff7df39de] = b'\x0f'
        mem[0x7ffff7df39df] = b's'
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x7461636f6c6c6165645f6c645f00636f)
        cpu.RIP = 0x7ffff7df39dd

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df39e0, 8)== ord('\xfa'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df39e1, 8)== ord('\x03'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df39dd, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df39de, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df39df, 8)== ord('s'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x6f6c6c6165645f6c645f00636f000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df39e2)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


    def test_PSLLDQ_9_symbolic(self):
        ''' Instruction PSLLDQ_9
            Groups: sse2
            0x7ffff7df3c5d:	pslldq	xmm2, 1
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7ffff7df3000, 0x1000, 'rwx')
        mem[0x7ffff7df3c60] = b'\xfa'
        mem[0x7ffff7df3c61] = b'\x01'
        mem[0x7ffff7df3c5d] = b'f'
        mem[0x7ffff7df3c5e] = b'\x0f'
        mem[0x7ffff7df3c5f] = b's'
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x68252e7568254d00796164666f656d69)
        cpu.RIP = 0x7ffff7df3c5d

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister as e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3c60, 8)== ord('\xfa'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3c61, 8)== ord('\x01'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3c5d, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3c5e, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x7ffff7df3c5f, 8)== ord('s'))
        condition = Operators.AND(condition, cpu.XMM2 == 0x252e7568254d00796164666f656d6900)
        condition = Operators.AND(condition, cpu.RIP == 0x7ffff7df3c62)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


if __name__ == '__main__':
    unittest.main()

