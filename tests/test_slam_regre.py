import unittest
from manticore.core.cpu.x86 import *
from manticore.core.smtlib import Operators
from manticore.core.memory import *


class CPUTest(unittest.TestCase):
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



    def test_PUNPCKHDQ_1(self):
        ''' Instruction PUNPCKHDQ_1 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c43] = 'f'
        mem[0x00419c44] = 'A'
        mem[0x00419c45] = '\x0f'
        mem[0x00419c46] = 'j'
        mem[0x00419c47] = '\xc0'
        cpu.XMM0 = 0x4e0000004c0000004a00000048
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419c43
        cpu.execute()
    
        self.assertEqual(mem[0x419c43], 'f')
        self.assertEqual(mem[0x419c44], 'A')
        self.assertEqual(mem[0x419c45], '\x0f')
        self.assertEqual(mem[0x419c46], 'j')
        self.assertEqual(mem[0x419c47], '\xc0')
        self.assertEqual(cpu.XMM0, 1438846037749345026124L)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848L)

    def test_PUNPCKHDQ_10(self):
        ''' Instruction PUNPCKHDQ_10 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c43] = 'f'
        mem[0x00419c44] = 'A'
        mem[0x00419c45] = '\x0f'
        mem[0x00419c46] = 'j'
        mem[0x00419c47] = '\xc0'
        cpu.XMM0 = 0x36000000340000003200000030
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419c43
        cpu.execute()
    
        self.assertEqual(mem[0x419c43], 'f')
        self.assertEqual(mem[0x419c44], 'A')
        self.assertEqual(mem[0x419c45], '\x0f')
        self.assertEqual(mem[0x419c46], 'j')
        self.assertEqual(mem[0x419c47], '\xc0')
        self.assertEqual(cpu.XMM0, 996124179980315787316L)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848L)

    def test_PUNPCKHDQ_11(self):
        ''' Instruction PUNPCKHDQ_11 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c43] = 'f'
        mem[0x00419c44] = 'A'
        mem[0x00419c45] = '\x0f'
        mem[0x00419c46] = 'j'
        mem[0x00419c47] = '\xc0'
        cpu.XMM0 = 0x3e0000003c0000003a00000038
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419c43
        cpu.execute()
    
        self.assertEqual(mem[0x419c43], 'f')
        self.assertEqual(mem[0x419c44], 'A')
        self.assertEqual(mem[0x419c45], '\x0f')
        self.assertEqual(mem[0x419c46], 'j')
        self.assertEqual(mem[0x419c47], '\xc0')
        self.assertEqual(cpu.XMM0, 1143698132569992200252L)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848L)

    def test_PUNPCKHDQ_12(self):
        ''' Instruction PUNPCKHDQ_12 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c43] = 'f'
        mem[0x00419c44] = 'A'
        mem[0x00419c45] = '\x0f'
        mem[0x00419c46] = 'j'
        mem[0x00419c47] = '\xc0'
        cpu.XMM0 = 0x8e0000008c0000008a00000088
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419c43
        cpu.execute()
    
        self.assertEqual(mem[0x419c43], 'f')
        self.assertEqual(mem[0x419c44], 'A')
        self.assertEqual(mem[0x419c45], '\x0f')
        self.assertEqual(mem[0x419c46], 'j')
        self.assertEqual(mem[0x419c47], '\xc0')
        self.assertEqual(cpu.XMM0, 2619437658466756329612L)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848L)

    def test_PUNPCKHDQ_13(self):
        ''' Instruction PUNPCKHDQ_13 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c43] = 'f'
        mem[0x00419c44] = 'A'
        mem[0x00419c45] = '\x0f'
        mem[0x00419c46] = 'j'
        mem[0x00419c47] = '\xc0'
        cpu.XMM0 = 0xe6000000e4000000e2000000e0
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419c43
        cpu.execute()
    
        self.assertEqual(mem[0x419c43], 'f')
        self.assertEqual(mem[0x419c44], 'A')
        self.assertEqual(mem[0x419c45], '\x0f')
        self.assertEqual(mem[0x419c46], 'j')
        self.assertEqual(mem[0x419c47], '\xc0')
        self.assertEqual(cpu.XMM0, 4242751136953196871908L)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848L)

    def test_PUNPCKHDQ_14(self):
        ''' Instruction PUNPCKHDQ_14 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c43] = 'f'
        mem[0x00419c44] = 'A'
        mem[0x00419c45] = '\x0f'
        mem[0x00419c46] = 'j'
        mem[0x00419c47] = '\xc0'
        cpu.XMM0 = 0x7e0000007c0000007a00000078
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419c43
        cpu.execute()
    
        self.assertEqual(mem[0x419c43], 'f')
        self.assertEqual(mem[0x419c44], 'A')
        self.assertEqual(mem[0x419c45], '\x0f')
        self.assertEqual(mem[0x419c46], 'j')
        self.assertEqual(mem[0x419c47], '\xc0')
        self.assertEqual(cpu.XMM0, 2324289753287403503740L)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848L)

    def test_PUNPCKHDQ_15(self):
        ''' Instruction PUNPCKHDQ_15 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c43] = 'f'
        mem[0x00419c44] = 'A'
        mem[0x00419c45] = '\x0f'
        mem[0x00419c46] = 'j'
        mem[0x00419c47] = '\xc0'
        cpu.XMM0 = 0x96000000940000009200000090
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419c43
        cpu.execute()
    
        self.assertEqual(mem[0x419c43], 'f')
        self.assertEqual(mem[0x419c44], 'A')
        self.assertEqual(mem[0x419c45], '\x0f')
        self.assertEqual(mem[0x419c46], 'j')
        self.assertEqual(mem[0x419c47], '\xc0')
        self.assertEqual(cpu.XMM0, 2767011611056432742548L)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848L)

    def test_PUNPCKHDQ_16(self):
        ''' Instruction PUNPCKHDQ_16 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c43] = 'f'
        mem[0x00419c44] = 'A'
        mem[0x00419c45] = '\x0f'
        mem[0x00419c46] = 'j'
        mem[0x00419c47] = '\xc0'
        cpu.XMM0 = 0x6000000040000000200000000
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419c43
        cpu.execute()
    
        self.assertEqual(mem[0x419c43], 'f')
        self.assertEqual(mem[0x419c44], 'A')
        self.assertEqual(mem[0x419c45], '\x0f')
        self.assertEqual(mem[0x419c46], 'j')
        self.assertEqual(mem[0x419c47], '\xc0')
        self.assertEqual(cpu.XMM0, 110680464442257309700L)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848L)

    def test_PUNPCKHDQ_17(self):
        ''' Instruction PUNPCKHDQ_17 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c43] = 'f'
        mem[0x00419c44] = 'A'
        mem[0x00419c45] = '\x0f'
        mem[0x00419c46] = 'j'
        mem[0x00419c47] = '\xc0'
        cpu.XMM0 = 0xce000000cc000000ca000000c8
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419c43
        cpu.execute()
    
        self.assertEqual(mem[0x419c43], 'f')
        self.assertEqual(mem[0x419c44], 'A')
        self.assertEqual(mem[0x419c45], '\x0f')
        self.assertEqual(mem[0x419c46], 'j')
        self.assertEqual(mem[0x419c47], '\xc0')
        self.assertEqual(cpu.XMM0, 3800029279184167633100L)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848L)

    def test_PUNPCKHDQ_18(self):
        ''' Instruction PUNPCKHDQ_18 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c43] = 'f'
        mem[0x00419c44] = 'A'
        mem[0x00419c45] = '\x0f'
        mem[0x00419c46] = 'j'
        mem[0x00419c47] = '\xc0'
        cpu.XMM0 = 0x9e0000009c0000009a00000098
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419c43
        cpu.execute()
    
        self.assertEqual(mem[0x419c43], 'f')
        self.assertEqual(mem[0x419c44], 'A')
        self.assertEqual(mem[0x419c45], '\x0f')
        self.assertEqual(mem[0x419c46], 'j')
        self.assertEqual(mem[0x419c47], '\xc0')
        self.assertEqual(cpu.XMM0, 2914585563646109155484L)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848L)

    def test_PUNPCKHDQ_19(self):
        ''' Instruction PUNPCKHDQ_19 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c43] = 'f'
        mem[0x00419c44] = 'A'
        mem[0x00419c45] = '\x0f'
        mem[0x00419c46] = 'j'
        mem[0x00419c47] = '\xc0'
        cpu.XMM0 = 0x46000000440000004200000040
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419c43
        cpu.execute()
    
        self.assertEqual(mem[0x419c43], 'f')
        self.assertEqual(mem[0x419c44], 'A')
        self.assertEqual(mem[0x419c45], '\x0f')
        self.assertEqual(mem[0x419c46], 'j')
        self.assertEqual(mem[0x419c47], '\xc0')
        self.assertEqual(cpu.XMM0, 1291272085159668613188L)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848L)

    def test_PUNPCKHDQ_2(self):
        ''' Instruction PUNPCKHDQ_2 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c43] = 'f'
        mem[0x00419c44] = 'A'
        mem[0x00419c45] = '\x0f'
        mem[0x00419c46] = 'j'
        mem[0x00419c47] = '\xc0'
        cpu.XMM0 = 0xbe000000bc000000ba000000b8
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419c43
        cpu.execute()
    
        self.assertEqual(mem[0x419c43], 'f')
        self.assertEqual(mem[0x419c44], 'A')
        self.assertEqual(mem[0x419c45], '\x0f')
        self.assertEqual(mem[0x419c46], 'j')
        self.assertEqual(mem[0x419c47], '\xc0')
        self.assertEqual(cpu.XMM0, 3504881374004814807228L)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848L)

    def test_PUNPCKHDQ_20(self):
        ''' Instruction PUNPCKHDQ_20 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c43] = 'f'
        mem[0x00419c44] = 'A'
        mem[0x00419c45] = '\x0f'
        mem[0x00419c46] = 'j'
        mem[0x00419c47] = '\xc0'
        cpu.XMM0 = 0x66000000640000006200000060
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419c43
        cpu.execute()
    
        self.assertEqual(mem[0x419c43], 'f')
        self.assertEqual(mem[0x419c44], 'A')
        self.assertEqual(mem[0x419c45], '\x0f')
        self.assertEqual(mem[0x419c46], 'j')
        self.assertEqual(mem[0x419c47], '\xc0')
        self.assertEqual(cpu.XMM0, 1881567895518374264932L)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848L)

    def test_PUNPCKHDQ_21(self):
        ''' Instruction PUNPCKHDQ_21 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c43] = 'f'
        mem[0x00419c44] = 'A'
        mem[0x00419c45] = '\x0f'
        mem[0x00419c46] = 'j'
        mem[0x00419c47] = '\xc0'
        cpu.XMM0 = 0x5e0000005c0000005a00000058
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419c43
        cpu.execute()
    
        self.assertEqual(mem[0x419c43], 'f')
        self.assertEqual(mem[0x419c44], 'A')
        self.assertEqual(mem[0x419c45], '\x0f')
        self.assertEqual(mem[0x419c46], 'j')
        self.assertEqual(mem[0x419c47], '\xc0')
        self.assertEqual(cpu.XMM0, 1733993942928697851996L)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848L)

    def test_PUNPCKHDQ_3(self):
        ''' Instruction PUNPCKHDQ_3 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c43] = 'f'
        mem[0x00419c44] = 'A'
        mem[0x00419c45] = '\x0f'
        mem[0x00419c46] = 'j'
        mem[0x00419c47] = '\xc0'
        cpu.XMM0 = 0x6e0000006c0000006a00000068
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419c43
        cpu.execute()
    
        self.assertEqual(mem[0x419c43], 'f')
        self.assertEqual(mem[0x419c44], 'A')
        self.assertEqual(mem[0x419c45], '\x0f')
        self.assertEqual(mem[0x419c46], 'j')
        self.assertEqual(mem[0x419c47], '\xc0')
        self.assertEqual(cpu.XMM0, 2029141848108050677868L)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848L)

    def test_PUNPCKHDQ_4(self):
        ''' Instruction PUNPCKHDQ_4 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c43] = 'f'
        mem[0x00419c44] = 'A'
        mem[0x00419c45] = '\x0f'
        mem[0x00419c46] = 'j'
        mem[0x00419c47] = '\xc0'
        cpu.XMM0 = 0xc6000000c4000000c2000000c0
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419c43
        cpu.execute()
    
        self.assertEqual(mem[0x419c43], 'f')
        self.assertEqual(mem[0x419c44], 'A')
        self.assertEqual(mem[0x419c45], '\x0f')
        self.assertEqual(mem[0x419c46], 'j')
        self.assertEqual(mem[0x419c47], '\xc0')
        self.assertEqual(cpu.XMM0, 3652455326594491220164L)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848L)

    def test_PUNPCKHDQ_5(self):
        ''' Instruction PUNPCKHDQ_5 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c43] = 'f'
        mem[0x00419c44] = 'A'
        mem[0x00419c45] = '\x0f'
        mem[0x00419c46] = 'j'
        mem[0x00419c47] = '\xc0'
        cpu.XMM0 = 0xb6000000b4000000b2000000b0
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419c43
        cpu.execute()
    
        self.assertEqual(mem[0x419c43], 'f')
        self.assertEqual(mem[0x419c44], 'A')
        self.assertEqual(mem[0x419c45], '\x0f')
        self.assertEqual(mem[0x419c46], 'j')
        self.assertEqual(mem[0x419c47], '\xc0')
        self.assertEqual(cpu.XMM0, 3357307421415138394292L)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848L)

    def test_PUNPCKHDQ_6(self):
        ''' Instruction PUNPCKHDQ_6 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c43] = 'f'
        mem[0x00419c44] = 'A'
        mem[0x00419c45] = '\x0f'
        mem[0x00419c46] = 'j'
        mem[0x00419c47] = '\xc0'
        cpu.XMM0 = 0xae000000ac000000aa000000a8
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419c43
        cpu.execute()
    
        self.assertEqual(mem[0x419c43], 'f')
        self.assertEqual(mem[0x419c44], 'A')
        self.assertEqual(mem[0x419c45], '\x0f')
        self.assertEqual(mem[0x419c46], 'j')
        self.assertEqual(mem[0x419c47], '\xc0')
        self.assertEqual(cpu.XMM0, 3209733468825461981356L)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848L)

    def test_PUNPCKHDQ_7(self):
        ''' Instruction PUNPCKHDQ_7 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c43] = 'f'
        mem[0x00419c44] = 'A'
        mem[0x00419c45] = '\x0f'
        mem[0x00419c46] = 'j'
        mem[0x00419c47] = '\xc0'
        cpu.XMM0 = 0xe0000000c0000000a00000008
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419c43
        cpu.execute()
    
        self.assertEqual(mem[0x419c43], 'f')
        self.assertEqual(mem[0x419c44], 'A')
        self.assertEqual(mem[0x419c45], '\x0f')
        self.assertEqual(mem[0x419c46], 'j')
        self.assertEqual(mem[0x419c47], '\xc0')
        self.assertEqual(cpu.XMM0, 258254417031933722636L)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848L)

    def test_PUNPCKHDQ_8(self):
        ''' Instruction PUNPCKHDQ_8 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c43] = 'f'
        mem[0x00419c44] = 'A'
        mem[0x00419c45] = '\x0f'
        mem[0x00419c46] = 'j'
        mem[0x00419c47] = '\xc0'
        cpu.XMM0 = 0x86000000840000008200000080
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419c43
        cpu.execute()
    
        self.assertEqual(mem[0x419c43], 'f')
        self.assertEqual(mem[0x419c44], 'A')
        self.assertEqual(mem[0x419c45], '\x0f')
        self.assertEqual(mem[0x419c46], 'j')
        self.assertEqual(mem[0x419c47], '\xc0')
        self.assertEqual(cpu.XMM0, 2471863705877079916676L)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848L)

    def test_PUNPCKHDQ_9(self):
        ''' Instruction PUNPCKHDQ_9 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c43] = 'f'
        mem[0x00419c44] = 'A'
        mem[0x00419c45] = '\x0f'
        mem[0x00419c46] = 'j'
        mem[0x00419c47] = '\xc0'
        cpu.XMM0 = 0xd6000000d4000000d2000000d0
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419c43
        cpu.execute()
    
        self.assertEqual(mem[0x419c43], 'f')
        self.assertEqual(mem[0x419c44], 'A')
        self.assertEqual(mem[0x419c45], '\x0f')
        self.assertEqual(mem[0x419c46], 'j')
        self.assertEqual(mem[0x419c47], '\xc0')
        self.assertEqual(cpu.XMM0, 3947603231773844046036L)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848L)

    def test_PUNPCKHQDQ_1(self):
        ''' Instruction PUNPCKHQDQ_1 
            Groups: sse2 
            0x419c71:	punpckhqdq	xmm1, xmm1
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c71] = 'f'
        mem[0x00419c72] = '\x0f'
        mem[0x00419c73] = 'm'
        mem[0x00419c74] = '\xc9'
        cpu.XMM1 = 0x6cbae800000000006cbad8
        cpu.RIP = 0x419c71
        cpu.execute()
    
        self.assertEqual(mem[0x419c71], 'f')
        self.assertEqual(mem[0x419c72], '\x0f')
        self.assertEqual(mem[0x419c73], 'm')
        self.assertEqual(mem[0x419c74], '\xc9')
        self.assertEqual(cpu.XMM1, 131446628328818805501115112L)
        self.assertEqual(cpu.RIP, 4299893L)

    def test_PUNPCKHQDQ_10(self):
        ''' Instruction PUNPCKHQDQ_10 
            Groups: sse2 
            0x419c71:	punpckhqdq	xmm1, xmm1
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c71] = 'f'
        mem[0x00419c72] = '\x0f'
        mem[0x00419c73] = 'm'
        mem[0x00419c74] = '\xc9'
        cpu.XMM1 = 0x6cb8e800000000006cb8d8
        cpu.RIP = 0x419c71
        cpu.execute()
    
        self.assertEqual(mem[0x419c71], 'f')
        self.assertEqual(mem[0x419c72], '\x0f')
        self.assertEqual(mem[0x419c73], 'm')
        self.assertEqual(mem[0x419c74], '\xc9')
        self.assertEqual(cpu.XMM1, 131437183595853066210687208L)
        self.assertEqual(cpu.RIP, 4299893L)

    def test_PUNPCKHQDQ_11(self):
        ''' Instruction PUNPCKHQDQ_11 
            Groups: sse2 
            0x419c86:	punpckhqdq	xmm0, xmm0
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c88] = 'm'
        mem[0x00419c89] = '\xc0'
        mem[0x00419c86] = 'f'
        mem[0x00419c87] = '\x0f'
        cpu.XMM0 = 0x6cba8800000000006cba78
        cpu.RIP = 0x419c86
        cpu.execute()
    
        self.assertEqual(mem[0x419c88], 'm')
        self.assertEqual(mem[0x419c89], '\xc0')
        self.assertEqual(mem[0x419c86], 'f')
        self.assertEqual(mem[0x419c87], '\x0f')
        self.assertEqual(cpu.XMM0, 131444857441387729384159880L)
        self.assertEqual(cpu.RIP, 4299914L)

    def test_PUNPCKHQDQ_12(self):
        ''' Instruction PUNPCKHQDQ_12 
            Groups: sse2 
            0x419c71:	punpckhqdq	xmm1, xmm1
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c71] = 'f'
        mem[0x00419c72] = '\x0f'
        mem[0x00419c73] = 'm'
        mem[0x00419c74] = '\xc9'
        cpu.XMM1 = 0x6cbaa800000000006cba98
        cpu.RIP = 0x419c71
        cpu.execute()
    
        self.assertEqual(mem[0x419c71], 'f')
        self.assertEqual(mem[0x419c72], '\x0f')
        self.assertEqual(mem[0x419c73], 'm')
        self.assertEqual(mem[0x419c74], '\xc9')
        self.assertEqual(cpu.XMM1, 131445447737198088089811624L)
        self.assertEqual(cpu.RIP, 4299893L)

    def test_PUNPCKHQDQ_13(self):
        ''' Instruction PUNPCKHQDQ_13 
            Groups: sse2 
            0x419c71:	punpckhqdq	xmm1, xmm1
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c71] = 'f'
        mem[0x00419c72] = '\x0f'
        mem[0x00419c73] = 'm'
        mem[0x00419c74] = '\xc9'
        cpu.XMM1 = 0x6cbee800000000006cbed8
        cpu.RIP = 0x419c71
        cpu.execute()
    
        self.assertEqual(mem[0x419c71], 'f')
        self.assertEqual(mem[0x419c72], '\x0f')
        self.assertEqual(mem[0x419c73], 'm')
        self.assertEqual(mem[0x419c74], '\xc9')
        self.assertEqual(cpu.XMM1, 131465517794750284081970920L)
        self.assertEqual(cpu.RIP, 4299893L)

    def test_PUNPCKHQDQ_14(self):
        ''' Instruction PUNPCKHQDQ_14 
            Groups: sse2 
            0x419c86:	punpckhqdq	xmm0, xmm0
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c88] = 'm'
        mem[0x00419c89] = '\xc0'
        mem[0x00419c86] = 'f'
        mem[0x00419c87] = '\x0f'
        cpu.XMM0 = 0x6cbf4800000000006cbf38
        cpu.RIP = 0x419c86
        cpu.execute()
    
        self.assertEqual(mem[0x419c88], 'm')
        self.assertEqual(mem[0x419c89], '\xc0')
        self.assertEqual(mem[0x419c86], 'f')
        self.assertEqual(mem[0x419c87], '\x0f')
        self.assertEqual(cpu.XMM0, 131467288682181360198926152L)
        self.assertEqual(cpu.RIP, 4299914L)

    def test_PUNPCKHQDQ_15(self):
        ''' Instruction PUNPCKHQDQ_15 
            Groups: sse2 
            0x419c86:	punpckhqdq	xmm0, xmm0
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c88] = 'm'
        mem[0x00419c89] = '\xc0'
        mem[0x00419c86] = 'f'
        mem[0x00419c87] = '\x0f'
        cpu.XMM0 = 0x6cbdc800000000006cbdb8
        cpu.RIP = 0x419c86
        cpu.execute()
    
        self.assertEqual(mem[0x419c88], 'm')
        self.assertEqual(mem[0x419c89], '\xc0')
        self.assertEqual(mem[0x419c86], 'f')
        self.assertEqual(mem[0x419c87], '\x0f')
        self.assertEqual(cpu.XMM0, 131460205132457055731105224L)
        self.assertEqual(cpu.RIP, 4299914L)

    def test_PUNPCKHQDQ_16(self):
        ''' Instruction PUNPCKHQDQ_16 
            Groups: sse2 
            0x419c71:	punpckhqdq	xmm1, xmm1
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c71] = 'f'
        mem[0x00419c72] = '\x0f'
        mem[0x00419c73] = 'm'
        mem[0x00419c74] = '\xc9'
        cpu.XMM1 = 0x6cb96800000000006cb958
        cpu.RIP = 0x419c71
        cpu.execute()
    
        self.assertEqual(mem[0x419c71], 'f')
        self.assertEqual(mem[0x419c72], '\x0f')
        self.assertEqual(mem[0x419c73], 'm')
        self.assertEqual(mem[0x419c74], '\xc9')
        self.assertEqual(cpu.XMM1, 131439544779094501033294184L)
        self.assertEqual(cpu.RIP, 4299893L)

    def test_PUNPCKHQDQ_17(self):
        ''' Instruction PUNPCKHQDQ_17 
            Groups: sse2 
            0x419c86:	punpckhqdq	xmm0, xmm0
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c88] = 'm'
        mem[0x00419c89] = '\xc0'
        mem[0x00419c86] = 'f'
        mem[0x00419c87] = '\x0f'
        cpu.XMM0 = 0x6cbb4800000000006cbb38
        cpu.RIP = 0x419c86
        cpu.execute()
    
        self.assertEqual(mem[0x419c88], 'm')
        self.assertEqual(mem[0x419c89], '\xc0')
        self.assertEqual(mem[0x419c86], 'f')
        self.assertEqual(mem[0x419c87], '\x0f')
        self.assertEqual(cpu.XMM0, 131448399216249881618070344L)
        self.assertEqual(cpu.RIP, 4299914L)

    def test_PUNPCKHQDQ_18(self):
        ''' Instruction PUNPCKHQDQ_18 
            Groups: sse2 
            0x419c86:	punpckhqdq	xmm0, xmm0
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c88] = 'm'
        mem[0x00419c89] = '\xc0'
        mem[0x00419c86] = 'f'
        mem[0x00419c87] = '\x0f'
        cpu.XMM0 = 0x6cb90800000000006cb8f8
        cpu.RIP = 0x419c86
        cpu.execute()
    
        self.assertEqual(mem[0x419c88], 'm')
        self.assertEqual(mem[0x419c89], '\xc0')
        self.assertEqual(mem[0x419c86], 'f')
        self.assertEqual(mem[0x419c87], '\x0f')
        self.assertEqual(cpu.XMM0, 131437773891663424916338952L)
        self.assertEqual(cpu.RIP, 4299914L)

    def test_PUNPCKHQDQ_19(self):
        ''' Instruction PUNPCKHQDQ_19 
            Groups: sse2 
            0x419c71:	punpckhqdq	xmm1, xmm1
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c71] = 'f'
        mem[0x00419c72] = '\x0f'
        mem[0x00419c73] = 'm'
        mem[0x00419c74] = '\xc9'
        cpu.XMM1 = 0x6cbfe800000000006cbfd8
        cpu.RIP = 0x419c71
        cpu.execute()
    
        self.assertEqual(mem[0x419c71], 'f')
        self.assertEqual(mem[0x419c72], '\x0f')
        self.assertEqual(mem[0x419c73], 'm')
        self.assertEqual(mem[0x419c74], '\xc9')
        self.assertEqual(cpu.XMM1, 131470240161233153727184872L)
        self.assertEqual(cpu.RIP, 4299893L)

    def test_PUNPCKHQDQ_2(self):
        ''' Instruction PUNPCKHQDQ_2 
            Groups: sse2 
            0x419c86:	punpckhqdq	xmm0, xmm0
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c88] = 'm'
        mem[0x00419c89] = '\xc0'
        mem[0x00419c86] = 'f'
        mem[0x00419c87] = '\x0f'
        cpu.XMM0 = 0x6cb88800000000006cb878
        cpu.RIP = 0x419c86
        cpu.execute()
    
        self.assertEqual(mem[0x419c88], 'm')
        self.assertEqual(mem[0x419c89], '\xc0')
        self.assertEqual(mem[0x419c86], 'f')
        self.assertEqual(mem[0x419c87], '\x0f')
        self.assertEqual(cpu.XMM0, 131435412708421990093731976L)
        self.assertEqual(cpu.RIP, 4299914L)

    def test_PUNPCKHQDQ_20(self):
        ''' Instruction PUNPCKHQDQ_20 
            Groups: sse2 
            0x419c71:	punpckhqdq	xmm1, xmm1
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c71] = 'f'
        mem[0x00419c72] = '\x0f'
        mem[0x00419c73] = 'm'
        mem[0x00419c74] = '\xc9'
        cpu.XMM1 = 0x6cb92800000000006cb918
        cpu.RIP = 0x419c71
        cpu.execute()
    
        self.assertEqual(mem[0x419c71], 'f')
        self.assertEqual(mem[0x419c72], '\x0f')
        self.assertEqual(mem[0x419c73], 'm')
        self.assertEqual(mem[0x419c74], '\xc9')
        self.assertEqual(cpu.XMM1, 131438364187473783621990696L)
        self.assertEqual(cpu.RIP, 4299893L)

    def test_PUNPCKHQDQ_21(self):
        ''' Instruction PUNPCKHQDQ_21 
            Groups: sse2 
            0x419c86:	punpckhqdq	xmm0, xmm0
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c88] = 'm'
        mem[0x00419c89] = '\xc0'
        mem[0x00419c86] = 'f'
        mem[0x00419c87] = '\x0f'
        cpu.XMM0 = 0x6cbac800000000006cbab8
        cpu.RIP = 0x419c86
        cpu.execute()
    
        self.assertEqual(mem[0x419c88], 'm')
        self.assertEqual(mem[0x419c89], '\xc0')
        self.assertEqual(mem[0x419c86], 'f')
        self.assertEqual(mem[0x419c87], '\x0f')
        self.assertEqual(cpu.XMM0, 131446038033008446795463368L)
        self.assertEqual(cpu.RIP, 4299914L)

    def test_PUNPCKHQDQ_3(self):
        ''' Instruction PUNPCKHQDQ_3 
            Groups: sse2 
            0x419c71:	punpckhqdq	xmm1, xmm1
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c71] = 'f'
        mem[0x00419c72] = '\x0f'
        mem[0x00419c73] = 'm'
        mem[0x00419c74] = '\xc9'
        cpu.XMM1 = 0x6cbbe800000000006cbbd8
        cpu.RIP = 0x419c71
        cpu.execute()
    
        self.assertEqual(mem[0x419c71], 'f')
        self.assertEqual(mem[0x419c72], '\x0f')
        self.assertEqual(mem[0x419c73], 'm')
        self.assertEqual(mem[0x419c74], '\xc9')
        self.assertEqual(cpu.XMM1, 131451350695301675146329064L)
        self.assertEqual(cpu.RIP, 4299893L)

    def test_PUNPCKHQDQ_4(self):
        ''' Instruction PUNPCKHQDQ_4 
            Groups: sse2 
            0x419c86:	punpckhqdq	xmm0, xmm0
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c88] = 'm'
        mem[0x00419c89] = '\xc0'
        mem[0x00419c86] = 'f'
        mem[0x00419c87] = '\x0f'
        cpu.XMM0 = 0x6cbd8800000000006cbd78
        cpu.RIP = 0x419c86
        cpu.execute()
    
        self.assertEqual(mem[0x419c88], 'm')
        self.assertEqual(mem[0x419c89], '\xc0')
        self.assertEqual(mem[0x419c86], 'f')
        self.assertEqual(mem[0x419c87], '\x0f')
        self.assertEqual(cpu.XMM0, 131459024540836338319801736L)
        self.assertEqual(cpu.RIP, 4299914L)

    def test_PUNPCKHQDQ_5(self):
        ''' Instruction PUNPCKHQDQ_5 
            Groups: sse2 
            0x419c71:	punpckhqdq	xmm1, xmm1
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c71] = 'f'
        mem[0x00419c72] = '\x0f'
        mem[0x00419c73] = 'm'
        mem[0x00419c74] = '\xc9'
        cpu.XMM1 = 0x6cb86800000000006cb858
        cpu.RIP = 0x419c71
        cpu.execute()
    
        self.assertEqual(mem[0x419c71], 'f')
        self.assertEqual(mem[0x419c72], '\x0f')
        self.assertEqual(mem[0x419c73], 'm')
        self.assertEqual(mem[0x419c74], '\xc9')
        self.assertEqual(cpu.XMM1, 131434822412611631388080232L)
        self.assertEqual(cpu.RIP, 4299893L)

    def test_PUNPCKHQDQ_6(self):
        ''' Instruction PUNPCKHQDQ_6 
            Groups: sse2 
            0x419c71:	punpckhqdq	xmm1, xmm1
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c71] = 'f'
        mem[0x00419c72] = '\x0f'
        mem[0x00419c73] = 'm'
        mem[0x00419c74] = '\xc9'
        cpu.XMM1 = 0x6cbde800000000006cbdd8
        cpu.RIP = 0x419c71
        cpu.execute()
    
        self.assertEqual(mem[0x419c71], 'f')
        self.assertEqual(mem[0x419c72], '\x0f')
        self.assertEqual(mem[0x419c73], 'm')
        self.assertEqual(mem[0x419c74], '\xc9')
        self.assertEqual(cpu.XMM1, 131460795428267414436756968L)
        self.assertEqual(cpu.RIP, 4299893L)

    def test_PUNPCKHQDQ_7(self):
        ''' Instruction PUNPCKHQDQ_7 
            Groups: sse2 
            0x419c71:	punpckhqdq	xmm1, xmm1
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c71] = 'f'
        mem[0x00419c72] = '\x0f'
        mem[0x00419c73] = 'm'
        mem[0x00419c74] = '\xc9'
        cpu.XMM1 = 0x6cbd2800000000006cbd18
        cpu.RIP = 0x419c71
        cpu.execute()
    
        self.assertEqual(mem[0x419c71], 'f')
        self.assertEqual(mem[0x419c72], '\x0f')
        self.assertEqual(mem[0x419c73], 'm')
        self.assertEqual(mem[0x419c74], '\xc9')
        self.assertEqual(cpu.XMM1, 131457253653405262202846504L)
        self.assertEqual(cpu.RIP, 4299893L)

    def test_PUNPCKHQDQ_8(self):
        ''' Instruction PUNPCKHQDQ_8 
            Groups: sse2 
            0x419c71:	punpckhqdq	xmm1, xmm1
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c71] = 'f'
        mem[0x00419c72] = '\x0f'
        mem[0x00419c73] = 'm'
        mem[0x00419c74] = '\xc9'
        cpu.XMM1 = 0x6cb8a800000000006cb898
        cpu.RIP = 0x419c71
        cpu.execute()
    
        self.assertEqual(mem[0x419c71], 'f')
        self.assertEqual(mem[0x419c72], '\x0f')
        self.assertEqual(mem[0x419c73], 'm')
        self.assertEqual(mem[0x419c74], '\xc9')
        self.assertEqual(cpu.XMM1, 131436003004232348799383720L)
        self.assertEqual(cpu.RIP, 4299893L)

    def test_PUNPCKHQDQ_9(self):
        ''' Instruction PUNPCKHQDQ_9 
            Groups: sse2 
            0x419c86:	punpckhqdq	xmm0, xmm0
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c88] = 'm'
        mem[0x00419c89] = '\xc0'
        mem[0x00419c86] = 'f'
        mem[0x00419c87] = '\x0f'
        cpu.XMM0 = 0x6cb94800000000006cb938
        cpu.RIP = 0x419c86
        cpu.execute()
    
        self.assertEqual(mem[0x419c88], 'm')
        self.assertEqual(mem[0x419c89], '\xc0')
        self.assertEqual(mem[0x419c86], 'f')
        self.assertEqual(mem[0x419c87], '\x0f')
        self.assertEqual(cpu.XMM0, 131438954483284142327642440L)
        self.assertEqual(cpu.RIP, 4299914L)

    def test_PUNPCKLBW_1(self):
        ''' Instruction PUNPCKLBW_1 
            Groups: sse2 
            0x4668ac:	punpcklbw	xmm1, xmm1
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00466000, 0x1000, 'rwx')
        mem[0x004668ac] = 'f'
        mem[0x004668ad] = '\x0f'
        mem[0x004668ae] = '`'
        mem[0x004668af] = '\xc9'
        cpu.XMM1 = 0x2f
        cpu.RIP = 0x4668ac
        cpu.execute()
    
        self.assertEqual(mem[0x4668ac], 'f')
        self.assertEqual(mem[0x4668ad], '\x0f')
        self.assertEqual(mem[0x4668ae], '`')
        self.assertEqual(mem[0x4668af], '\xc9')
        self.assertEqual(cpu.XMM1, 12079)
        self.assertEqual(cpu.RIP, 4614320L)

    def test_PUNPCKLDQ_1(self):
        ''' Instruction PUNPCKLDQ_1 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c48] = 'f'
        mem[0x00419c49] = 'A'
        mem[0x00419c4a] = '\x0f'
        mem[0x00419c4b] = 'b'
        mem[0x00419c4c] = '\xc8'
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0xa6000000a4000000a2000000a0
        cpu.RIP = 0x419c48
        cpu.execute()
    
        self.assertEqual(mem[0x419c48], 'f')
        self.assertEqual(mem[0x419c49], 'A')
        self.assertEqual(mem[0x419c4a], '\x0f')
        self.assertEqual(mem[0x419c4b], 'b')
        self.assertEqual(mem[0x419c4c], '\xc8')
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 2988372539940947361952L)
        self.assertEqual(cpu.RIP, 4299853L)

    def test_PUNPCKLDQ_10(self):
        ''' Instruction PUNPCKLDQ_10 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c48] = 'f'
        mem[0x00419c49] = 'A'
        mem[0x00419c4a] = '\x0f'
        mem[0x00419c4b] = 'b'
        mem[0x00419c4c] = '\xc8'
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0x3e0000003c0000003a00000038
        cpu.RIP = 0x419c48
        cpu.execute()
    
        self.assertEqual(mem[0x419c48], 'f')
        self.assertEqual(mem[0x419c49], 'A')
        self.assertEqual(mem[0x419c4a], '\x0f')
        self.assertEqual(mem[0x419c4b], 'b')
        self.assertEqual(mem[0x419c4c], '\xc8')
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 1069911156275153993784L)
        self.assertEqual(cpu.RIP, 4299853L)

    def test_PUNPCKLDQ_11(self):
        ''' Instruction PUNPCKLDQ_11 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c48] = 'f'
        mem[0x00419c49] = 'A'
        mem[0x00419c4a] = '\x0f'
        mem[0x00419c4b] = 'b'
        mem[0x00419c4c] = '\xc8'
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0x6000000040000000200000000
        cpu.RIP = 0x419c48
        cpu.execute()
    
        self.assertEqual(mem[0x419c48], 'f')
        self.assertEqual(mem[0x419c49], 'A')
        self.assertEqual(mem[0x419c4a], '\x0f')
        self.assertEqual(mem[0x419c4b], 'b')
        self.assertEqual(mem[0x419c4c], '\xc8')
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 36893488147419103232L)
        self.assertEqual(cpu.RIP, 4299853L)

    def test_PUNPCKLDQ_12(self):
        ''' Instruction PUNPCKLDQ_12 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c48] = 'f'
        mem[0x00419c49] = 'A'
        mem[0x00419c4a] = '\x0f'
        mem[0x00419c4b] = 'b'
        mem[0x00419c4c] = '\xc8'
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0x1e0000001c0000001a00000018
        cpu.RIP = 0x419c48
        cpu.execute()
    
        self.assertEqual(mem[0x419c48], 'f')
        self.assertEqual(mem[0x419c49], 'A')
        self.assertEqual(mem[0x419c4a], '\x0f')
        self.assertEqual(mem[0x419c4b], 'b')
        self.assertEqual(mem[0x419c4c], '\xc8')
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 479615345916448342040L)
        self.assertEqual(cpu.RIP, 4299853L)

    def test_PUNPCKLDQ_13(self):
        ''' Instruction PUNPCKLDQ_13 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c48] = 'f'
        mem[0x00419c49] = 'A'
        mem[0x00419c4a] = '\x0f'
        mem[0x00419c4b] = 'b'
        mem[0x00419c4c] = '\xc8'
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0xe0000000c0000000a00000008
        cpu.RIP = 0x419c48
        cpu.execute()
    
        self.assertEqual(mem[0x419c48], 'f')
        self.assertEqual(mem[0x419c49], 'A')
        self.assertEqual(mem[0x419c4a], '\x0f')
        self.assertEqual(mem[0x419c4b], 'b')
        self.assertEqual(mem[0x419c4c], '\xc8')
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 184467440737095516168L)
        self.assertEqual(cpu.RIP, 4299853L)

    def test_PUNPCKLDQ_14(self):
        ''' Instruction PUNPCKLDQ_14 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c48] = 'f'
        mem[0x00419c49] = 'A'
        mem[0x00419c4a] = '\x0f'
        mem[0x00419c4b] = 'b'
        mem[0x00419c4c] = '\xc8'
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0xee000000ec000000ea000000e8
        cpu.RIP = 0x419c48
        cpu.execute()
    
        self.assertEqual(mem[0x419c48], 'f')
        self.assertEqual(mem[0x419c49], 'A')
        self.assertEqual(mem[0x419c4a], '\x0f')
        self.assertEqual(mem[0x419c4b], 'b')
        self.assertEqual(mem[0x419c4c], '\xc8')
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 4316538113248035078376L)
        self.assertEqual(cpu.RIP, 4299853L)

    def test_PUNPCKLDQ_15(self):
        ''' Instruction PUNPCKLDQ_15 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c48] = 'f'
        mem[0x00419c49] = 'A'
        mem[0x00419c4a] = '\x0f'
        mem[0x00419c4b] = 'b'
        mem[0x00419c4c] = '\xc8'
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0x2e0000002c0000002a00000028
        cpu.RIP = 0x419c48
        cpu.execute()
    
        self.assertEqual(mem[0x419c48], 'f')
        self.assertEqual(mem[0x419c49], 'A')
        self.assertEqual(mem[0x419c4a], '\x0f')
        self.assertEqual(mem[0x419c4b], 'b')
        self.assertEqual(mem[0x419c4c], '\xc8')
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 774763251095801167912L)
        self.assertEqual(cpu.RIP, 4299853L)

    def test_PUNPCKLDQ_16(self):
        ''' Instruction PUNPCKLDQ_16 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c48] = 'f'
        mem[0x00419c49] = 'A'
        mem[0x00419c4a] = '\x0f'
        mem[0x00419c4b] = 'b'
        mem[0x00419c4c] = '\xc8'
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0xf6000000f4000000f2000000f0
        cpu.RIP = 0x419c48
        cpu.execute()
    
        self.assertEqual(mem[0x419c48], 'f')
        self.assertEqual(mem[0x419c49], 'A')
        self.assertEqual(mem[0x419c4a], '\x0f')
        self.assertEqual(mem[0x419c4b], 'b')
        self.assertEqual(mem[0x419c4c], '\xc8')
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 4464112065837711491312L)
        self.assertEqual(cpu.RIP, 4299853L)

    def test_PUNPCKLDQ_17(self):
        ''' Instruction PUNPCKLDQ_17 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c48] = 'f'
        mem[0x00419c49] = 'A'
        mem[0x00419c4a] = '\x0f'
        mem[0x00419c4b] = 'b'
        mem[0x00419c4c] = '\xc8'
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0x9e0000009c0000009a00000098
        cpu.RIP = 0x419c48
        cpu.execute()
    
        self.assertEqual(mem[0x419c48], 'f')
        self.assertEqual(mem[0x419c49], 'A')
        self.assertEqual(mem[0x419c4a], '\x0f')
        self.assertEqual(mem[0x419c4b], 'b')
        self.assertEqual(mem[0x419c4c], '\xc8')
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 2840798587351270949016L)
        self.assertEqual(cpu.RIP, 4299853L)

    def test_PUNPCKLDQ_18(self):
        ''' Instruction PUNPCKLDQ_18 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c48] = 'f'
        mem[0x00419c49] = 'A'
        mem[0x00419c4a] = '\x0f'
        mem[0x00419c4b] = 'b'
        mem[0x00419c4c] = '\xc8'
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0x16000000140000001200000010
        cpu.RIP = 0x419c48
        cpu.execute()
    
        self.assertEqual(mem[0x419c48], 'f')
        self.assertEqual(mem[0x419c49], 'A')
        self.assertEqual(mem[0x419c4a], '\x0f')
        self.assertEqual(mem[0x419c4b], 'b')
        self.assertEqual(mem[0x419c4c], '\xc8')
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 332041393326771929104L)
        self.assertEqual(cpu.RIP, 4299853L)

    def test_PUNPCKLDQ_19(self):
        ''' Instruction PUNPCKLDQ_19 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c48] = 'f'
        mem[0x00419c49] = 'A'
        mem[0x00419c4a] = '\x0f'
        mem[0x00419c4b] = 'b'
        mem[0x00419c4c] = '\xc8'
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0x96000000940000009200000090
        cpu.RIP = 0x419c48
        cpu.execute()
    
        self.assertEqual(mem[0x419c48], 'f')
        self.assertEqual(mem[0x419c49], 'A')
        self.assertEqual(mem[0x419c4a], '\x0f')
        self.assertEqual(mem[0x419c4b], 'b')
        self.assertEqual(mem[0x419c4c], '\xc8')
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 2693224634761594536080L)
        self.assertEqual(cpu.RIP, 4299853L)

    def test_PUNPCKLDQ_2(self):
        ''' Instruction PUNPCKLDQ_2 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c48] = 'f'
        mem[0x00419c49] = 'A'
        mem[0x00419c4a] = '\x0f'
        mem[0x00419c4b] = 'b'
        mem[0x00419c4c] = '\xc8'
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0x76000000740000007200000070
        cpu.RIP = 0x419c48
        cpu.execute()
    
        self.assertEqual(mem[0x419c48], 'f')
        self.assertEqual(mem[0x419c49], 'A')
        self.assertEqual(mem[0x419c4a], '\x0f')
        self.assertEqual(mem[0x419c4b], 'b')
        self.assertEqual(mem[0x419c4c], '\xc8')
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 2102928824402888884336L)
        self.assertEqual(cpu.RIP, 4299853L)

    def test_PUNPCKLDQ_20(self):
        ''' Instruction PUNPCKLDQ_20 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c48] = 'f'
        mem[0x00419c49] = 'A'
        mem[0x00419c4a] = '\x0f'
        mem[0x00419c4b] = 'b'
        mem[0x00419c4c] = '\xc8'
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0xde000000dc000000da000000d8
        cpu.RIP = 0x419c48
        cpu.execute()
    
        self.assertEqual(mem[0x419c48], 'f')
        self.assertEqual(mem[0x419c49], 'A')
        self.assertEqual(mem[0x419c4a], '\x0f')
        self.assertEqual(mem[0x419c4b], 'b')
        self.assertEqual(mem[0x419c4c], '\xc8')
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 4021390208068682252504L)
        self.assertEqual(cpu.RIP, 4299853L)

    def test_PUNPCKLDQ_21(self):
        ''' Instruction PUNPCKLDQ_21 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c48] = 'f'
        mem[0x00419c49] = 'A'
        mem[0x00419c4a] = '\x0f'
        mem[0x00419c4b] = 'b'
        mem[0x00419c4c] = '\xc8'
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0xe6000000e4000000e2000000e0
        cpu.RIP = 0x419c48
        cpu.execute()
    
        self.assertEqual(mem[0x419c48], 'f')
        self.assertEqual(mem[0x419c49], 'A')
        self.assertEqual(mem[0x419c4a], '\x0f')
        self.assertEqual(mem[0x419c4b], 'b')
        self.assertEqual(mem[0x419c4c], '\xc8')
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 4168964160658358665440L)
        self.assertEqual(cpu.RIP, 4299853L)

    def test_PUNPCKLDQ_3(self):
        ''' Instruction PUNPCKLDQ_3 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c48] = 'f'
        mem[0x00419c49] = 'A'
        mem[0x00419c4a] = '\x0f'
        mem[0x00419c4b] = 'b'
        mem[0x00419c4c] = '\xc8'
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0x36000000340000003200000030
        cpu.RIP = 0x419c48
        cpu.execute()
    
        self.assertEqual(mem[0x419c48], 'f')
        self.assertEqual(mem[0x419c49], 'A')
        self.assertEqual(mem[0x419c4a], '\x0f')
        self.assertEqual(mem[0x419c4b], 'b')
        self.assertEqual(mem[0x419c4c], '\xc8')
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 922337203685477580848L)
        self.assertEqual(cpu.RIP, 4299853L)

    def test_PUNPCKLDQ_4(self):
        ''' Instruction PUNPCKLDQ_4 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c48] = 'f'
        mem[0x00419c49] = 'A'
        mem[0x00419c4a] = '\x0f'
        mem[0x00419c4b] = 'b'
        mem[0x00419c4c] = '\xc8'
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0x6e0000006c0000006a00000068
        cpu.RIP = 0x419c48
        cpu.execute()
    
        self.assertEqual(mem[0x419c48], 'f')
        self.assertEqual(mem[0x419c49], 'A')
        self.assertEqual(mem[0x419c4a], '\x0f')
        self.assertEqual(mem[0x419c4b], 'b')
        self.assertEqual(mem[0x419c4c], '\xc8')
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 1955354871813212471400L)
        self.assertEqual(cpu.RIP, 4299853L)

    def test_PUNPCKLDQ_5(self):
        ''' Instruction PUNPCKLDQ_5 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c48] = 'f'
        mem[0x00419c49] = 'A'
        mem[0x00419c4a] = '\x0f'
        mem[0x00419c4b] = 'b'
        mem[0x00419c4c] = '\xc8'
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0x7e0000007c0000007a00000078
        cpu.RIP = 0x419c48
        cpu.execute()
    
        self.assertEqual(mem[0x419c48], 'f')
        self.assertEqual(mem[0x419c49], 'A')
        self.assertEqual(mem[0x419c4a], '\x0f')
        self.assertEqual(mem[0x419c4b], 'b')
        self.assertEqual(mem[0x419c4c], '\xc8')
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 2250502776992565297272L)
        self.assertEqual(cpu.RIP, 4299853L)

    def test_PUNPCKLDQ_6(self):
        ''' Instruction PUNPCKLDQ_6 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c48] = 'f'
        mem[0x00419c49] = 'A'
        mem[0x00419c4a] = '\x0f'
        mem[0x00419c4b] = 'b'
        mem[0x00419c4c] = '\xc8'
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0x26000000240000002200000020
        cpu.RIP = 0x419c48
        cpu.execute()
    
        self.assertEqual(mem[0x419c48], 'f')
        self.assertEqual(mem[0x419c49], 'A')
        self.assertEqual(mem[0x419c4a], '\x0f')
        self.assertEqual(mem[0x419c4b], 'b')
        self.assertEqual(mem[0x419c4c], '\xc8')
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 627189298506124754976L)
        self.assertEqual(cpu.RIP, 4299853L)

    def test_PUNPCKLDQ_7(self):
        ''' Instruction PUNPCKLDQ_7 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c48] = 'f'
        mem[0x00419c49] = 'A'
        mem[0x00419c4a] = '\x0f'
        mem[0x00419c4b] = 'b'
        mem[0x00419c4c] = '\xc8'
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0xbe000000bc000000ba000000b8
        cpu.RIP = 0x419c48
        cpu.execute()
    
        self.assertEqual(mem[0x419c48], 'f')
        self.assertEqual(mem[0x419c49], 'A')
        self.assertEqual(mem[0x419c4a], '\x0f')
        self.assertEqual(mem[0x419c4b], 'b')
        self.assertEqual(mem[0x419c4c], '\xc8')
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 3431094397709976600760L)
        self.assertEqual(cpu.RIP, 4299853L)

    def test_PUNPCKLDQ_8(self):
        ''' Instruction PUNPCKLDQ_8 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c48] = 'f'
        mem[0x00419c49] = 'A'
        mem[0x00419c4a] = '\x0f'
        mem[0x00419c4b] = 'b'
        mem[0x00419c4c] = '\xc8'
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0xce000000cc000000ca000000c8
        cpu.RIP = 0x419c48
        cpu.execute()
    
        self.assertEqual(mem[0x419c48], 'f')
        self.assertEqual(mem[0x419c49], 'A')
        self.assertEqual(mem[0x419c4a], '\x0f')
        self.assertEqual(mem[0x419c4b], 'b')
        self.assertEqual(mem[0x419c4c], '\xc8')
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 3726242302889329426632L)
        self.assertEqual(cpu.RIP, 4299853L)

    def test_PUNPCKLDQ_9(self):
        ''' Instruction PUNPCKLDQ_9 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c48] = 'f'
        mem[0x00419c49] = 'A'
        mem[0x00419c4a] = '\x0f'
        mem[0x00419c4b] = 'b'
        mem[0x00419c4c] = '\xc8'
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0x46000000440000004200000040
        cpu.RIP = 0x419c48
        cpu.execute()
    
        self.assertEqual(mem[0x419c48], 'f')
        self.assertEqual(mem[0x419c49], 'A')
        self.assertEqual(mem[0x419c4a], '\x0f')
        self.assertEqual(mem[0x419c4b], 'b')
        self.assertEqual(mem[0x419c4c], '\xc8')
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 1217485108864830406720L)
        self.assertEqual(cpu.RIP, 4299853L)

    def test_PUNPCKLQDQ_1(self):
        ''' Instruction PUNPCKLQDQ_1 
            Groups: sse2 
            0x419c82:	punpcklqdq	xmm1, xmm0
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c82] = 'f'
        mem[0x00419c83] = '\x0f'
        mem[0x00419c84] = 'l'
        mem[0x00419c85] = '\xc8'
        cpu.XMM0 = 0x6cbfc800000000006cbfb8
        cpu.XMM1 = 0x6cbfc800000000006cbfb8
        cpu.RIP = 0x419c82
        cpu.execute()
    
        self.assertEqual(mem[0x419c82], 'f')
        self.assertEqual(mem[0x419c83], '\x0f')
        self.assertEqual(mem[0x419c84], 'l')
        self.assertEqual(mem[0x419c85], '\xc8')
        self.assertEqual(cpu.XMM0, 131469649865422795021533112L)
        self.assertEqual(cpu.XMM1, 131469354717517615668707256L)
        self.assertEqual(cpu.RIP, 4299910L)

    def test_PUNPCKLQDQ_10(self):
        ''' Instruction PUNPCKLQDQ_10 
            Groups: sse2 
            0x419c6c:	punpcklqdq	xmm8, xmm1
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c70] = '\xc1'
        mem[0x00419c6c] = 'f'
        mem[0x00419c6d] = 'D'
        mem[0x00419c6e] = '\x0f'
        mem[0x00419c6f] = 'l'
        cpu.XMM8 = 0x6cbc6800000000006cbc58
        cpu.XMM1 = 0x6cbc6800000000006cbc58
        cpu.RIP = 0x419c6c
        cpu.execute()
    
        self.assertEqual(mem[0x419c70], '\xc1')
        self.assertEqual(mem[0x419c6c], 'f')
        self.assertEqual(mem[0x419c6d], 'D')
        self.assertEqual(mem[0x419c6e], '\x0f')
        self.assertEqual(mem[0x419c6f], 'l')
        self.assertEqual(cpu.XMM8, 131453416730637930616110168L)
        self.assertEqual(cpu.XMM1, 131453711878543109968936024L)
        self.assertEqual(cpu.RIP, 4299889L)

    def test_PUNPCKLQDQ_11(self):
        ''' Instruction PUNPCKLQDQ_11 
            Groups: sse2 
            0x419c82:	punpcklqdq	xmm1, xmm0
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c82] = 'f'
        mem[0x00419c83] = '\x0f'
        mem[0x00419c84] = 'l'
        mem[0x00419c85] = '\xc8'
        cpu.XMM0 = 0x6cbb4800000000006cbb38
        cpu.XMM1 = 0x6cbb4800000000006cbb38
        cpu.RIP = 0x419c82
        cpu.execute()
    
        self.assertEqual(mem[0x419c82], 'f')
        self.assertEqual(mem[0x419c83], '\x0f')
        self.assertEqual(mem[0x419c84], 'l')
        self.assertEqual(mem[0x419c85], '\xc8')
        self.assertEqual(cpu.XMM0, 131448399216249881618070328L)
        self.assertEqual(cpu.XMM1, 131448104068344702265244472L)
        self.assertEqual(cpu.RIP, 4299910L)

    def test_PUNPCKLQDQ_12(self):
        ''' Instruction PUNPCKLQDQ_12 
            Groups: sse2 
            0x419c6c:	punpcklqdq	xmm8, xmm1
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c70] = '\xc1'
        mem[0x00419c6c] = 'f'
        mem[0x00419c6d] = 'D'
        mem[0x00419c6e] = '\x0f'
        mem[0x00419c6f] = 'l'
        cpu.XMM8 = 0x6cbde800000000006cbdd8
        cpu.XMM1 = 0x6cbde800000000006cbdd8
        cpu.RIP = 0x419c6c
        cpu.execute()
    
        self.assertEqual(mem[0x419c70], '\xc1')
        self.assertEqual(mem[0x419c6c], 'f')
        self.assertEqual(mem[0x419c6d], 'D')
        self.assertEqual(mem[0x419c6e], '\x0f')
        self.assertEqual(mem[0x419c6f], 'l')
        self.assertEqual(cpu.XMM8, 131460500280362235083931096L)
        self.assertEqual(cpu.XMM1, 131460795428267414436756952L)
        self.assertEqual(cpu.RIP, 4299889L)

    def test_PUNPCKLQDQ_13(self):
        ''' Instruction PUNPCKLQDQ_13 
            Groups: sse2 
            0x419c6c:	punpcklqdq	xmm8, xmm1
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c70] = '\xc1'
        mem[0x00419c6c] = 'f'
        mem[0x00419c6d] = 'D'
        mem[0x00419c6e] = '\x0f'
        mem[0x00419c6f] = 'l'
        cpu.XMM8 = 0x6cbee800000000006cbed8
        cpu.XMM1 = 0x6cbee800000000006cbed8
        cpu.RIP = 0x419c6c
        cpu.execute()
    
        self.assertEqual(mem[0x419c70], '\xc1')
        self.assertEqual(mem[0x419c6c], 'f')
        self.assertEqual(mem[0x419c6d], 'D')
        self.assertEqual(mem[0x419c6e], '\x0f')
        self.assertEqual(mem[0x419c6f], 'l')
        self.assertEqual(cpu.XMM8, 131465222646845104729145048L)
        self.assertEqual(cpu.XMM1, 131465517794750284081970904L)
        self.assertEqual(cpu.RIP, 4299889L)

    def test_PUNPCKLQDQ_14(self):
        ''' Instruction PUNPCKLQDQ_14 
            Groups: sse2 
            0x419c6c:	punpcklqdq	xmm8, xmm1
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c70] = '\xc1'
        mem[0x00419c6c] = 'f'
        mem[0x00419c6d] = 'D'
        mem[0x00419c6e] = '\x0f'
        mem[0x00419c6f] = 'l'
        cpu.XMM8 = 0x6cbba800000000006cbb98
        cpu.XMM1 = 0x6cbba800000000006cbb98
        cpu.RIP = 0x419c6c
        cpu.execute()
    
        self.assertEqual(mem[0x419c70], '\xc1')
        self.assertEqual(mem[0x419c6c], 'f')
        self.assertEqual(mem[0x419c6d], 'D')
        self.assertEqual(mem[0x419c6e], '\x0f')
        self.assertEqual(mem[0x419c6f], 'l')
        self.assertEqual(cpu.XMM8, 131449874955775778382199704L)
        self.assertEqual(cpu.XMM1, 131450170103680957735025560L)
        self.assertEqual(cpu.RIP, 4299889L)

    def test_PUNPCKLQDQ_15(self):
        ''' Instruction PUNPCKLQDQ_15 
            Groups: sse2 
            0x419c82:	punpcklqdq	xmm1, xmm0
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c82] = 'f'
        mem[0x00419c83] = '\x0f'
        mem[0x00419c84] = 'l'
        mem[0x00419c85] = '\xc8'
        cpu.XMM0 = 0x6cbcc800000000006cbcb8
        cpu.XMM1 = 0x6cbcc800000000006cbcb8
        cpu.RIP = 0x419c82
        cpu.execute()
    
        self.assertEqual(mem[0x419c82], 'f')
        self.assertEqual(mem[0x419c83], '\x0f')
        self.assertEqual(mem[0x419c84], 'l')
        self.assertEqual(mem[0x419c85], '\xc8')
        self.assertEqual(cpu.XMM0, 131455482765974186085891256L)
        self.assertEqual(cpu.XMM1, 131455187618069006733065400L)
        self.assertEqual(cpu.RIP, 4299910L)

    def test_PUNPCKLQDQ_16(self):
        ''' Instruction PUNPCKLQDQ_16 
            Groups: sse2 
            0x419c82:	punpcklqdq	xmm1, xmm0
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c82] = 'f'
        mem[0x00419c83] = '\x0f'
        mem[0x00419c84] = 'l'
        mem[0x00419c85] = '\xc8'
        cpu.XMM0 = 0x6cbe0800000000006cbdf8
        cpu.XMM1 = 0x6cbe0800000000006cbdf8
        cpu.RIP = 0x419c82
        cpu.execute()
    
        self.assertEqual(mem[0x419c82], 'f')
        self.assertEqual(mem[0x419c83], '\x0f')
        self.assertEqual(mem[0x419c84], 'l')
        self.assertEqual(mem[0x419c85], '\xc8')
        self.assertEqual(cpu.XMM0, 131461385724077773142408696L)
        self.assertEqual(cpu.XMM1, 131461090576172593789582840L)
        self.assertEqual(cpu.RIP, 4299910L)

    def test_PUNPCKLQDQ_17(self):
        ''' Instruction PUNPCKLQDQ_17 
            Groups: sse2 
            0x419c82:	punpcklqdq	xmm1, xmm0
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c82] = 'f'
        mem[0x00419c83] = '\x0f'
        mem[0x00419c84] = 'l'
        mem[0x00419c85] = '\xc8'
        cpu.XMM0 = 0x6cbec800000000006cbeb8
        cpu.XMM1 = 0x6cbec800000000006cbeb8
        cpu.RIP = 0x419c82
        cpu.execute()
    
        self.assertEqual(mem[0x419c82], 'f')
        self.assertEqual(mem[0x419c83], '\x0f')
        self.assertEqual(mem[0x419c84], 'l')
        self.assertEqual(mem[0x419c85], '\xc8')
        self.assertEqual(cpu.XMM0, 131464927498939925376319160L)
        self.assertEqual(cpu.XMM1, 131464632351034746023493304L)
        self.assertEqual(cpu.RIP, 4299910L)

    def test_PUNPCKLQDQ_18(self):
        ''' Instruction PUNPCKLQDQ_18 
            Groups: sse2 
            0x419c6c:	punpcklqdq	xmm8, xmm1
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c70] = '\xc1'
        mem[0x00419c6c] = 'f'
        mem[0x00419c6d] = 'D'
        mem[0x00419c6e] = '\x0f'
        mem[0x00419c6f] = 'l'
        cpu.XMM8 = 0x6cbbe800000000006cbbd8
        cpu.XMM1 = 0x6cbbe800000000006cbbd8
        cpu.RIP = 0x419c6c
        cpu.execute()
    
        self.assertEqual(mem[0x419c70], '\xc1')
        self.assertEqual(mem[0x419c6c], 'f')
        self.assertEqual(mem[0x419c6d], 'D')
        self.assertEqual(mem[0x419c6e], '\x0f')
        self.assertEqual(mem[0x419c6f], 'l')
        self.assertEqual(cpu.XMM8, 131451055547396495793503192L)
        self.assertEqual(cpu.XMM1, 131451350695301675146329048L)
        self.assertEqual(cpu.RIP, 4299889L)

    def test_PUNPCKLQDQ_19(self):
        ''' Instruction PUNPCKLQDQ_19 
            Groups: sse2 
            0x419c82:	punpcklqdq	xmm1, xmm0
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c82] = 'f'
        mem[0x00419c83] = '\x0f'
        mem[0x00419c84] = 'l'
        mem[0x00419c85] = '\xc8'
        cpu.XMM0 = 0x6cbc8800000000006cbc78
        cpu.XMM1 = 0x6cbc8800000000006cbc78
        cpu.RIP = 0x419c82
        cpu.execute()
    
        self.assertEqual(mem[0x419c82], 'f')
        self.assertEqual(mem[0x419c83], '\x0f')
        self.assertEqual(mem[0x419c84], 'l')
        self.assertEqual(mem[0x419c85], '\xc8')
        self.assertEqual(cpu.XMM0, 131454302174353468674587768L)
        self.assertEqual(cpu.XMM1, 131454007026448289321761912L)
        self.assertEqual(cpu.RIP, 4299910L)

    def test_PUNPCKLQDQ_2(self):
        ''' Instruction PUNPCKLQDQ_2 
            Groups: sse2 
            0x419c6c:	punpcklqdq	xmm8, xmm1
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c70] = '\xc1'
        mem[0x00419c6c] = 'f'
        mem[0x00419c6d] = 'D'
        mem[0x00419c6e] = '\x0f'
        mem[0x00419c6f] = 'l'
        cpu.XMM8 = 0x6cbf6800000000006cbf58
        cpu.XMM1 = 0x6cbf6800000000006cbf58
        cpu.RIP = 0x419c6c
        cpu.execute()
    
        self.assertEqual(mem[0x419c70], '\xc1')
        self.assertEqual(mem[0x419c6c], 'f')
        self.assertEqual(mem[0x419c6d], 'D')
        self.assertEqual(mem[0x419c6e], '\x0f')
        self.assertEqual(mem[0x419c6f], 'l')
        self.assertEqual(cpu.XMM8, 131467583830086539551752024L)
        self.assertEqual(cpu.XMM1, 131467878977991718904577880L)
        self.assertEqual(cpu.RIP, 4299889L)

    def test_PUNPCKLQDQ_20(self):
        ''' Instruction PUNPCKLQDQ_20 
            Groups: sse2 
            0x419c82:	punpcklqdq	xmm1, xmm0
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c82] = 'f'
        mem[0x00419c83] = '\x0f'
        mem[0x00419c84] = 'l'
        mem[0x00419c85] = '\xc8'
        cpu.XMM0 = 0x6cba8800000000006cba78
        cpu.XMM1 = 0x6cba8800000000006cba78
        cpu.RIP = 0x419c82
        cpu.execute()
    
        self.assertEqual(mem[0x419c82], 'f')
        self.assertEqual(mem[0x419c83], '\x0f')
        self.assertEqual(mem[0x419c84], 'l')
        self.assertEqual(mem[0x419c85], '\xc8')
        self.assertEqual(cpu.XMM0, 131444857441387729384159864L)
        self.assertEqual(cpu.XMM1, 131444562293482550031334008L)
        self.assertEqual(cpu.RIP, 4299910L)

    def test_PUNPCKLQDQ_21(self):
        ''' Instruction PUNPCKLQDQ_21 
            Groups: sse2 
            0x419c6c:	punpcklqdq	xmm8, xmm1
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c70] = '\xc1'
        mem[0x00419c6c] = 'f'
        mem[0x00419c6d] = 'D'
        mem[0x00419c6e] = '\x0f'
        mem[0x00419c6f] = 'l'
        cpu.XMM8 = 0x6cb96800000000006cb958
        cpu.XMM1 = 0x6cb96800000000006cb958
        cpu.RIP = 0x419c6c
        cpu.execute()
    
        self.assertEqual(mem[0x419c70], '\xc1')
        self.assertEqual(mem[0x419c6c], 'f')
        self.assertEqual(mem[0x419c6d], 'D')
        self.assertEqual(mem[0x419c6e], '\x0f')
        self.assertEqual(mem[0x419c6f], 'l')
        self.assertEqual(cpu.XMM8, 131439249631189321680468312L)
        self.assertEqual(cpu.XMM1, 131439544779094501033294168L)
        self.assertEqual(cpu.RIP, 4299889L)

    def test_PUNPCKLQDQ_3(self):
        ''' Instruction PUNPCKLQDQ_3 
            Groups: sse2 
            0x419c6c:	punpcklqdq	xmm8, xmm1
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c70] = '\xc1'
        mem[0x00419c6c] = 'f'
        mem[0x00419c6d] = 'D'
        mem[0x00419c6e] = '\x0f'
        mem[0x00419c6f] = 'l'
        cpu.XMM8 = 0x6cbb2800000000006cbb18
        cpu.XMM1 = 0x6cbb2800000000006cbb18
        cpu.RIP = 0x419c6c
        cpu.execute()
    
        self.assertEqual(mem[0x419c70], '\xc1')
        self.assertEqual(mem[0x419c6c], 'f')
        self.assertEqual(mem[0x419c6d], 'D')
        self.assertEqual(mem[0x419c6e], '\x0f')
        self.assertEqual(mem[0x419c6f], 'l')
        self.assertEqual(cpu.XMM8, 131447513772534343559592728L)
        self.assertEqual(cpu.XMM1, 131447808920439522912418584L)
        self.assertEqual(cpu.RIP, 4299889L)

    def test_PUNPCKLQDQ_4(self):
        ''' Instruction PUNPCKLQDQ_4 
            Groups: sse2 
            0x419c6c:	punpcklqdq	xmm8, xmm1
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c70] = '\xc1'
        mem[0x00419c6c] = 'f'
        mem[0x00419c6d] = 'D'
        mem[0x00419c6e] = '\x0f'
        mem[0x00419c6f] = 'l'
        cpu.XMM8 = 0x6cb8a800000000006cb898
        cpu.XMM1 = 0x6cb8a800000000006cb898
        cpu.RIP = 0x419c6c
        cpu.execute()
    
        self.assertEqual(mem[0x419c70], '\xc1')
        self.assertEqual(mem[0x419c6c], 'f')
        self.assertEqual(mem[0x419c6d], 'D')
        self.assertEqual(mem[0x419c6e], '\x0f')
        self.assertEqual(mem[0x419c6f], 'l')
        self.assertEqual(cpu.XMM8, 131435707856327169446557848L)
        self.assertEqual(cpu.XMM1, 131436003004232348799383704L)
        self.assertEqual(cpu.RIP, 4299889L)

    def test_PUNPCKLQDQ_5(self):
        ''' Instruction PUNPCKLQDQ_5 
            Groups: sse2 
            0x419c6c:	punpcklqdq	xmm8, xmm1
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c70] = '\xc1'
        mem[0x00419c6c] = 'f'
        mem[0x00419c6d] = 'D'
        mem[0x00419c6e] = '\x0f'
        mem[0x00419c6f] = 'l'
        cpu.XMM8 = 0x6cbc2800000000006cbc18
        cpu.XMM1 = 0x6cbc2800000000006cbc18
        cpu.RIP = 0x419c6c
        cpu.execute()
    
        self.assertEqual(mem[0x419c70], '\xc1')
        self.assertEqual(mem[0x419c6c], 'f')
        self.assertEqual(mem[0x419c6d], 'D')
        self.assertEqual(mem[0x419c6e], '\x0f')
        self.assertEqual(mem[0x419c6f], 'l')
        self.assertEqual(cpu.XMM8, 131452236139017213204806680L)
        self.assertEqual(cpu.XMM1, 131452531286922392557632536L)
        self.assertEqual(cpu.RIP, 4299889L)

    def test_PUNPCKLQDQ_6(self):
        ''' Instruction PUNPCKLQDQ_6 
            Groups: sse2 
            0x419c82:	punpcklqdq	xmm1, xmm0
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c82] = 'f'
        mem[0x00419c83] = '\x0f'
        mem[0x00419c84] = 'l'
        mem[0x00419c85] = '\xc8'
        cpu.XMM0 = 0x6cbf4800000000006cbf38
        cpu.XMM1 = 0x6cbf4800000000006cbf38
        cpu.RIP = 0x419c82
        cpu.execute()
    
        self.assertEqual(mem[0x419c82], 'f')
        self.assertEqual(mem[0x419c83], '\x0f')
        self.assertEqual(mem[0x419c84], 'l')
        self.assertEqual(mem[0x419c85], '\xc8')
        self.assertEqual(cpu.XMM0, 131467288682181360198926136L)
        self.assertEqual(cpu.XMM1, 131466993534276180846100280L)
        self.assertEqual(cpu.RIP, 4299910L)

    def test_PUNPCKLQDQ_7(self):
        ''' Instruction PUNPCKLQDQ_7 
            Groups: sse2 
            0x419c6c:	punpcklqdq	xmm8, xmm1
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c70] = '\xc1'
        mem[0x00419c6c] = 'f'
        mem[0x00419c6d] = 'D'
        mem[0x00419c6e] = '\x0f'
        mem[0x00419c6f] = 'l'
        cpu.XMM8 = 0x6cba6800000000006cba58
        cpu.XMM1 = 0x6cba6800000000006cba58
        cpu.RIP = 0x419c6c
        cpu.execute()
    
        self.assertEqual(mem[0x419c70], '\xc1')
        self.assertEqual(mem[0x419c6c], 'f')
        self.assertEqual(mem[0x419c6d], 'D')
        self.assertEqual(mem[0x419c6e], '\x0f')
        self.assertEqual(mem[0x419c6f], 'l')
        self.assertEqual(cpu.XMM8, 131443971997672191325682264L)
        self.assertEqual(cpu.XMM1, 131444267145577370678508120L)
        self.assertEqual(cpu.RIP, 4299889L)

    def test_PUNPCKLQDQ_8(self):
        ''' Instruction PUNPCKLQDQ_8 
            Groups: sse2 
            0x419c82:	punpcklqdq	xmm1, xmm0
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c82] = 'f'
        mem[0x00419c83] = '\x0f'
        mem[0x00419c84] = 'l'
        mem[0x00419c85] = '\xc8'
        cpu.XMM0 = 0x6cba0800000000006cb9f8
        cpu.XMM1 = 0x6cba0800000000006cb9f8
        cpu.RIP = 0x419c82
        cpu.execute()
    
        self.assertEqual(mem[0x419c82], 'f')
        self.assertEqual(mem[0x419c83], '\x0f')
        self.assertEqual(mem[0x419c84], 'l')
        self.assertEqual(mem[0x419c85], '\xc8')
        self.assertEqual(cpu.XMM0, 131442496258146294561552888L)
        self.assertEqual(cpu.XMM1, 131442201110241115208727032L)
        self.assertEqual(cpu.RIP, 4299910L)

    def test_PUNPCKLQDQ_9(self):
        ''' Instruction PUNPCKLQDQ_9 
            Groups: sse2 
            0x419c82:	punpcklqdq	xmm1, xmm0
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x00419c82] = 'f'
        mem[0x00419c83] = '\x0f'
        mem[0x00419c84] = 'l'
        mem[0x00419c85] = '\xc8'
        cpu.XMM0 = 0x6cbdc800000000006cbdb8
        cpu.XMM1 = 0x6cbdc800000000006cbdb8
        cpu.RIP = 0x419c82
        cpu.execute()
    
        self.assertEqual(mem[0x419c82], 'f')
        self.assertEqual(mem[0x419c83], '\x0f')
        self.assertEqual(mem[0x419c84], 'l')
        self.assertEqual(mem[0x419c85], '\xc8')
        self.assertEqual(cpu.XMM0, 131460205132457055731105208L)
        self.assertEqual(cpu.XMM1, 131459909984551876378279352L)
        self.assertEqual(cpu.RIP, 4299910L)

    def test_PUNPCKLWD_1(self):
        ''' Instruction PUNPCKLWD_1 
            Groups: sse2 
            0x4668b6:	punpcklwd	xmm1, xmm1
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00466000, 0x1000, 'rwx')
        mem[0x004668b8] = 'a'
        mem[0x004668b9] = '\xc9'
        mem[0x004668b6] = 'f'
        mem[0x004668b7] = '\x0f'
        cpu.XMM1 = 0x2f2f
        cpu.RIP = 0x4668b6
        cpu.execute()
    
        self.assertEqual(mem[0x4668b8], 'a')
        self.assertEqual(mem[0x4668b9], '\xc9')
        self.assertEqual(mem[0x4668b6], 'f')
        self.assertEqual(mem[0x4668b7], '\x0f')
        self.assertEqual(cpu.XMM1, 791621423)
        self.assertEqual(cpu.RIP, 4614330L)

    def test_PUNPCKHDQ_1_symbolic(self):
        ''' Instruction PUNPCKHDQ_1 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c43] = 'f'
        mem[0x419c44] = 'A'
        mem[0x419c45] = '\x0f'
        mem[0x419c46] = 'j'
        mem[0x419c47] = '\xc0'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x4e0000004c0000004a00000048)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419c43

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c43, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c44, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c45, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c46, 8)== ord('j'))
        condition = Operators.AND(condition, cpu.read_int(0x419c47, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x4e000000000000004c)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419c48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHDQ_10_symbolic(self):
        ''' Instruction PUNPCKHDQ_10 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c43] = 'f'
        mem[0x419c44] = 'A'
        mem[0x419c45] = '\x0f'
        mem[0x419c46] = 'j'
        mem[0x419c47] = '\xc0'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x36000000340000003200000030)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419c43

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c43, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c44, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c45, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c46, 8)== ord('j'))
        condition = Operators.AND(condition, cpu.read_int(0x419c47, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x360000000000000034)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419c48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHDQ_11_symbolic(self):
        ''' Instruction PUNPCKHDQ_11 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c43] = 'f'
        mem[0x419c44] = 'A'
        mem[0x419c45] = '\x0f'
        mem[0x419c46] = 'j'
        mem[0x419c47] = '\xc0'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x3e0000003c0000003a00000038)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419c43

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c43, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c44, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c45, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c46, 8)== ord('j'))
        condition = Operators.AND(condition, cpu.read_int(0x419c47, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x3e000000000000003c)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419c48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHDQ_12_symbolic(self):
        ''' Instruction PUNPCKHDQ_12 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c43] = 'f'
        mem[0x419c44] = 'A'
        mem[0x419c45] = '\x0f'
        mem[0x419c46] = 'j'
        mem[0x419c47] = '\xc0'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x8e0000008c0000008a00000088)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419c43

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c43, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c44, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c45, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c46, 8)== ord('j'))
        condition = Operators.AND(condition, cpu.read_int(0x419c47, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x8e000000000000008c)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419c48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHDQ_13_symbolic(self):
        ''' Instruction PUNPCKHDQ_13 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c43] = 'f'
        mem[0x419c44] = 'A'
        mem[0x419c45] = '\x0f'
        mem[0x419c46] = 'j'
        mem[0x419c47] = '\xc0'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0xe6000000e4000000e2000000e0)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419c43

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c43, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c44, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c45, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c46, 8)== ord('j'))
        condition = Operators.AND(condition, cpu.read_int(0x419c47, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.XMM0 == 0xe600000000000000e4)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419c48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHDQ_14_symbolic(self):
        ''' Instruction PUNPCKHDQ_14 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c43] = 'f'
        mem[0x419c44] = 'A'
        mem[0x419c45] = '\x0f'
        mem[0x419c46] = 'j'
        mem[0x419c47] = '\xc0'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x7e0000007c0000007a00000078)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419c43

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c43, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c44, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c45, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c46, 8)== ord('j'))
        condition = Operators.AND(condition, cpu.read_int(0x419c47, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x7e000000000000007c)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419c48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHDQ_15_symbolic(self):
        ''' Instruction PUNPCKHDQ_15 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c43] = 'f'
        mem[0x419c44] = 'A'
        mem[0x419c45] = '\x0f'
        mem[0x419c46] = 'j'
        mem[0x419c47] = '\xc0'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x96000000940000009200000090)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419c43

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c43, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c44, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c45, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c46, 8)== ord('j'))
        condition = Operators.AND(condition, cpu.read_int(0x419c47, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x960000000000000094)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419c48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHDQ_16_symbolic(self):
        ''' Instruction PUNPCKHDQ_16 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c43] = 'f'
        mem[0x419c44] = 'A'
        mem[0x419c45] = '\x0f'
        mem[0x419c46] = 'j'
        mem[0x419c47] = '\xc0'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6000000040000000200000000)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419c43

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c43, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c44, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c45, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c46, 8)== ord('j'))
        condition = Operators.AND(condition, cpu.read_int(0x419c47, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x60000000000000004)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419c48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHDQ_17_symbolic(self):
        ''' Instruction PUNPCKHDQ_17 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c43] = 'f'
        mem[0x419c44] = 'A'
        mem[0x419c45] = '\x0f'
        mem[0x419c46] = 'j'
        mem[0x419c47] = '\xc0'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0xce000000cc000000ca000000c8)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419c43

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c43, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c44, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c45, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c46, 8)== ord('j'))
        condition = Operators.AND(condition, cpu.read_int(0x419c47, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.XMM0 == 0xce00000000000000cc)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419c48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHDQ_18_symbolic(self):
        ''' Instruction PUNPCKHDQ_18 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c43] = 'f'
        mem[0x419c44] = 'A'
        mem[0x419c45] = '\x0f'
        mem[0x419c46] = 'j'
        mem[0x419c47] = '\xc0'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x9e0000009c0000009a00000098)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419c43

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c43, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c44, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c45, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c46, 8)== ord('j'))
        condition = Operators.AND(condition, cpu.read_int(0x419c47, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x9e000000000000009c)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419c48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHDQ_19_symbolic(self):
        ''' Instruction PUNPCKHDQ_19 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c43] = 'f'
        mem[0x419c44] = 'A'
        mem[0x419c45] = '\x0f'
        mem[0x419c46] = 'j'
        mem[0x419c47] = '\xc0'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x46000000440000004200000040)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419c43

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c43, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c44, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c45, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c46, 8)== ord('j'))
        condition = Operators.AND(condition, cpu.read_int(0x419c47, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x460000000000000044)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419c48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHDQ_2_symbolic(self):
        ''' Instruction PUNPCKHDQ_2 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c43] = 'f'
        mem[0x419c44] = 'A'
        mem[0x419c45] = '\x0f'
        mem[0x419c46] = 'j'
        mem[0x419c47] = '\xc0'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0xbe000000bc000000ba000000b8)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419c43

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c43, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c44, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c45, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c46, 8)== ord('j'))
        condition = Operators.AND(condition, cpu.read_int(0x419c47, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.XMM0 == 0xbe00000000000000bc)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419c48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHDQ_20_symbolic(self):
        ''' Instruction PUNPCKHDQ_20 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c43] = 'f'
        mem[0x419c44] = 'A'
        mem[0x419c45] = '\x0f'
        mem[0x419c46] = 'j'
        mem[0x419c47] = '\xc0'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x66000000640000006200000060)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419c43

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c43, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c44, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c45, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c46, 8)== ord('j'))
        condition = Operators.AND(condition, cpu.read_int(0x419c47, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x660000000000000064)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419c48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHDQ_21_symbolic(self):
        ''' Instruction PUNPCKHDQ_21 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c43] = 'f'
        mem[0x419c44] = 'A'
        mem[0x419c45] = '\x0f'
        mem[0x419c46] = 'j'
        mem[0x419c47] = '\xc0'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x5e0000005c0000005a00000058)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419c43

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c43, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c44, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c45, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c46, 8)== ord('j'))
        condition = Operators.AND(condition, cpu.read_int(0x419c47, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x5e000000000000005c)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419c48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHDQ_3_symbolic(self):
        ''' Instruction PUNPCKHDQ_3 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c43] = 'f'
        mem[0x419c44] = 'A'
        mem[0x419c45] = '\x0f'
        mem[0x419c46] = 'j'
        mem[0x419c47] = '\xc0'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6e0000006c0000006a00000068)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419c43

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c43, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c44, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c45, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c46, 8)== ord('j'))
        condition = Operators.AND(condition, cpu.read_int(0x419c47, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6e000000000000006c)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419c48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHDQ_4_symbolic(self):
        ''' Instruction PUNPCKHDQ_4 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c43] = 'f'
        mem[0x419c44] = 'A'
        mem[0x419c45] = '\x0f'
        mem[0x419c46] = 'j'
        mem[0x419c47] = '\xc0'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0xc6000000c4000000c2000000c0)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419c43

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c43, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c44, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c45, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c46, 8)== ord('j'))
        condition = Operators.AND(condition, cpu.read_int(0x419c47, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.XMM0 == 0xc600000000000000c4)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419c48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHDQ_5_symbolic(self):
        ''' Instruction PUNPCKHDQ_5 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c43] = 'f'
        mem[0x419c44] = 'A'
        mem[0x419c45] = '\x0f'
        mem[0x419c46] = 'j'
        mem[0x419c47] = '\xc0'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0xb6000000b4000000b2000000b0)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419c43

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c43, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c44, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c45, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c46, 8)== ord('j'))
        condition = Operators.AND(condition, cpu.read_int(0x419c47, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.XMM0 == 0xb600000000000000b4)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419c48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHDQ_6_symbolic(self):
        ''' Instruction PUNPCKHDQ_6 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c43] = 'f'
        mem[0x419c44] = 'A'
        mem[0x419c45] = '\x0f'
        mem[0x419c46] = 'j'
        mem[0x419c47] = '\xc0'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0xae000000ac000000aa000000a8)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419c43

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c43, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c44, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c45, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c46, 8)== ord('j'))
        condition = Operators.AND(condition, cpu.read_int(0x419c47, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.XMM0 == 0xae00000000000000ac)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419c48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHDQ_7_symbolic(self):
        ''' Instruction PUNPCKHDQ_7 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c43] = 'f'
        mem[0x419c44] = 'A'
        mem[0x419c45] = '\x0f'
        mem[0x419c46] = 'j'
        mem[0x419c47] = '\xc0'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0xe0000000c0000000a00000008)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419c43

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c43, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c44, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c45, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c46, 8)== ord('j'))
        condition = Operators.AND(condition, cpu.read_int(0x419c47, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.XMM0 == 0xe000000000000000c)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419c48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHDQ_8_symbolic(self):
        ''' Instruction PUNPCKHDQ_8 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c43] = 'f'
        mem[0x419c44] = 'A'
        mem[0x419c45] = '\x0f'
        mem[0x419c46] = 'j'
        mem[0x419c47] = '\xc0'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x86000000840000008200000080)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419c43

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c43, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c44, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c45, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c46, 8)== ord('j'))
        condition = Operators.AND(condition, cpu.read_int(0x419c47, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x860000000000000084)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419c48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHDQ_9_symbolic(self):
        ''' Instruction PUNPCKHDQ_9 
            Groups: sse2 
            0x419c43:	punpckhdq	xmm0, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c43] = 'f'
        mem[0x419c44] = 'A'
        mem[0x419c45] = '\x0f'
        mem[0x419c46] = 'j'
        mem[0x419c47] = '\xc0'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0xd6000000d4000000d2000000d0)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419c43

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c43, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c44, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c45, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c46, 8)== ord('j'))
        condition = Operators.AND(condition, cpu.read_int(0x419c47, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.XMM0 == 0xd600000000000000d4)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419c48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHQDQ_1_symbolic(self):
        ''' Instruction PUNPCKHQDQ_1 
            Groups: sse2 
            0x419c71:	punpckhqdq	xmm1, xmm1
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c71] = 'f'
        mem[0x419c72] = '\x0f'
        mem[0x419c73] = 'm'
        mem[0x419c74] = '\xc9'
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cbae800000000006cbad8)
        cpu.RIP = 0x419c71

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c71, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c72, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c73, 8)== ord('m'))
        condition = Operators.AND(condition, cpu.read_int(0x419c74, 8)== ord('\xc9'))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cbae800000000006cbae8)
        condition = Operators.AND(condition, cpu.RIP == 0x419c75)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHQDQ_10_symbolic(self):
        ''' Instruction PUNPCKHQDQ_10 
            Groups: sse2 
            0x419c71:	punpckhqdq	xmm1, xmm1
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c71] = 'f'
        mem[0x419c72] = '\x0f'
        mem[0x419c73] = 'm'
        mem[0x419c74] = '\xc9'
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cb8e800000000006cb8d8)
        cpu.RIP = 0x419c71

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c71, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c72, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c73, 8)== ord('m'))
        condition = Operators.AND(condition, cpu.read_int(0x419c74, 8)== ord('\xc9'))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cb8e800000000006cb8e8)
        condition = Operators.AND(condition, cpu.RIP == 0x419c75)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHQDQ_11_symbolic(self):
        ''' Instruction PUNPCKHQDQ_11 
            Groups: sse2 
            0x419c86:	punpckhqdq	xmm0, xmm0
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c88] = 'm'
        mem[0x419c89] = '\xc0'
        mem[0x419c86] = 'f'
        mem[0x419c87] = '\x0f'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6cba8800000000006cba78)
        cpu.RIP = 0x419c86

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c88, 8)== ord('m'))
        condition = Operators.AND(condition, cpu.read_int(0x419c89, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.read_int(0x419c86, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c87, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6cba8800000000006cba88)
        condition = Operators.AND(condition, cpu.RIP == 0x419c8a)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHQDQ_12_symbolic(self):
        ''' Instruction PUNPCKHQDQ_12 
            Groups: sse2 
            0x419c71:	punpckhqdq	xmm1, xmm1
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c71] = 'f'
        mem[0x419c72] = '\x0f'
        mem[0x419c73] = 'm'
        mem[0x419c74] = '\xc9'
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cbaa800000000006cba98)
        cpu.RIP = 0x419c71

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c71, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c72, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c73, 8)== ord('m'))
        condition = Operators.AND(condition, cpu.read_int(0x419c74, 8)== ord('\xc9'))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cbaa800000000006cbaa8)
        condition = Operators.AND(condition, cpu.RIP == 0x419c75)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHQDQ_13_symbolic(self):
        ''' Instruction PUNPCKHQDQ_13 
            Groups: sse2 
            0x419c71:	punpckhqdq	xmm1, xmm1
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c71] = 'f'
        mem[0x419c72] = '\x0f'
        mem[0x419c73] = 'm'
        mem[0x419c74] = '\xc9'
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cbee800000000006cbed8)
        cpu.RIP = 0x419c71

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c71, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c72, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c73, 8)== ord('m'))
        condition = Operators.AND(condition, cpu.read_int(0x419c74, 8)== ord('\xc9'))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cbee800000000006cbee8)
        condition = Operators.AND(condition, cpu.RIP == 0x419c75)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHQDQ_14_symbolic(self):
        ''' Instruction PUNPCKHQDQ_14 
            Groups: sse2 
            0x419c86:	punpckhqdq	xmm0, xmm0
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c88] = 'm'
        mem[0x419c89] = '\xc0'
        mem[0x419c86] = 'f'
        mem[0x419c87] = '\x0f'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6cbf4800000000006cbf38)
        cpu.RIP = 0x419c86

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c88, 8)== ord('m'))
        condition = Operators.AND(condition, cpu.read_int(0x419c89, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.read_int(0x419c86, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c87, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6cbf4800000000006cbf48)
        condition = Operators.AND(condition, cpu.RIP == 0x419c8a)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHQDQ_15_symbolic(self):
        ''' Instruction PUNPCKHQDQ_15 
            Groups: sse2 
            0x419c86:	punpckhqdq	xmm0, xmm0
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c88] = 'm'
        mem[0x419c89] = '\xc0'
        mem[0x419c86] = 'f'
        mem[0x419c87] = '\x0f'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6cbdc800000000006cbdb8)
        cpu.RIP = 0x419c86

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c88, 8)== ord('m'))
        condition = Operators.AND(condition, cpu.read_int(0x419c89, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.read_int(0x419c86, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c87, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6cbdc800000000006cbdc8)
        condition = Operators.AND(condition, cpu.RIP == 0x419c8a)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHQDQ_16_symbolic(self):
        ''' Instruction PUNPCKHQDQ_16 
            Groups: sse2 
            0x419c71:	punpckhqdq	xmm1, xmm1
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c71] = 'f'
        mem[0x419c72] = '\x0f'
        mem[0x419c73] = 'm'
        mem[0x419c74] = '\xc9'
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cb96800000000006cb958)
        cpu.RIP = 0x419c71

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c71, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c72, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c73, 8)== ord('m'))
        condition = Operators.AND(condition, cpu.read_int(0x419c74, 8)== ord('\xc9'))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cb96800000000006cb968)
        condition = Operators.AND(condition, cpu.RIP == 0x419c75)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHQDQ_17_symbolic(self):
        ''' Instruction PUNPCKHQDQ_17 
            Groups: sse2 
            0x419c86:	punpckhqdq	xmm0, xmm0
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c88] = 'm'
        mem[0x419c89] = '\xc0'
        mem[0x419c86] = 'f'
        mem[0x419c87] = '\x0f'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6cbb4800000000006cbb38)
        cpu.RIP = 0x419c86

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c88, 8)== ord('m'))
        condition = Operators.AND(condition, cpu.read_int(0x419c89, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.read_int(0x419c86, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c87, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6cbb4800000000006cbb48)
        condition = Operators.AND(condition, cpu.RIP == 0x419c8a)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHQDQ_18_symbolic(self):
        ''' Instruction PUNPCKHQDQ_18 
            Groups: sse2 
            0x419c86:	punpckhqdq	xmm0, xmm0
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c88] = 'm'
        mem[0x419c89] = '\xc0'
        mem[0x419c86] = 'f'
        mem[0x419c87] = '\x0f'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6cb90800000000006cb8f8)
        cpu.RIP = 0x419c86

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c88, 8)== ord('m'))
        condition = Operators.AND(condition, cpu.read_int(0x419c89, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.read_int(0x419c86, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c87, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6cb90800000000006cb908)
        condition = Operators.AND(condition, cpu.RIP == 0x419c8a)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHQDQ_19_symbolic(self):
        ''' Instruction PUNPCKHQDQ_19 
            Groups: sse2 
            0x419c71:	punpckhqdq	xmm1, xmm1
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c71] = 'f'
        mem[0x419c72] = '\x0f'
        mem[0x419c73] = 'm'
        mem[0x419c74] = '\xc9'
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cbfe800000000006cbfd8)
        cpu.RIP = 0x419c71

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c71, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c72, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c73, 8)== ord('m'))
        condition = Operators.AND(condition, cpu.read_int(0x419c74, 8)== ord('\xc9'))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cbfe800000000006cbfe8)
        condition = Operators.AND(condition, cpu.RIP == 0x419c75)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHQDQ_2_symbolic(self):
        ''' Instruction PUNPCKHQDQ_2 
            Groups: sse2 
            0x419c86:	punpckhqdq	xmm0, xmm0
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c88] = 'm'
        mem[0x419c89] = '\xc0'
        mem[0x419c86] = 'f'
        mem[0x419c87] = '\x0f'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6cb88800000000006cb878)
        cpu.RIP = 0x419c86

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c88, 8)== ord('m'))
        condition = Operators.AND(condition, cpu.read_int(0x419c89, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.read_int(0x419c86, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c87, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6cb88800000000006cb888)
        condition = Operators.AND(condition, cpu.RIP == 0x419c8a)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHQDQ_20_symbolic(self):
        ''' Instruction PUNPCKHQDQ_20 
            Groups: sse2 
            0x419c71:	punpckhqdq	xmm1, xmm1
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c71] = 'f'
        mem[0x419c72] = '\x0f'
        mem[0x419c73] = 'm'
        mem[0x419c74] = '\xc9'
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cb92800000000006cb918)
        cpu.RIP = 0x419c71

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c71, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c72, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c73, 8)== ord('m'))
        condition = Operators.AND(condition, cpu.read_int(0x419c74, 8)== ord('\xc9'))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cb92800000000006cb928)
        condition = Operators.AND(condition, cpu.RIP == 0x419c75)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHQDQ_21_symbolic(self):
        ''' Instruction PUNPCKHQDQ_21 
            Groups: sse2 
            0x419c86:	punpckhqdq	xmm0, xmm0
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c88] = 'm'
        mem[0x419c89] = '\xc0'
        mem[0x419c86] = 'f'
        mem[0x419c87] = '\x0f'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6cbac800000000006cbab8)
        cpu.RIP = 0x419c86

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c88, 8)== ord('m'))
        condition = Operators.AND(condition, cpu.read_int(0x419c89, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.read_int(0x419c86, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c87, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6cbac800000000006cbac8)
        condition = Operators.AND(condition, cpu.RIP == 0x419c8a)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHQDQ_3_symbolic(self):
        ''' Instruction PUNPCKHQDQ_3 
            Groups: sse2 
            0x419c71:	punpckhqdq	xmm1, xmm1
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c71] = 'f'
        mem[0x419c72] = '\x0f'
        mem[0x419c73] = 'm'
        mem[0x419c74] = '\xc9'
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cbbe800000000006cbbd8)
        cpu.RIP = 0x419c71

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c71, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c72, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c73, 8)== ord('m'))
        condition = Operators.AND(condition, cpu.read_int(0x419c74, 8)== ord('\xc9'))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cbbe800000000006cbbe8)
        condition = Operators.AND(condition, cpu.RIP == 0x419c75)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHQDQ_4_symbolic(self):
        ''' Instruction PUNPCKHQDQ_4 
            Groups: sse2 
            0x419c86:	punpckhqdq	xmm0, xmm0
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c88] = 'm'
        mem[0x419c89] = '\xc0'
        mem[0x419c86] = 'f'
        mem[0x419c87] = '\x0f'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6cbd8800000000006cbd78)
        cpu.RIP = 0x419c86

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c88, 8)== ord('m'))
        condition = Operators.AND(condition, cpu.read_int(0x419c89, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.read_int(0x419c86, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c87, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6cbd8800000000006cbd88)
        condition = Operators.AND(condition, cpu.RIP == 0x419c8a)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHQDQ_5_symbolic(self):
        ''' Instruction PUNPCKHQDQ_5 
            Groups: sse2 
            0x419c71:	punpckhqdq	xmm1, xmm1
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c71] = 'f'
        mem[0x419c72] = '\x0f'
        mem[0x419c73] = 'm'
        mem[0x419c74] = '\xc9'
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cb86800000000006cb858)
        cpu.RIP = 0x419c71

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c71, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c72, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c73, 8)== ord('m'))
        condition = Operators.AND(condition, cpu.read_int(0x419c74, 8)== ord('\xc9'))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cb86800000000006cb868)
        condition = Operators.AND(condition, cpu.RIP == 0x419c75)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHQDQ_6_symbolic(self):
        ''' Instruction PUNPCKHQDQ_6 
            Groups: sse2 
            0x419c71:	punpckhqdq	xmm1, xmm1
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c71] = 'f'
        mem[0x419c72] = '\x0f'
        mem[0x419c73] = 'm'
        mem[0x419c74] = '\xc9'
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cbde800000000006cbdd8)
        cpu.RIP = 0x419c71

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c71, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c72, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c73, 8)== ord('m'))
        condition = Operators.AND(condition, cpu.read_int(0x419c74, 8)== ord('\xc9'))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cbde800000000006cbde8)
        condition = Operators.AND(condition, cpu.RIP == 0x419c75)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHQDQ_7_symbolic(self):
        ''' Instruction PUNPCKHQDQ_7 
            Groups: sse2 
            0x419c71:	punpckhqdq	xmm1, xmm1
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c71] = 'f'
        mem[0x419c72] = '\x0f'
        mem[0x419c73] = 'm'
        mem[0x419c74] = '\xc9'
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cbd2800000000006cbd18)
        cpu.RIP = 0x419c71

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c71, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c72, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c73, 8)== ord('m'))
        condition = Operators.AND(condition, cpu.read_int(0x419c74, 8)== ord('\xc9'))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cbd2800000000006cbd28)
        condition = Operators.AND(condition, cpu.RIP == 0x419c75)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHQDQ_8_symbolic(self):
        ''' Instruction PUNPCKHQDQ_8 
            Groups: sse2 
            0x419c71:	punpckhqdq	xmm1, xmm1
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c71] = 'f'
        mem[0x419c72] = '\x0f'
        mem[0x419c73] = 'm'
        mem[0x419c74] = '\xc9'
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cb8a800000000006cb898)
        cpu.RIP = 0x419c71

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c71, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c72, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c73, 8)== ord('m'))
        condition = Operators.AND(condition, cpu.read_int(0x419c74, 8)== ord('\xc9'))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cb8a800000000006cb8a8)
        condition = Operators.AND(condition, cpu.RIP == 0x419c75)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKHQDQ_9_symbolic(self):
        ''' Instruction PUNPCKHQDQ_9 
            Groups: sse2 
            0x419c86:	punpckhqdq	xmm0, xmm0
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c88] = 'm'
        mem[0x419c89] = '\xc0'
        mem[0x419c86] = 'f'
        mem[0x419c87] = '\x0f'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6cb94800000000006cb938)
        cpu.RIP = 0x419c86

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c88, 8)== ord('m'))
        condition = Operators.AND(condition, cpu.read_int(0x419c89, 8)== ord('\xc0'))
        condition = Operators.AND(condition, cpu.read_int(0x419c86, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c87, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6cb94800000000006cb948)
        condition = Operators.AND(condition, cpu.RIP == 0x419c8a)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLBW_1_symbolic(self):
        ''' Instruction PUNPCKLBW_1 
            Groups: sse2 
            0x4668ac:	punpcklbw	xmm1, xmm1
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00466000, 0x1000, 'rwx')
        mem[0x4668ac] = 'f'
        mem[0x4668ad] = '\x0f'
        mem[0x4668ae] = '`'
        mem[0x4668af] = '\xc9'
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x2f)
        cpu.RIP = 0x4668ac

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x4668ac, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x4668ad, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x4668ae, 8)== ord('`'))
        condition = Operators.AND(condition, cpu.read_int(0x4668af, 8)== ord('\xc9'))
        condition = Operators.AND(condition, cpu.XMM1 == 0x2f2f)
        condition = Operators.AND(condition, cpu.RIP == 0x4668b0)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLDQ_1_symbolic(self):
        ''' Instruction PUNPCKLDQ_1 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c48] = 'f'
        mem[0x419c49] = 'A'
        mem[0x419c4a] = '\x0f'
        mem[0x419c4b] = 'b'
        mem[0x419c4c] = '\xc8'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xa6000000a4000000a2000000a0)
        cpu.RIP = 0x419c48

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c48, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c49, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4a, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4b, 8)== ord('b'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4c, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0xa200000000000000a0)
        condition = Operators.AND(condition, cpu.RIP == 0x419c4d)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLDQ_10_symbolic(self):
        ''' Instruction PUNPCKLDQ_10 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c48] = 'f'
        mem[0x419c49] = 'A'
        mem[0x419c4a] = '\x0f'
        mem[0x419c4b] = 'b'
        mem[0x419c4c] = '\xc8'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x3e0000003c0000003a00000038)
        cpu.RIP = 0x419c48

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c48, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c49, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4a, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4b, 8)== ord('b'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4c, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0x3a0000000000000038)
        condition = Operators.AND(condition, cpu.RIP == 0x419c4d)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLDQ_11_symbolic(self):
        ''' Instruction PUNPCKLDQ_11 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c48] = 'f'
        mem[0x419c49] = 'A'
        mem[0x419c4a] = '\x0f'
        mem[0x419c4b] = 'b'
        mem[0x419c4c] = '\xc8'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6000000040000000200000000)
        cpu.RIP = 0x419c48

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c48, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c49, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4a, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4b, 8)== ord('b'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4c, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0x20000000000000000)
        condition = Operators.AND(condition, cpu.RIP == 0x419c4d)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLDQ_12_symbolic(self):
        ''' Instruction PUNPCKLDQ_12 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c48] = 'f'
        mem[0x419c49] = 'A'
        mem[0x419c4a] = '\x0f'
        mem[0x419c4b] = 'b'
        mem[0x419c4c] = '\xc8'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x1e0000001c0000001a00000018)
        cpu.RIP = 0x419c48

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c48, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c49, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4a, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4b, 8)== ord('b'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4c, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0x1a0000000000000018)
        condition = Operators.AND(condition, cpu.RIP == 0x419c4d)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLDQ_13_symbolic(self):
        ''' Instruction PUNPCKLDQ_13 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c48] = 'f'
        mem[0x419c49] = 'A'
        mem[0x419c4a] = '\x0f'
        mem[0x419c4b] = 'b'
        mem[0x419c4c] = '\xc8'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xe0000000c0000000a00000008)
        cpu.RIP = 0x419c48

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c48, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c49, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4a, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4b, 8)== ord('b'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4c, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0xa0000000000000008)
        condition = Operators.AND(condition, cpu.RIP == 0x419c4d)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLDQ_14_symbolic(self):
        ''' Instruction PUNPCKLDQ_14 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c48] = 'f'
        mem[0x419c49] = 'A'
        mem[0x419c4a] = '\x0f'
        mem[0x419c4b] = 'b'
        mem[0x419c4c] = '\xc8'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xee000000ec000000ea000000e8)
        cpu.RIP = 0x419c48

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c48, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c49, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4a, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4b, 8)== ord('b'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4c, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0xea00000000000000e8)
        condition = Operators.AND(condition, cpu.RIP == 0x419c4d)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLDQ_15_symbolic(self):
        ''' Instruction PUNPCKLDQ_15 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c48] = 'f'
        mem[0x419c49] = 'A'
        mem[0x419c4a] = '\x0f'
        mem[0x419c4b] = 'b'
        mem[0x419c4c] = '\xc8'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x2e0000002c0000002a00000028)
        cpu.RIP = 0x419c48

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c48, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c49, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4a, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4b, 8)== ord('b'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4c, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0x2a0000000000000028)
        condition = Operators.AND(condition, cpu.RIP == 0x419c4d)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLDQ_16_symbolic(self):
        ''' Instruction PUNPCKLDQ_16 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c48] = 'f'
        mem[0x419c49] = 'A'
        mem[0x419c4a] = '\x0f'
        mem[0x419c4b] = 'b'
        mem[0x419c4c] = '\xc8'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xf6000000f4000000f2000000f0)
        cpu.RIP = 0x419c48

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c48, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c49, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4a, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4b, 8)== ord('b'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4c, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0xf200000000000000f0)
        condition = Operators.AND(condition, cpu.RIP == 0x419c4d)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLDQ_17_symbolic(self):
        ''' Instruction PUNPCKLDQ_17 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c48] = 'f'
        mem[0x419c49] = 'A'
        mem[0x419c4a] = '\x0f'
        mem[0x419c4b] = 'b'
        mem[0x419c4c] = '\xc8'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x9e0000009c0000009a00000098)
        cpu.RIP = 0x419c48

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c48, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c49, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4a, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4b, 8)== ord('b'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4c, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0x9a0000000000000098)
        condition = Operators.AND(condition, cpu.RIP == 0x419c4d)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLDQ_18_symbolic(self):
        ''' Instruction PUNPCKLDQ_18 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c48] = 'f'
        mem[0x419c49] = 'A'
        mem[0x419c4a] = '\x0f'
        mem[0x419c4b] = 'b'
        mem[0x419c4c] = '\xc8'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x16000000140000001200000010)
        cpu.RIP = 0x419c48

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c48, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c49, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4a, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4b, 8)== ord('b'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4c, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0x120000000000000010)
        condition = Operators.AND(condition, cpu.RIP == 0x419c4d)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLDQ_19_symbolic(self):
        ''' Instruction PUNPCKLDQ_19 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c48] = 'f'
        mem[0x419c49] = 'A'
        mem[0x419c4a] = '\x0f'
        mem[0x419c4b] = 'b'
        mem[0x419c4c] = '\xc8'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x96000000940000009200000090)
        cpu.RIP = 0x419c48

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c48, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c49, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4a, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4b, 8)== ord('b'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4c, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0x920000000000000090)
        condition = Operators.AND(condition, cpu.RIP == 0x419c4d)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLDQ_2_symbolic(self):
        ''' Instruction PUNPCKLDQ_2 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c48] = 'f'
        mem[0x419c49] = 'A'
        mem[0x419c4a] = '\x0f'
        mem[0x419c4b] = 'b'
        mem[0x419c4c] = '\xc8'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x76000000740000007200000070)
        cpu.RIP = 0x419c48

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c48, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c49, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4a, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4b, 8)== ord('b'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4c, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0x720000000000000070)
        condition = Operators.AND(condition, cpu.RIP == 0x419c4d)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLDQ_20_symbolic(self):
        ''' Instruction PUNPCKLDQ_20 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c48] = 'f'
        mem[0x419c49] = 'A'
        mem[0x419c4a] = '\x0f'
        mem[0x419c4b] = 'b'
        mem[0x419c4c] = '\xc8'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xde000000dc000000da000000d8)
        cpu.RIP = 0x419c48

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c48, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c49, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4a, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4b, 8)== ord('b'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4c, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0xda00000000000000d8)
        condition = Operators.AND(condition, cpu.RIP == 0x419c4d)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLDQ_21_symbolic(self):
        ''' Instruction PUNPCKLDQ_21 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c48] = 'f'
        mem[0x419c49] = 'A'
        mem[0x419c4a] = '\x0f'
        mem[0x419c4b] = 'b'
        mem[0x419c4c] = '\xc8'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xe6000000e4000000e2000000e0)
        cpu.RIP = 0x419c48

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c48, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c49, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4a, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4b, 8)== ord('b'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4c, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0xe200000000000000e0)
        condition = Operators.AND(condition, cpu.RIP == 0x419c4d)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLDQ_3_symbolic(self):
        ''' Instruction PUNPCKLDQ_3 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c48] = 'f'
        mem[0x419c49] = 'A'
        mem[0x419c4a] = '\x0f'
        mem[0x419c4b] = 'b'
        mem[0x419c4c] = '\xc8'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x36000000340000003200000030)
        cpu.RIP = 0x419c48

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c48, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c49, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4a, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4b, 8)== ord('b'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4c, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0x320000000000000030)
        condition = Operators.AND(condition, cpu.RIP == 0x419c4d)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLDQ_4_symbolic(self):
        ''' Instruction PUNPCKLDQ_4 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c48] = 'f'
        mem[0x419c49] = 'A'
        mem[0x419c4a] = '\x0f'
        mem[0x419c4b] = 'b'
        mem[0x419c4c] = '\xc8'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6e0000006c0000006a00000068)
        cpu.RIP = 0x419c48

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c48, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c49, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4a, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4b, 8)== ord('b'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4c, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6a0000000000000068)
        condition = Operators.AND(condition, cpu.RIP == 0x419c4d)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLDQ_5_symbolic(self):
        ''' Instruction PUNPCKLDQ_5 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c48] = 'f'
        mem[0x419c49] = 'A'
        mem[0x419c4a] = '\x0f'
        mem[0x419c4b] = 'b'
        mem[0x419c4c] = '\xc8'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x7e0000007c0000007a00000078)
        cpu.RIP = 0x419c48

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c48, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c49, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4a, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4b, 8)== ord('b'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4c, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0x7a0000000000000078)
        condition = Operators.AND(condition, cpu.RIP == 0x419c4d)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLDQ_6_symbolic(self):
        ''' Instruction PUNPCKLDQ_6 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c48] = 'f'
        mem[0x419c49] = 'A'
        mem[0x419c4a] = '\x0f'
        mem[0x419c4b] = 'b'
        mem[0x419c4c] = '\xc8'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x26000000240000002200000020)
        cpu.RIP = 0x419c48

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c48, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c49, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4a, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4b, 8)== ord('b'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4c, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0x220000000000000020)
        condition = Operators.AND(condition, cpu.RIP == 0x419c4d)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLDQ_7_symbolic(self):
        ''' Instruction PUNPCKLDQ_7 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c48] = 'f'
        mem[0x419c49] = 'A'
        mem[0x419c4a] = '\x0f'
        mem[0x419c4b] = 'b'
        mem[0x419c4c] = '\xc8'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xbe000000bc000000ba000000b8)
        cpu.RIP = 0x419c48

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c48, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c49, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4a, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4b, 8)== ord('b'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4c, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0xba00000000000000b8)
        condition = Operators.AND(condition, cpu.RIP == 0x419c4d)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLDQ_8_symbolic(self):
        ''' Instruction PUNPCKLDQ_8 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c48] = 'f'
        mem[0x419c49] = 'A'
        mem[0x419c4a] = '\x0f'
        mem[0x419c4b] = 'b'
        mem[0x419c4c] = '\xc8'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xce000000cc000000ca000000c8)
        cpu.RIP = 0x419c48

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c48, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c49, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4a, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4b, 8)== ord('b'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4c, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0xca00000000000000c8)
        condition = Operators.AND(condition, cpu.RIP == 0x419c4d)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLDQ_9_symbolic(self):
        ''' Instruction PUNPCKLDQ_9 
            Groups: sse2 
            0x419c48:	punpckldq	xmm1, xmm8
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c48] = 'f'
        mem[0x419c49] = 'A'
        mem[0x419c4a] = '\x0f'
        mem[0x419c4b] = 'b'
        mem[0x419c4c] = '\xc8'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x46000000440000004200000040)
        cpu.RIP = 0x419c48

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c48, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c49, 8)== ord('A'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4a, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4b, 8)== ord('b'))
        condition = Operators.AND(condition, cpu.read_int(0x419c4c, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0x420000000000000040)
        condition = Operators.AND(condition, cpu.RIP == 0x419c4d)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLQDQ_1_symbolic(self):
        ''' Instruction PUNPCKLQDQ_1 
            Groups: sse2 
            0x419c82:	punpcklqdq	xmm1, xmm0
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c82] = 'f'
        mem[0x419c83] = '\x0f'
        mem[0x419c84] = 'l'
        mem[0x419c85] = '\xc8'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6cbfc800000000006cbfb8)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cbfc800000000006cbfb8)
        cpu.RIP = 0x419c82

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c82, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c83, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c84, 8)== ord('l'))
        condition = Operators.AND(condition, cpu.read_int(0x419c85, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6cbfc800000000006cbfb8)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cbfb800000000006cbfb8)
        condition = Operators.AND(condition, cpu.RIP == 0x419c86)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLQDQ_10_symbolic(self):
        ''' Instruction PUNPCKLQDQ_10 
            Groups: sse2 
            0x419c6c:	punpcklqdq	xmm8, xmm1
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c70] = '\xc1'
        mem[0x419c6c] = 'f'
        mem[0x419c6d] = 'D'
        mem[0x419c6e] = '\x0f'
        mem[0x419c6f] = 'l'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x6cbc6800000000006cbc58)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cbc6800000000006cbc58)
        cpu.RIP = 0x419c6c

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c70, 8)== ord('\xc1'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6c, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6d, 8)== ord('D'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6e, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6f, 8)== ord('l'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x6cbc5800000000006cbc58)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cbc6800000000006cbc58)
        condition = Operators.AND(condition, cpu.RIP == 0x419c71)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLQDQ_11_symbolic(self):
        ''' Instruction PUNPCKLQDQ_11 
            Groups: sse2 
            0x419c82:	punpcklqdq	xmm1, xmm0
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c82] = 'f'
        mem[0x419c83] = '\x0f'
        mem[0x419c84] = 'l'
        mem[0x419c85] = '\xc8'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6cbb4800000000006cbb38)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cbb4800000000006cbb38)
        cpu.RIP = 0x419c82

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c82, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c83, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c84, 8)== ord('l'))
        condition = Operators.AND(condition, cpu.read_int(0x419c85, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6cbb4800000000006cbb38)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cbb3800000000006cbb38)
        condition = Operators.AND(condition, cpu.RIP == 0x419c86)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLQDQ_12_symbolic(self):
        ''' Instruction PUNPCKLQDQ_12 
            Groups: sse2 
            0x419c6c:	punpcklqdq	xmm8, xmm1
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c70] = '\xc1'
        mem[0x419c6c] = 'f'
        mem[0x419c6d] = 'D'
        mem[0x419c6e] = '\x0f'
        mem[0x419c6f] = 'l'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x6cbde800000000006cbdd8)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cbde800000000006cbdd8)
        cpu.RIP = 0x419c6c

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c70, 8)== ord('\xc1'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6c, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6d, 8)== ord('D'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6e, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6f, 8)== ord('l'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x6cbdd800000000006cbdd8)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cbde800000000006cbdd8)
        condition = Operators.AND(condition, cpu.RIP == 0x419c71)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLQDQ_13_symbolic(self):
        ''' Instruction PUNPCKLQDQ_13 
            Groups: sse2 
            0x419c6c:	punpcklqdq	xmm8, xmm1
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c70] = '\xc1'
        mem[0x419c6c] = 'f'
        mem[0x419c6d] = 'D'
        mem[0x419c6e] = '\x0f'
        mem[0x419c6f] = 'l'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x6cbee800000000006cbed8)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cbee800000000006cbed8)
        cpu.RIP = 0x419c6c

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c70, 8)== ord('\xc1'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6c, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6d, 8)== ord('D'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6e, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6f, 8)== ord('l'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x6cbed800000000006cbed8)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cbee800000000006cbed8)
        condition = Operators.AND(condition, cpu.RIP == 0x419c71)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLQDQ_14_symbolic(self):
        ''' Instruction PUNPCKLQDQ_14 
            Groups: sse2 
            0x419c6c:	punpcklqdq	xmm8, xmm1
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c70] = '\xc1'
        mem[0x419c6c] = 'f'
        mem[0x419c6d] = 'D'
        mem[0x419c6e] = '\x0f'
        mem[0x419c6f] = 'l'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x6cbba800000000006cbb98)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cbba800000000006cbb98)
        cpu.RIP = 0x419c6c

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c70, 8)== ord('\xc1'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6c, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6d, 8)== ord('D'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6e, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6f, 8)== ord('l'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x6cbb9800000000006cbb98)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cbba800000000006cbb98)
        condition = Operators.AND(condition, cpu.RIP == 0x419c71)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLQDQ_15_symbolic(self):
        ''' Instruction PUNPCKLQDQ_15 
            Groups: sse2 
            0x419c82:	punpcklqdq	xmm1, xmm0
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c82] = 'f'
        mem[0x419c83] = '\x0f'
        mem[0x419c84] = 'l'
        mem[0x419c85] = '\xc8'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6cbcc800000000006cbcb8)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cbcc800000000006cbcb8)
        cpu.RIP = 0x419c82

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c82, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c83, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c84, 8)== ord('l'))
        condition = Operators.AND(condition, cpu.read_int(0x419c85, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6cbcc800000000006cbcb8)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cbcb800000000006cbcb8)
        condition = Operators.AND(condition, cpu.RIP == 0x419c86)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLQDQ_16_symbolic(self):
        ''' Instruction PUNPCKLQDQ_16 
            Groups: sse2 
            0x419c82:	punpcklqdq	xmm1, xmm0
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c82] = 'f'
        mem[0x419c83] = '\x0f'
        mem[0x419c84] = 'l'
        mem[0x419c85] = '\xc8'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6cbe0800000000006cbdf8)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cbe0800000000006cbdf8)
        cpu.RIP = 0x419c82

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c82, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c83, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c84, 8)== ord('l'))
        condition = Operators.AND(condition, cpu.read_int(0x419c85, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6cbe0800000000006cbdf8)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cbdf800000000006cbdf8)
        condition = Operators.AND(condition, cpu.RIP == 0x419c86)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLQDQ_17_symbolic(self):
        ''' Instruction PUNPCKLQDQ_17 
            Groups: sse2 
            0x419c82:	punpcklqdq	xmm1, xmm0
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c82] = 'f'
        mem[0x419c83] = '\x0f'
        mem[0x419c84] = 'l'
        mem[0x419c85] = '\xc8'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6cbec800000000006cbeb8)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cbec800000000006cbeb8)
        cpu.RIP = 0x419c82

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c82, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c83, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c84, 8)== ord('l'))
        condition = Operators.AND(condition, cpu.read_int(0x419c85, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6cbec800000000006cbeb8)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cbeb800000000006cbeb8)
        condition = Operators.AND(condition, cpu.RIP == 0x419c86)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLQDQ_18_symbolic(self):
        ''' Instruction PUNPCKLQDQ_18 
            Groups: sse2 
            0x419c6c:	punpcklqdq	xmm8, xmm1
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c70] = '\xc1'
        mem[0x419c6c] = 'f'
        mem[0x419c6d] = 'D'
        mem[0x419c6e] = '\x0f'
        mem[0x419c6f] = 'l'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x6cbbe800000000006cbbd8)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cbbe800000000006cbbd8)
        cpu.RIP = 0x419c6c

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c70, 8)== ord('\xc1'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6c, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6d, 8)== ord('D'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6e, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6f, 8)== ord('l'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x6cbbd800000000006cbbd8)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cbbe800000000006cbbd8)
        condition = Operators.AND(condition, cpu.RIP == 0x419c71)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLQDQ_19_symbolic(self):
        ''' Instruction PUNPCKLQDQ_19 
            Groups: sse2 
            0x419c82:	punpcklqdq	xmm1, xmm0
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c82] = 'f'
        mem[0x419c83] = '\x0f'
        mem[0x419c84] = 'l'
        mem[0x419c85] = '\xc8'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6cbc8800000000006cbc78)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cbc8800000000006cbc78)
        cpu.RIP = 0x419c82

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c82, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c83, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c84, 8)== ord('l'))
        condition = Operators.AND(condition, cpu.read_int(0x419c85, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6cbc8800000000006cbc78)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cbc7800000000006cbc78)
        condition = Operators.AND(condition, cpu.RIP == 0x419c86)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLQDQ_2_symbolic(self):
        ''' Instruction PUNPCKLQDQ_2 
            Groups: sse2 
            0x419c6c:	punpcklqdq	xmm8, xmm1
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c70] = '\xc1'
        mem[0x419c6c] = 'f'
        mem[0x419c6d] = 'D'
        mem[0x419c6e] = '\x0f'
        mem[0x419c6f] = 'l'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x6cbf6800000000006cbf58)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cbf6800000000006cbf58)
        cpu.RIP = 0x419c6c

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c70, 8)== ord('\xc1'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6c, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6d, 8)== ord('D'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6e, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6f, 8)== ord('l'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x6cbf5800000000006cbf58)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cbf6800000000006cbf58)
        condition = Operators.AND(condition, cpu.RIP == 0x419c71)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLQDQ_20_symbolic(self):
        ''' Instruction PUNPCKLQDQ_20 
            Groups: sse2 
            0x419c82:	punpcklqdq	xmm1, xmm0
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c82] = 'f'
        mem[0x419c83] = '\x0f'
        mem[0x419c84] = 'l'
        mem[0x419c85] = '\xc8'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6cba8800000000006cba78)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cba8800000000006cba78)
        cpu.RIP = 0x419c82

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c82, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c83, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c84, 8)== ord('l'))
        condition = Operators.AND(condition, cpu.read_int(0x419c85, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6cba8800000000006cba78)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cba7800000000006cba78)
        condition = Operators.AND(condition, cpu.RIP == 0x419c86)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLQDQ_21_symbolic(self):
        ''' Instruction PUNPCKLQDQ_21 
            Groups: sse2 
            0x419c6c:	punpcklqdq	xmm8, xmm1
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c70] = '\xc1'
        mem[0x419c6c] = 'f'
        mem[0x419c6d] = 'D'
        mem[0x419c6e] = '\x0f'
        mem[0x419c6f] = 'l'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x6cb96800000000006cb958)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cb96800000000006cb958)
        cpu.RIP = 0x419c6c

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c70, 8)== ord('\xc1'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6c, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6d, 8)== ord('D'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6e, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6f, 8)== ord('l'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x6cb95800000000006cb958)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cb96800000000006cb958)
        condition = Operators.AND(condition, cpu.RIP == 0x419c71)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLQDQ_3_symbolic(self):
        ''' Instruction PUNPCKLQDQ_3 
            Groups: sse2 
            0x419c6c:	punpcklqdq	xmm8, xmm1
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c70] = '\xc1'
        mem[0x419c6c] = 'f'
        mem[0x419c6d] = 'D'
        mem[0x419c6e] = '\x0f'
        mem[0x419c6f] = 'l'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x6cbb2800000000006cbb18)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cbb2800000000006cbb18)
        cpu.RIP = 0x419c6c

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c70, 8)== ord('\xc1'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6c, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6d, 8)== ord('D'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6e, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6f, 8)== ord('l'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x6cbb1800000000006cbb18)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cbb2800000000006cbb18)
        condition = Operators.AND(condition, cpu.RIP == 0x419c71)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLQDQ_4_symbolic(self):
        ''' Instruction PUNPCKLQDQ_4 
            Groups: sse2 
            0x419c6c:	punpcklqdq	xmm8, xmm1
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c70] = '\xc1'
        mem[0x419c6c] = 'f'
        mem[0x419c6d] = 'D'
        mem[0x419c6e] = '\x0f'
        mem[0x419c6f] = 'l'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x6cb8a800000000006cb898)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cb8a800000000006cb898)
        cpu.RIP = 0x419c6c

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c70, 8)== ord('\xc1'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6c, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6d, 8)== ord('D'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6e, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6f, 8)== ord('l'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x6cb89800000000006cb898)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cb8a800000000006cb898)
        condition = Operators.AND(condition, cpu.RIP == 0x419c71)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLQDQ_5_symbolic(self):
        ''' Instruction PUNPCKLQDQ_5 
            Groups: sse2 
            0x419c6c:	punpcklqdq	xmm8, xmm1
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c70] = '\xc1'
        mem[0x419c6c] = 'f'
        mem[0x419c6d] = 'D'
        mem[0x419c6e] = '\x0f'
        mem[0x419c6f] = 'l'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x6cbc2800000000006cbc18)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cbc2800000000006cbc18)
        cpu.RIP = 0x419c6c

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c70, 8)== ord('\xc1'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6c, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6d, 8)== ord('D'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6e, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6f, 8)== ord('l'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x6cbc1800000000006cbc18)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cbc2800000000006cbc18)
        condition = Operators.AND(condition, cpu.RIP == 0x419c71)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLQDQ_6_symbolic(self):
        ''' Instruction PUNPCKLQDQ_6 
            Groups: sse2 
            0x419c82:	punpcklqdq	xmm1, xmm0
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c82] = 'f'
        mem[0x419c83] = '\x0f'
        mem[0x419c84] = 'l'
        mem[0x419c85] = '\xc8'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6cbf4800000000006cbf38)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cbf4800000000006cbf38)
        cpu.RIP = 0x419c82

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c82, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c83, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c84, 8)== ord('l'))
        condition = Operators.AND(condition, cpu.read_int(0x419c85, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6cbf4800000000006cbf38)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cbf3800000000006cbf38)
        condition = Operators.AND(condition, cpu.RIP == 0x419c86)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLQDQ_7_symbolic(self):
        ''' Instruction PUNPCKLQDQ_7 
            Groups: sse2 
            0x419c6c:	punpcklqdq	xmm8, xmm1
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c70] = '\xc1'
        mem[0x419c6c] = 'f'
        mem[0x419c6d] = 'D'
        mem[0x419c6e] = '\x0f'
        mem[0x419c6f] = 'l'
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x6cba6800000000006cba58)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cba6800000000006cba58)
        cpu.RIP = 0x419c6c

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c70, 8)== ord('\xc1'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6c, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6d, 8)== ord('D'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6e, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c6f, 8)== ord('l'))
        condition = Operators.AND(condition, cpu.XMM8 == 0x6cba5800000000006cba58)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cba6800000000006cba58)
        condition = Operators.AND(condition, cpu.RIP == 0x419c71)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLQDQ_8_symbolic(self):
        ''' Instruction PUNPCKLQDQ_8 
            Groups: sse2 
            0x419c82:	punpcklqdq	xmm1, xmm0
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c82] = 'f'
        mem[0x419c83] = '\x0f'
        mem[0x419c84] = 'l'
        mem[0x419c85] = '\xc8'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6cba0800000000006cb9f8)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cba0800000000006cb9f8)
        cpu.RIP = 0x419c82

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c82, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c83, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c84, 8)== ord('l'))
        condition = Operators.AND(condition, cpu.read_int(0x419c85, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6cba0800000000006cb9f8)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cb9f800000000006cb9f8)
        condition = Operators.AND(condition, cpu.RIP == 0x419c86)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLQDQ_9_symbolic(self):
        ''' Instruction PUNPCKLQDQ_9 
            Groups: sse2 
            0x419c82:	punpcklqdq	xmm1, xmm0
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, 'rwx')
        mem[0x419c82] = 'f'
        mem[0x419c83] = '\x0f'
        mem[0x419c84] = 'l'
        mem[0x419c85] = '\xc8'
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6cbdc800000000006cbdb8)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6cbdc800000000006cbdb8)
        cpu.RIP = 0x419c82

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x419c82, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c83, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.read_int(0x419c84, 8)== ord('l'))
        condition = Operators.AND(condition, cpu.read_int(0x419c85, 8)== ord('\xc8'))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6cbdc800000000006cbdb8)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6cbdb800000000006cbdb8)
        condition = Operators.AND(condition, cpu.RIP == 0x419c86)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_PUNPCKLWD_1_symbolic(self):
        ''' Instruction PUNPCKLWD_1 
            Groups: sse2 
            0x4668b6:	punpcklwd	xmm1, xmm1
        '''
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00466000, 0x1000, 'rwx')
        mem[0x4668b8] = 'a'
        mem[0x4668b9] = '\xc9'
        mem[0x4668b6] = 'f'
        mem[0x4668b7] = '\x0f'
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x2f2f)
        cpu.RIP = 0x4668b6

        done = False
        while not done:
            try:
                cpu.execute()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.read_int(0x4668b8, 8)== ord('a'))
        condition = Operators.AND(condition, cpu.read_int(0x4668b9, 8)== ord('\xc9'))
        condition = Operators.AND(condition, cpu.read_int(0x4668b6, 8)== ord('f'))
        condition = Operators.AND(condition, cpu.read_int(0x4668b7, 8)== ord('\x0f'))
        condition = Operators.AND(condition, cpu.XMM1 == 0x2f2f2f2f)
        condition = Operators.AND(condition, cpu.RIP == 0x4668ba)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

          

if __name__ == '__main__':
    unittest.main()

