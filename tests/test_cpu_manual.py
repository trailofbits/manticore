import struct
import unittest
from manticore.core.cpu.x86 import *
from manticore.core.smtlib import Operators
from manticore.core.memory import *
import mockmem

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

sizes = {'RAX': 64, 'EAX': 32, 'AX': 16, 'AL': 8, 'AH': 8, 'RCX': 64, 'ECX': 32, 'CX': 16, 'CL': 8, 'CH': 8, 'RDX': 64, 'EDX': 32, 'DX': 16, 'DL': 8, 'DH': 8, 'RBX': 64, 'EBX': 32, 'BX': 16, 'BL': 8, 'BH': 8, 'RSP': 64, 'ESP': 32, 'SP': 16, 'SPL': 8, 'RBP': 64, 'EBP': 32, 'BP': 16, 'BPL': 8, 'RSI': 64, 'ESI': 32, 'SI': 16, 'SIL': 8, 'RDI': 64, 'EDI': 32, 'DI': 16, 'DIL': 8, 'R8': 64, 'R8D': 32, 'R8W': 16, 'R8B': 8, 'R9': 64, 'R9D': 32, 'R9W': 16, 'R9B': 8, 'R10': 64, 'R10D': 32, 'R10W': 16, 'R10B': 8, 'R11': 64, 'R11D': 32, 'R11W': 16, 'R11B': 8, 'R12': 64, 'R12D': 32, 'R12W': 16, 'R12B': 8, 'R13': 64, 'R13D': 32, 'R13W': 16, 'R13B': 8, 'R14': 64, 'R14D': 32, 'R14W': 16, 'R14B': 8, 'R15': 64, 'R15D': 32, 'R15W': 16, 'R15B': 8, 'ES': 16, 'CS': 16, 'SS': 16, 'DS': 16, 'FS': 16, 'GS': 16, 'RIP': 64, 'EIP':32, 'IP': 16, 'RFLAGS': 64, 'EFLAGS': 32, 'FLAGS': 16, 'XMM0': 128, 'XMM1': 128, 'XMM2': 128, 'XMM3': 128, 'XMM4': 128, 'XMM5': 128, 'XMM6': 128, 'XMM7': 128, 'XMM8': 128, 'XMM9': 128, 'XMM10': 128, 'XMM11': 128, 'XMM12': 128, 'XMM13': 128, 'XMM14': 128, 'XMM15': 128, 'YMM0': 256, 'YMM1': 256, 'YMM2': 256, 'YMM3': 256, 'YMM4': 256, 'YMM5': 256, 'YMM6': 256, 'YMM7': 256, 'YMM8': 256, 'YMM9': 256, 'YMM10': 256, 'YMM11': 256, 'YMM12': 256, 'YMM13': 256, 'YMM14': 256, 'YMM15': 256}

class SymCPUTest(unittest.TestCase):
    _flag_offsets = {
        'CF': 0,
        'PF': 2,
        'AF': 4,
        'ZF': 6,
        'SF': 7,
        'IF': 9,
        'DF': 10,
        'OF': 11,
    }

    _flags={
        'CF': 0x00001,
        'PF': 0x00004,
        'AF': 0x00010,
        'ZF': 0x00040,
        'SF': 0x00080,
        'DF': 0x00400,
        'OF': 0x00800,
        'IF': 0x00200,}
    
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

    def setUp(self):
        mem = mockmem.Memory()
        self.cpu = I386Cpu(mem) #TODO reset cpu in between tests...
                    #TODO mock getchar/putchar in case the instructon access memory directly
    def tearDown(self):
        self.cpu = None
    def testInitialRegState(self):
        cpu = self.cpu
        #'CR0', 'CR1', 'CR2', 'CR3', 'CR4', 'CR5', 'CR6', 'CR7', 'CR8',
        # 'DR0', 'DR1', 'DR2', 'DR3', 'DR4', 'DR5', 'DR6', 'DR7',
        #'MM0', 'MM1', 'MM2', 'MM3', 'MM4', 'MM5', 'MM6', 'MM7',
        #  'ST0', 'ST1', 'ST2', 'ST3', 'ST4', 'ST5', 'ST6', 'ST7'

        values = {
                  'RFLAGS':          0x0,
                  'TOP':            0x7,
                  'FP0':            (0,0),
                  'FP1':            (0,0),
                  'FP2':            (0,0),
                  'FP3':            (0,0),
                  'FP4':            (0,0),
                  'FP5':            (0,0),
                  'FP6':            (0,0),
                  'FP7':            (0,0),
                  'CS':             0x0,
                  'SS':             0x0,
                  'DS':             0x0,
                  'ES':             0x0}

        for reg_name in cpu.canonical_registers:
            if len(reg_name) > 2:
                v = values.get(reg_name, 0)
                self.assertEqual(cpu.read_register(reg_name),v)

    def testRegisterCacheAccess(self):
        cpu = self.cpu
        cpu.ESI = 0x12345678
        self.assertEqual(cpu.ESI, 0x12345678)
        cpu.SI = 0xAAAA
        self.assertEqual(cpu.SI, 0xAAAA)

        
        cpu.RAX = 0x12345678aabbccdd
        self.assertEqual(cpu.ESI, 0x1234AAAA)
        cpu.SI = 0xAAAA
        self.assertEqual(cpu.SI, 0xAAAA)




    def testFlagAccess(self):

        cpu = self.cpu
        cpu.RFLAGS = 0
        self.assertFalse(cpu.CF)
        self.assertFalse(cpu.PF)
        self.assertFalse(cpu.AF)
        self.assertFalse(cpu.ZF)
        self.assertFalse(cpu.SF)
        self.assertFalse(cpu.DF)
        self.assertFalse(cpu.OF)

        #flag to register CF
        cpu.CF = True
        self.assertTrue( cpu.RFLAGS&self._flags['CF'] !=0)
        cpu.CF = False
        self.assertTrue( cpu.RFLAGS&self._flags['CF'] ==0)

        #register to flag CF
        cpu.RFLAGS |= self._flags['CF']
        self.assertTrue(cpu.CF)
        cpu.RFLAGS &= ~self._flags['CF']
        self.assertFalse(cpu.CF)

        #flag to register PF
        cpu.PF = True
        self.assertTrue( cpu.RFLAGS&self._flags['PF'] !=0)
        cpu.PF = False
        self.assertTrue( cpu.RFLAGS&self._flags['PF'] ==0)

        #register to flag PF
        cpu.RFLAGS |= self._flags['PF']
        self.assertTrue(cpu.PF)
        cpu.RFLAGS &= ~self._flags['PF']
        self.assertFalse(cpu.PF)

        #flag to register AF
        cpu.AF = True
        self.assertTrue( cpu.RFLAGS&self._flags['AF'] !=0)
        cpu.AF = False
        self.assertTrue( cpu.RFLAGS&self._flags['AF'] ==0)

        #register to flag AF
        cpu.RFLAGS |= self._flags['AF']
        self.assertTrue(cpu.AF)
        cpu.RFLAGS &= ~self._flags['AF']
        self.assertFalse(cpu.AF)

        #flag to register ZF
        cpu.ZF = True
        self.assertTrue( (cpu.RFLAGS&self._flags['ZF']) !=0)
        cpu.ZF = False
        self.assertTrue( cpu.RFLAGS&self._flags['ZF'] ==0)

        #register to flag ZF
        cpu.RFLAGS |= self._flags['ZF']
        self.assertTrue(cpu.ZF)
        cpu.RFLAGS &= ~self._flags['ZF']
        self.assertFalse(cpu.ZF)

        #flag to register SF
        cpu.SF = True
        self.assertTrue( cpu.RFLAGS&self._flags['SF'] !=0)
        cpu.SF = False
        self.assertTrue( cpu.RFLAGS&self._flags['SF'] ==0)

        #register to flag SF
        cpu.RFLAGS |= self._flags['SF']
        self.assertTrue(cpu.SF)
        cpu.RFLAGS &= ~self._flags['SF']
        self.assertFalse(cpu.SF)

        #flag to register DF
        cpu.DF = True
        self.assertTrue( cpu.RFLAGS&self._flags['DF'] !=0)
        cpu.DF = False
        self.assertTrue( cpu.RFLAGS&self._flags['DF'] ==0)

        #register to flag DF
        cpu.RFLAGS |= self._flags['DF']
        self.assertTrue(cpu.DF)
        cpu.RFLAGS &= ~self._flags['DF']
        self.assertFalse(cpu.DF)

        #flag to register OF
        cpu.OF = True
        self.assertTrue( cpu.RFLAGS&self._flags['OF'] !=0)
        cpu.OF = False
        self.assertTrue( cpu.RFLAGS&self._flags['OF'] ==0)

        #register to flag
        cpu.RFLAGS |= self._flags['OF']
        self.assertTrue(cpu.OF)
        cpu.RFLAGS &= ~self._flags['OF']
        self.assertFalse(cpu.OF)

    def _check_flags_CPAZSIDO(self, c, p, a, z, s, i, d, o):
        self.assertEqual(self.cpu.CF, c)
        self.assertEqual(self.cpu.PF, p)
        self.assertEqual(self.cpu.AF, a)
        self.assertEqual(self.cpu.ZF, z)
        self.assertEqual(self.cpu.SF, s)
        self.assertEqual(self.cpu.IF, i)
        self.assertEqual(self.cpu.DF, d)
        self.assertEqual(self.cpu.OF, o)

    def _construct_flag_bitfield(self, flags):
        return reduce(operator.or_, (self._flags[f] for f in flags))

    def _construct_sym_flag_bitfield(self, flags):
        return reduce(operator.or_, (BitVecConstant(32, self._flags[f]) for f in flags))

    def test_set_eflags(self):
        self.assertEqual(self.cpu.EFLAGS, 0)

        flags = ['CF', 'PF', 'AF', 'ZF', 'SF']
        self.cpu.EFLAGS = self._construct_flag_bitfield(flags)

        self._check_flags_CPAZSIDO(1, 1, 1, 1, 1, 0, 0, 0)

    def test_get_eflags(self):
        self.assertEqual(self.cpu.EFLAGS, 0)

        flags = ['CF', 'AF', 'SF']
        self.cpu.CF = 1
        self.cpu.AF = 1
        self.cpu.SF = 1
        self.cpu.DF = 0

        self.assertEqual(self.cpu.EFLAGS, self._construct_flag_bitfield(flags))

    def test_set_sym_eflags(self):
        def check_flag(obj, flag):
            equal = obj.operands[0]
            extract = equal.operands[0]
            assert isinstance(obj, Bool)
            assert extract.begining == self._flag_offsets[flag]
            assert extract.end == extract.begining

        flags = ['CF', 'PF', 'AF', 'ZF']
        sym_bitfield = self._construct_sym_flag_bitfield(flags)
        self.cpu.EFLAGS = sym_bitfield

        check_flag(self.cpu.CF, 'CF')
        check_flag(self.cpu.PF, 'PF')
        check_flag(self.cpu.AF, 'AF')
        check_flag(self.cpu.ZF, 'ZF')

    def test_get_sym_eflags(self):
        def flatten_ors(x):
            '''
            Retrieve all nodes of a BitVecOr expression tree
            '''
            assert isinstance(x, BitVecOr)
            if any(isinstance(op, BitVecOr) for op in x.operands):
                ret = []
                for op in x.operands:
                    if isinstance(op, BitVecOr):
                        ret += flatten_ors(op)
                    else:
                        ret.append(op)
                return ret
            else:
                return list(x.operands)

        self.cpu.CF = 1
        self.cpu.AF = 1

        a = BitVecConstant(32, 1) != 0
        b = BitVecConstant(32, 0) != 0
        self.cpu.ZF = a
        self.cpu.SF = b

        flags = flatten_ors(self.cpu.EFLAGS)

        self.assertTrue(isinstance(self.cpu.EFLAGS, BitVecOr))
        self.assertEqual(len(flags), 8)

        self.assertEqual(self.cpu.CF, 1)
        self.assertEqual(self.cpu.AF, 1)
        self.assertIs(self.cpu.ZF, a)
        self.assertIs(self.cpu.SF, b)

    def testRegisterAccess(self):
        cpu = self.cpu

        #initially zero
        self.assertEqual(cpu.EAX, 0)

        cpu.EAX += 1
        self.assertEqual(cpu.EAX, 1)
        cpu.EAX = 0x8000000
        self.assertEqual(cpu.EAX, 0x8000000)
        cpu.EAX = 0xff000000
        self.assertEqual(cpu.EAX, 0xff000000)
        cpu.EAX = 0x00ff0000
        self.assertEqual(cpu.EAX, 0x00ff0000)
        cpu.EAX = 0x0000ff00
        self.assertEqual(cpu.EAX, 0x0000ff00)
        cpu.EAX = 0xff
        self.assertEqual(cpu.EAX, 0xff)

        #overflow shall be discarded
        #self.assertRaises@@@@@@@@@@@@cpu.EAX = 0x100000000
        cpu.EAX = 0x100000000
        self.assertEqual(cpu.EAX, 0x00000000)

        #partial register access
        cpu.EAX = 0x11223344
        self.assertEqual(cpu.EAX, 0x11223344)
        self.assertEqual(cpu.AX, 0x3344)
        self.assertEqual(cpu.AH, 0x33)
        self.assertEqual(cpu.AL, 0x44)

        #partial register mod
        cpu.AL=0xDD
        self.assertEqual(cpu.EAX, 0x112233DD)
        self.assertEqual(cpu.AX, 0x33DD)
        self.assertEqual(cpu.AH, 0x33)
        self.assertEqual(cpu.AL, 0xDD)

        cpu.AH=0xCC
        self.assertEqual(cpu.EAX, 0x1122CCDD)
        self.assertEqual(cpu.AX, 0xCCDD)
        self.assertEqual(cpu.AH, 0xCC)
        self.assertEqual(cpu.AL, 0xDD)

        #partial register mod is truncated
        cpu.AL=0xDD
        self.assertEqual(cpu.EAX, 0x1122CCDD)
        self.assertEqual(cpu.AX, 0xCCDD)
        self.assertEqual(cpu.AH, 0xCC)
        self.assertEqual(cpu.AL, 0xDD)

        cpu.EDX = 0x8048c50
        self.assertEqual(cpu.EDX, 0x8048c50)

        #initially zero
        self.assertEqual(cpu.ECX, 0)

        cpu.ECX += 1
        self.assertEqual(cpu.ECX, 1)
        cpu.ECX = 0x8000000
        self.assertEqual(cpu.ECX, 0x8000000)
        cpu.ECX = 0xff000000
        self.assertEqual(cpu.ECX, 0xff000000)
        cpu.ECX = 0x00ff0000
        self.assertEqual(cpu.ECX, 0x00ff0000)
        cpu.ECX = 0x0000ff00
        self.assertEqual(cpu.ECX, 0x0000ff00)
        cpu.ECX = 0xff
        self.assertEqual(cpu.ECX, 0xff)

        #overflow shall be discarded
        #self.assertRaises@@@@@@@@@@@@cpu.ECX = 0x100000000
        cpu.ECX = 0x100000000
        self.assertEqual(cpu.ECX, 0x00000000)

        #partial register access
        cpu.ECX = 0x11223344
        self.assertEqual(cpu.ECX, 0x11223344)
        self.assertEqual(cpu.CX, 0x3344)
        self.assertEqual(cpu.CH, 0x33)
        self.assertEqual(cpu.CL, 0x44)

        #partial register mod
        cpu.CL=0xDD
        self.assertEqual(cpu.ECX, 0x112233DD)
        self.assertEqual(cpu.CX, 0x33DD)
        self.assertEqual(cpu.CH, 0x33)
        self.assertEqual(cpu.CL, 0xDD)

        cpu.CH=0xCC
        self.assertEqual(cpu.ECX, 0x1122CCDD)
        self.assertEqual(cpu.CX, 0xCCDD)
        self.assertEqual(cpu.CH, 0xCC)
        self.assertEqual(cpu.CL, 0xDD)

        #partial register mod is truncated
        cpu.CL=0xDD
        self.assertEqual(cpu.ECX, 0x1122CCDD)
        self.assertEqual(cpu.CX, 0xCCDD)
        self.assertEqual(cpu.CH, 0xCC)
        self.assertEqual(cpu.CL, 0xDD)


    def test_le_or(self):
        cs = ConstraintSet()
        mem = SMemory64(cs)

        cpu = AMD64Cpu(mem)
        mem.mmap(0x1000,0x1000,'rwx')
        cpu.write_int(0x1000, 0x4142434445464748, 64)
        cpu.write_int(0x1000, cpu.read_int(0x1000, 32) | 0, 32)

        addr1 = cs.new_bitvec(64)
        cs.add(addr1 == 0x1004)
        cpu.write_int(addr1, 0x58, 8)

        self.assertEqual(cpu.read_int(0x1000,32), 0x45464748)

        addr1 = cs.new_bitvec(64)
        cs.add(addr1 == 0x1000)
        cpu.write_int(addr1, 0x59, 8)

        solutions = solver.get_all_values(cs, cpu.read_int(0x1000,32))
        self.assertEqual(len(solutions), 1)
        self.assertEqual(solutions[0], 0x45464759)
        cpu.write_int(0x1000, cpu.read_int(0x1000,32) | 0, 32)
        cpu.write_int(0x1000, cpu.read_int(0x1000,32) | 0, 32)
        cpu.write_int(0x1000, cpu.read_int(0x1000,32) | 0, 32)
        solutions = solver.get_all_values(cs, cpu.read_int(0x1000,32))
        self.assertEqual(len(solutions), 1)
        self.assertEqual(solutions[0], 0x45464759)

    def test_cache_001(self):
        cs = ConstraintSet()
        mem = SMemory64(ConstraintSet())

        cpu = AMD64Cpu(mem)
        mem.mmap(0x1000,0x1000,'rwx')
        cpu.write_int(0x1000, 0x4142434445464748, 64)
        #print cpu.mem_cache
        cpu.write_int(0x1004, 0x5152535455565758, 64)
        #print cpu.mem_cache
        cpu.write_int(0x1008, 0x6162636465666768, 64)
        #print cpu.mem_cache
        #print hex(cpu.read_int(0x1000,32))
        #print hex(cpu.read_int(0x1000,32))
        #print hex(cpu.read_int(0x1000,32))
        #print hex(cpu.read_int(0x1000,32))
        #print hex(cpu.read_int(0x1000,32))
        self.assertEqual(cpu.read_int(0x1000,32), 0x45464748)
        cpu.write_int( 0x1000, 0x45464748,32)
        self.assertEqual(cpu.read_int(0x1000,32), 0x45464748)
        self.assertEqual(cpu.read_int(0x1004,32), 0x55565758)
        self.assertEqual(cpu.read_int(0x1008,32), 0x65666768)

        self.assertEqual(cpu.read_int(0x1008,64), 0x6162636465666768)
        self.assertEqual(cpu.read_int(0x1000,64), 0x5556575845464748)

        #cpu.writeback()
        for i in xrange(0x10):
            self.assertEqual(mem[i+0x1000], 'HGFEXWVUhgfedcba'[i])
        self.assertItemsEqual(mem.read(0x1000,0x10), 'HGFEXWVUhgfedcba')

    def test_cache_002(self):
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)

        #alloc/map a little mem
        addr = mem.mmap(0x1000, 0x1000, 'rwx')
        self.assertEqual(addr, 0x1000)

        cpu.write_int(0x1000, 0x4142434445464748, 64)
        cpu.write_int(0x1004, 0x5152535455565758, 64)
        cpu.write_int(0x1008, 0x6162636465666768, 64)
        
        self.assertEqual(cpu.read_int(0x1000,32), 0x45464748)
        self.assertEqual(cpu.read_int(0x1004,32), 0x55565758)
        self.assertEqual(cpu.read_int(0x1008,32), 0x65666768)

        self.assertEqual(cpu.read_int(0x1008,64), 0x6162636465666768)
        self.assertEqual(cpu.read_int(0x1000,64), 0x5556575845464748)

        #cpu.writeback()
        for i in xrange(0x10):
            self.assertEqual(mem[i+0x1000], 'HGFEXWVUhgfedcba'[i])

    def test_cache_003(self):
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)

        #alloc/map a little mem
        addr = mem.mmap(0x1000, 0x1000, 'rwx')
        self.assertEqual(addr, 0x1000)

        cpu.write_int(0x1000, 0x4142434445464748, 64)
        cpu.write_int(0x1008, 0x6162636465666768, 64)


        self.assertEqual(cpu.read_int(0x1000,64), 0x4142434445464748)
        self.assertEqual(cpu.read_int(0x1008,64), 0x6162636465666768)

        for i in range(8):
            self.assertEqual( cpu.read_int(0x1000+i, 8), ord("HGFEDCBA"[i]) )
        for i in range(8):
            self.assertEqual( cpu.read_int(0x1008+i, 8), ord("hgfedcba"[i]) )

        addr1 = cs.new_bitvec(64)
        cs.add(addr1 == 0x1004)
        cpu.write_int(addr1, 0x58, 8)

        # 48 47 46 45 58 43 42 41 68 67 66 65 64 63 62 61 

        value = cpu.read_int(0x1004, 16)
        self.assertItemsEqual(solver.get_all_values(cs, value), [0x4358] )

        addr2 = cs.new_bitvec(64)
        cs.add(Operators.AND(addr2>=0x1000, addr2<=0x100c))

        cpu.write_int(addr2, 0x5959, 16) 
        
        solutions = solver.get_all_values(cs, cpu.read_int(addr2, 32) )
    
        self.assertEqual( len(solutions), 0x100c-0x1000+1 )
        self.assertEqual( set(solutions), set([0x45465959, 0x41425959, 0x58455959, 0x65665959, 0x67685959, 0x43585959, 0x68415959, 0x42435959, 0x66675959, 0x62635959, 0x64655959, 0x63645959, 0x61625959]))

        
    def test_cache_004(self):
        import random
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)

        #alloc/map a little mem
        addr = mem.mmap(0x1000, 0x1000, 'rwx')
        self.assertEqual(addr, 0x1000)


        memory = ['\x00'] *0x1000
        written = set()
        for _ in xrange(1000):
            address = random.randint(0x1000,0x2000-8)
            [written.add(i) for i in range(address,address+8)]
            value = random.randint(0x0,0xffffffffffffffff)
            memory[address-0x1000:address-0x1000+8] = list(struct.pack('<Q',value))
            cpu.write_int(address, value, 64)
            if random.randint(0,10) > 5:
                cpu.read_int(random.randint(0x1000,0x2000-8), random.choice([8,16,32,64]))

        written = list(written)
        random.shuffle(written)
        for address in written:
            size = random.choice([8,16,32,64])
            if address > 0x2000-size/8:
                continue
            pattern = {8:'B', 16:'<H', 32:'<L', 64:'<Q'} [size]
            self.assertEqual(cpu.read_int(address,size), struct.unpack(pattern, ''.join(memory[address-0x1000:address-0x1000+size/8]))[0] )



    def test_cache_005(self):
        import random
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)

        #alloc/map a little mem
        addr = mem.mmap(0x1000, 0x1000, 'rwx')
        self.assertEqual(addr, 0x1000)
        self.assertRaises(Exception, cpu.write_int, 0x1000-1, 0x414243445464748, 64)
        self.assertRaises(Exception, cpu.write_int, 0x2000-7, 0x414243445464748, 64)
        self.assertRaises(Exception, cpu.read_int, 0x1000-1, 0x414243445464748, 64)
        self.assertRaises(Exception, cpu.read_int, 0x2000-7, 0x414243445464748, 64)

        #alloc/map a little mem
        addr = mem.mmap(0x7000, 0x1000, 'r')
        self.assertEqual(addr, 0x7000)
        self.assertRaises(Exception, cpu.write_int, 0x7000-1, 0x414243445464748, 64)
        self.assertRaises(Exception, cpu.write_int, 0x8000-7, 0x414243445464748, 64)
        self.assertRaises(Exception, cpu.read_int, 0x7000-1, 0x414243445464748, 64)
        self.assertRaises(Exception, cpu.read_int, 0x8000-7, 0x414243445464748, 64)

        self.assertRaises(Exception, cpu.write_int, 0x7100, 0x414243445464748, 64)

        #alloc/map a little mem
        addr = mem.mmap(0xf000, 0x1000, 'w')
        self.assertEqual(addr, 0xf000)
        self.assertRaises(Exception, cpu.write_int, 0xf000-1, 0x414243445464748, 64)
        self.assertRaises(Exception, cpu.write_int, 0x10000-7, 0x414243445464748, 64)
        self.assertRaises(Exception, cpu.read_int, 0xf000-1, 0x414243445464748, 64)
        self.assertRaises(Exception, cpu.read_int, 0x10000-7, 0x414243445464748, 64)

        self.assertRaises(Exception, cpu.read_int, 0xf100, 0x414243445464748, 64)


    def test_IDIV_concrete(self):
        cs = ConstraintSet()
        mem = SMemory32(cs)
        cpu = I386Cpu(mem)

        #alloc/map a little mem
        code = mem.mmap(0x1000, 0x1000, 'rwx')
        stack = mem.mmap(0xf000, 0x1000, 'rw')

        mem[code:code+3] = '\xf7\x7d\xf4'
        cpu.EIP = code
        cpu.EAX = 116
        cpu.EBP=stack+0x700
        cpu.write_int(cpu.EBP - 0xc, 100, 32)

        cpu.execute()

        self.assertEqual(cpu.EAX, 1)

    def test_IDIV_symbolic(self):
        cs = ConstraintSet()
        mem = SMemory32(cs)
        cpu = I386Cpu(mem)

        #alloc/map a little mem
        code = mem.mmap(0x1000, 0x1000, 'rwx')
        stack = mem.mmap(0xf000, 0x1000, 'rw')

        mem[code:code+3] = '\xf7\x7d\xf4'
        cpu.EIP = code
        cpu.EAX = cs.new_bitvec(32, 'EAX')  
        cs.add(cpu.EAX == 116)
        cpu.EBP = cs.new_bitvec(32, 'EBP')
        cs.add(cpu.EBP == stack+0x700)
        value = cs.new_bitvec(32, 'VALUE')
        cpu.write_int(cpu.EBP - 0xc, value, 32)
        cs.add(value == 100)
        cpu.execute()
        cs.add(cpu.EAX == 1)
        self.assertTrue(solver.check(cs))

    def test_IDIV_grr001(self):
        cs = ConstraintSet()
        mem = SMemory32(cs)
        cpu = I386Cpu(mem)

        #alloc/map a little mem
        code = mem.mmap(0x1000, 0x1000, 'rwx')

        mem[code:code+2] = '\xf7\xf9'
        cpu.EIP = code
        cpu.EAX = 0xffffffff
        cpu.EDX = 0xffffffff
        cpu.ECX = 0x32
        cpu.execute()
        self.assertEqual(cpu.EAX, 0)

    def test_IDIV_grr001_symbolic(self):
        cs = ConstraintSet()
        mem = SMemory32(cs)
        cpu = I386Cpu(mem)

        #alloc/map a little mem
        code = mem.mmap(0x1000, 0x1000, 'rwx')

        mem[code:code+2] = '\xf7\xf9'
        cpu.EIP = code
        cpu.EAX = cs.new_bitvec(32, 'EAX')  
        cs.add(cpu.EAX == 0xffffffff)
        cpu.EDX = cs.new_bitvec(32, 'EDX')  
        cs.add(cpu.EDX == 0xffffffff)
        cpu.ECX = cs.new_bitvec(32, 'ECX')  
        cs.add(cpu.ECX == 0x32)

        cpu.execute()
        cs.add(cpu.EAX == 0)
        self.assertTrue(solver.check(cs))

    def test_ADC_001(self):
        '''INSTRUCTION: 0x0000000067756f91:	adc	esi, edx'''

        cs = ConstraintSet()
        mem = SMemory32(cs)
        cpu = I386Cpu(mem)

        #alloc/map a little mem
        code = mem.mmap(0x1000, 0x1000, 'rwx')

        mem[code:code+2] = '\x13\xf2'
        cpu.EIP = code
        cpu.ESI = 0x0
        cpu.EDX = 0xffffffff
        cpu.CF = True
        cpu.execute()
        self.assertEqual(cpu.EDX, 0xffffffff)
        self.assertEqual(cpu.ESI, 0)
        self.assertEqual(cpu.CF, True)

    def test_ADC_001_symbolic(self):
        '''INSTRUCTION: 0x0000000067756f91:	adc	esi, edx'''

        cs = ConstraintSet()
        mem = SMemory32(cs)
        cpu = I386Cpu(mem)

        #alloc/map a little mem
        code = mem.mmap(0x1000, 0x1000, 'rwx')

        mem[code:code+2] = '\x13\xf2'
        cpu.EIP = code
        cpu.ESI = cs.new_bitvec(32, 'ESI')  
        cs.add(cpu.ESI == 0)
        cpu.EDX = cs.new_bitvec(32, 'EDX')  
        cs.add(cpu.EDX == 0xffffffff)
        cpu.CF = cs.new_bool('CF')  
        cs.add(cpu.CF)

        cpu.execute()

        cs.add(cpu.ESI == 0)
        cs.add(cpu.EDX == 0xffffffff)
        cs.add(cpu.CF)

        self.assertTrue(solver.check(cs))


    def test_CMPXCHG8B_symbolic(self):
        '''CMPXCHG8B'''

        cs = ConstraintSet()
        mem = SMemory32(cs)
        cpu = I386Cpu(mem)

        #alloc/map a little mem
        code = mem.mmap(0x1000, 0x1000, 'rwx')
        data = mem.mmap(0x2000, 0x1000, 'rwx')

        mem[code:code+5] = '\xf0\x0f\xc7\x0f;'
        cpu.EIP = code

        cpu.EDI = cs.new_bitvec(32, 'EDI')  
        cs.add( Operators.OR(cpu.EDI == 0x2000, cpu.EDI == 0x2100, cpu.EDI == 0x2200 ) )
        self.assertEqual(sorted(solver.get_all_values(cs, cpu.EDI)),[0x2000,0x2100,0x2200])
        self.assertEqual(cpu.read_int(0x2000,64), 0)
        self.assertEqual(cpu.read_int(0x2100,64), 0)
        self.assertEqual(cpu.read_int(0x2200,64), 0)
        self.assertItemsEqual(solver.get_all_values(cs, cpu.read_int(cpu.EDI,64)), [0]) 
        #self.assertEqual(cpu.read_int(cpu.EDI,64), 0 )

        cpu.write_int(0x2100, 0x4142434445464748, 64)


        cpu.EAX = cs.new_bitvec(32, 'EAX')  
        cs.add( Operators.OR(cpu.EAX == 0x41424344, cpu.EAX == 0x0badf00d, cpu.EAX == 0xf7f7f7f7 ) )
        cpu.EDX= 0x45464748

        cpu.execute()
        self.assertTrue(solver.check(cs))

        self.assertItemsEqual(solver.get_all_values(cs, cpu.read_int(cpu.EDI,64)), [0, 4702394921427289928])

    def test_POPCNT(self):
        '''POPCNT EAX, EAX
        CPU Dump
        Address   Hex dump   
        00333689  F3 0F B8 C0
        '''

        cs = ConstraintSet()
        mem = SMemory32(cs)
        cpu = I386Cpu(mem)

        #alloc/map a little mem
        code = mem.mmap(0x1000, 0x1000, 'rwx')

        mem[code:code+4] = '\xF3\x0F\xB8\xC0'
        cpu.EIP = code
        cpu.EAX = 0x75523C33
        cpu.execute()
        self.assertEqual(cpu.EAX, 0x10)
        self.assertEqual(cpu.ZF, False)

    def test_DEC_1(self):
        ''' Instruction DEC_1 
            Groups: mode64 
            0x41e10a:	dec	ecx
        '''
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x0041e000, 0x1000, 'rwx')
        mem[0x0041e10a] = '\xff'
        mem[0x0041e10b] = '\xc9'
        cpu.AF = False
        cpu.OF = False
        cpu.ZF = False
        cpu.RIP = 0x41e10a
        cpu.PF = False
        cpu.SF = False
        cpu.ECX = 0xd
        cpu.execute()
        self.assertItemsEqual(mem[0x41e10a:0x41e10c], '\xff\xc9')
        self.assertEqual(cpu.AF, False)
        self.assertEqual(cpu.OF, False)
        self.assertEqual(cpu.ZF, False)
        self.assertEqual(cpu.RIP, 4317452L)
        self.assertEqual(cpu.PF, True)
        self.assertEqual(cpu.SF, False)
        self.assertEqual(cpu.ECX, 12L)

    def test_PUSHFD_1(self):
        ''' Instruction PUSHFD_1 
            Groups: not64bitmode 
            0x8065f6f:	pushfd	
        '''
        mem = Memory32()
        cpu = I386Cpu(mem)
        mem.mmap(0x08065000, 0x1000, 'rwx')
        mem.mmap(0xffffc000, 0x1000, 'rwx')
        mem[0xffffc600:0xffffc609] = '\x00\x00\x00\x00\x02\x03\x00\x00\x00'
        mem[0x08065f6f] = '\x9c'
        cpu.EIP = 0x8065f6f
        cpu.EBP = 0xffffb600
        cpu.ESP = 0xffffc604

        cpu.CF = True
        cpu.OF = True
        cpu.AF = True
        cpu.ZF = True
        cpu.PF = True
        cpu.execute()
    
        self.assertItemsEqual(mem[0xffffc600:0xffffc609], '\x55\x08\x00\x00\x02\x03\x00\x00\x00')
        self.assertEqual(mem[0x8065f6f], '\x9c')
        self.assertEqual(cpu.EIP, 0x8065f70)
        self.assertEqual(cpu.EBP, 0xffffb600)
        self.assertEqual(cpu.ESP, 0xffffc600)

    def test_XLATB_1(self):
        ''' Instruction XLATB_1 
            Groups:  
            0x8059a8d: xlatb   
        '''
        mem = Memory32()
        cpu = I386Cpu(mem)
        mem.mmap(0x08059000, 0x1000, 'rwx')
        mem.mmap(0xffffd000, 0x1000, 'rwx')
        mem[0x08059a8d] = '\xd7'
        mem[0xffffd00a] = '\x41'

        cpu.EBX=0xffffd000
        cpu.AL=0x0a
        cpu.EIP = 0x8059a8d
        cpu.execute()
    
        self.assertEqual(mem[0x8059a8d], '\xd7')
        self.assertEqual(mem[0xffffd00a], '\x41')
        self.assertEqual(cpu.AL, 0x41)     
        self.assertEqual(cpu.EIP, 134584974L)

    def test_XLATB_1_symbolic(self):
        ''' Instruction XLATB_1 
            Groups:  
            0x8059a8d: xlatb   
        '''
        cs = ConstraintSet()
        mem = SMemory32(cs)
        cpu = I386Cpu(mem)
        mem.mmap(0x08059000, 0x1000, 'rwx')
        mem.mmap(0xffffd000, 0x1000, 'rwx')
        mem[0x8059a8d] = '\xd7'
        mem[0xffffd00a] = '\x41'
        cpu.EIP = 0x8059a8d
        cpu.AL=0xa

        cpu.EBX=0xffffd000

    def test_SAR_1(self):
        ''' Instruction SAR_1 
            Groups: mode64 
            0x41e10a:	SAR	cl, EBX
Using the SAR instruction to perform a division operation does not produce the same result as the IDIV instruction. The quotient from the IDIV instruction is rounded toward zero, whereas the "quotient" of the SAR instruction is rounded toward negative infinity. This difference is apparent only for negative numbers. For example, when the IDIV instruction is used to divide -9 by 4, the result is -2 with a remainder of -1. If the SAR instruction is used to shift -9 right by two bits, the result is -3 and the "remainder" is +3; however, the SAR instruction stores only the most significant bit of the remainder (in the CF flag).

        '''
        mem = Memory32()
        cpu = I386Cpu(mem)
        mem.mmap(0x0041e000, 0x1000, 'rwx')
        mem[0x0041e10a] = '\xc1'
        mem[0x0041e10b] = '\xf8'
        mem[0x0041e10c] = '\x02'
        cpu.RIP = 0x41e10a
        cpu.PF = True
        cpu.SF = True
        cpu.ZF = False
        cpu.AF = False
        cpu.OF = False
        cpu.EAX = 0xfffffff7
        cpu.execute()
        self.assertEqual(cpu.CF, True)
        self.assertEqual(cpu.SF, True)
        self.assertEqual(cpu.PF, False)
        self.assertEqual(cpu.ZF, False)
        self.assertEqual(cpu.EAX, 0xfffffffd)


    def test_SAR_1_symbolic(self):
        cs = ConstraintSet()
        mem = SMemory32(cs)
        cpu = I386Cpu(mem)
        mem.mmap(0x0041e000, 0x1000, 'rwx')
        mem[0x0041e10a] = '\xc1'
        mem[0x0041e10b] = '\xf8'
        mem[0x0041e10c] = '\x02'
        cpu.RIP = 0x41e10a

        cpu.PF = cs.new_bool();cs.add(cpu.PF == True)
        cpu.SF = cs.new_bool();cs.add(cpu.SF == True)
        cpu.ZF = cs.new_bool();cs.add(cpu.ZF == False)
        cpu.AF = cs.new_bool();cs.add(cpu.AF == False)
        cpu.OF = cs.new_bool();cs.add(cpu.OF == False)
        cpu.EAX = cs.new_bitvec(32);cs.add(cpu.EAX == 0xfffffff7)

        done = False
        while not done:
            try:
                cpu.execute()
                #cpu.writeback()
                done = True
            except ConcretizeRegister,e:
                symbol = getattr(cpu, e.reg_name)
                values = solver.get_all_values(cs, symbol)
                self.assertEqual(len(values), 1)
                setattr(cpu, e.reg_name, values[0])

        condition = True
        condition = Operators.AND(condition, cpu.EAX == 0xfffffffd)
        condition = Operators.AND(condition, cpu.ZF == False)
        condition = Operators.AND(condition, cpu.CF == True)
        condition = Operators.AND(condition, cpu.SF == True)
        condition = Operators.AND(condition, cpu.PF == False)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          

    def test_SAR_2(self):
        ''' Instruction SAR_2 

        '''
        mem = Memory32()
        cpu = I386Cpu(mem)
        mem.mmap(0x0041e000, 0x1000, 'rwx')
        mem[0x0041e10a] = '\xc0'
        mem[0x0041e10b] = '\xf8'
        mem[0x0041e10c] = '\x9f'
        cpu.RIP = 0x41e10a
        cpu.CF = True
        cpu.SF = True
        cpu.ZF = False
        cpu.AF = False
        cpu.OF = False
        cpu.PF = False
        cpu.EAX = 0xfffffffd
        cpu.execute()
        self.assertEqual(cpu.PF, True)
        self.assertEqual(cpu.SF, True)
        self.assertEqual(cpu.ZF, False)
        self.assertEqual(cpu.OF, False)
        self.assertEqual(cpu.AF, False)
        self.assertEqual(cpu.EAX, 0xffffffff)


    def test_SAR_2_symbolicsa(self):
        cs = ConstraintSet()
        mem = SMemory32(cs)
        cpu = I386Cpu(mem)
        mem.mmap(0x0041e000, 0x1000, 'rwx')

        mem[0x0041e10a] = '\xc0'
        mem[0x0041e10b] = '\xf8'
        mem[0x0041e10c] = '\xff'
        cpu.RIP = 0x41e10a

        cpu.PF = cs.new_bool();cs.add(cpu.PF == True)
        cpu.CF = cs.new_bool();cs.add(cpu.CF == False)
        cpu.SF = cs.new_bool();cs.add(cpu.SF == True)
        cpu.ZF = cs.new_bool();cs.add(cpu.ZF == False)
        cpu.AF = cs.new_bool();cs.add(cpu.AF == False)
        cpu.OF = cs.new_bool();cs.add(cpu.OF == False)
        cpu.EAX = cs.new_bitvec(32);cs.add(cpu.EAX == 0xffffffff)

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
        condition = Operators.AND(condition, cpu.EAX == 0xffffffff)
        condition = Operators.AND(condition, cpu.ZF == False)
        condition = Operators.AND(condition, cpu.PF == True)
        condition = Operators.AND(condition, cpu.SF == True)
        condition = Operators.AND(condition, cpu.CF == True)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))
          
    def test_SAR_3_symbolic(self):
        ''' Instruction SAR_6 
            eax            0xffffd000	-12288
            ecx            0x3d1ce0ff	1025302783
            eip            0x80483f3	0x80483f3
            eflags         0x287	[ CF PF SF IF ]
            0xffffd000:	0x8f

            => 0x80483f0 <main+3>:	sarb   %cl,0x0(%eax)

            eax            0xffffd000	-12288
            ecx            0x3d1ce0ff	1025302783
            eip            0x80483f4	0x80483f4
            eflags         0x287	[ CF PF SF IF ]
            0xffffd000:	0xff

        '''
        cs = ConstraintSet()
        mem = SMemory32(cs)
        cpu = I386Cpu(mem)
        mem.mmap(0x0804d000, 0x1000, 'rwx')
        mem.mmap(0xffffb000, 0x1000, 'rwx')
        mem[0x804d600] = '\xd2'
        mem[0x804d601] = '\x78'
        mem[0x804d602] = '\x00'
        mem[0x804d603] = '\xff'
        addr = cs.new_bitvec(32) ; cs.add(addr == 0xffffb000)
        value = cs.new_bitvec(8) ; cs.add(value == 0x8f)
        mem[addr] = value

        cpu.EAX = cs.new_bitvec(32)
        cs.add(cpu.EAX == 0xffffb000)
        cpu.CL = cs.new_bitvec(8)
        cs.add(cpu.CL == 0xff)

        cpu.EIP = 0x804d600
        cpu.CF = cs.new_bool(); cs.add(cpu.CF == True)
        cpu.PF = cs.new_bool(); cs.add(cpu.PF == True)
        cpu.SF = cs.new_bool(); cs.add(cpu.SF == True)

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
        condition = Operators.AND(condition, cpu.read_int(0xffffb000, 8) == 0xff)
        condition = Operators.AND(condition, cpu.CL == 0xff)
        condition = Operators.AND(condition, cpu.CF == True)
        condition = Operators.AND(condition, cpu.PF == True)
        condition = Operators.AND(condition, cpu.SF == True)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

if __name__ == '__main__':
    unittest.main()
