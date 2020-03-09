import unittest

from manticore.native.cpu.abstractcpu import ConcretizeRegister
from manticore.native.cpu.x86 import AMD64Cpu
from manticore.native.memory import *
from manticore.core.smtlib.solver import Z3Solver

solver = Z3Solver.instance()


class CPUTest(unittest.TestCase):
    _multiprocess_can_split_ = True

    class ROOperand:
        """ Mocking class for operand ronly """

        def __init__(self, size, value):
            self.size = size
            self.value = value

        def read(self):
            return self.value & ((1 << self.size) - 1)

    class RWOperand(ROOperand):
        """ Mocking class for operand rw """

        def write(self, value):
            self.value = value & ((1 << self.size) - 1)
            return self.value

    def test_MOVHPD_1(self):
        """ Instruction MOVHPD_1
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A24000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7A249D1, "IVATE\x00\x00\x00")
        mem.write(0x7FFFF7DF294E, "f\x0f\x16O\x08")
        cpu.XMM1 = 0xFFFFFFFFFFFF00FF52505F4342494C47
        cpu.RDI = 0x7FFFF7A249C9
        cpu.RIP = 0x7FFFF7DF294E
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7A249D1:0x7FFFF7A249D9],
            [b"I", b"V", b"A", b"T", b"E", b"\x00", b"\x00", b"\x00"],
        )
        self.assertEqual(
            mem[0x7FFFF7DF294E:0x7FFFF7DF2953], [b"f", b"\x0f", b"\x16", b"O", b"\x08"]
        )
        self.assertEqual(cpu.XMM1, 5492818941963568420245782219847)
        self.assertEqual(cpu.RDI, 140737347996105)
        self.assertEqual(cpu.RIP, 140737351985491)

    def test_MOVHPD_10(self):
        """ Instruction MOVHPD_10
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A24000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7A248D6, "2.5\x00GLIB")
        mem.write(0x7FFFF7DF294E, "f\x0f\x16O\x08")
        cpu.XMM1 = 0xFFFFFFFF00FFFFFF2E325F4342494C47
        cpu.RDI = 0x7FFFF7A248CE
        cpu.RIP = 0x7FFFF7DF294E
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7A248D6:0x7FFFF7A248DE], [b"2", b".", b"5", b"\x00", b"G", b"L", b"I", b"B"]
        )
        self.assertEqual(
            mem[0x7FFFF7DF294E:0x7FFFF7DF2953], [b"f", b"\x0f", b"\x16", b"O", b"\x08"]
        )
        self.assertEqual(cpu.XMM1, 88109632480871197291218000195730623559)
        self.assertEqual(cpu.RDI, 140737347995854)
        self.assertEqual(cpu.RIP, 140737351985491)

    def test_MOVHPD_11(self):
        """ Instruction MOVHPD_11
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A24000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7A248D6, "2.5\x00GLIB")
        mem.write(0x7FFFF7DF2953, "f\x0f\x16V\x08")
        cpu.XMM2 = 0x42494C4700352E322E325F4342494C47
        cpu.RSI = 0x7FFFF7A248CE
        cpu.RIP = 0x7FFFF7DF2953
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7A248D6:0x7FFFF7A248DE], [b"2", b".", b"5", b"\x00", b"G", b"L", b"I", b"B"]
        )
        self.assertEqual(
            mem[0x7FFFF7DF2953:0x7FFFF7DF2958], [b"f", b"\x0f", b"\x16", b"V", b"\x08"]
        )
        self.assertEqual(cpu.XMM2, 88109632480871197291218000195730623559)
        self.assertEqual(cpu.RSI, 140737347995854)
        self.assertEqual(cpu.RIP, 140737351985496)

    def test_MOVHPD_12(self):
        """ Instruction MOVHPD_12
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A24000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7A248D6, "2.5\x00GLIB")
        mem.write(0x7FFFF7DF294E, "f\x0f\x16O\x08")
        cpu.XMM1 = 0xFFFFFFFF00FFFFFF2E325F4342494C47
        cpu.RDI = 0x7FFFF7A248CE
        cpu.RIP = 0x7FFFF7DF294E
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7A248D6:0x7FFFF7A248DE], [b"2", b".", b"5", b"\x00", b"G", b"L", b"I", b"B"]
        )
        self.assertEqual(
            mem[0x7FFFF7DF294E:0x7FFFF7DF2953], [b"f", b"\x0f", b"\x16", b"O", b"\x08"]
        )
        self.assertEqual(cpu.XMM1, 88109632480871197291218000195730623559)
        self.assertEqual(cpu.RDI, 140737347995854)
        self.assertEqual(cpu.RIP, 140737351985491)

    def test_MOVHPD_13(self):
        """ Instruction MOVHPD_13
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A21000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7A218DA, "tart_mai")
        mem.write(0x7FFFF7DF294E, "f\x0f\x16O\x08")
        cpu.XMM1 = 0x735F6362696C5F5F
        cpu.RDI = 0x7FFFF7A218D2
        cpu.RIP = 0x7FFFF7DF294E
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7A218DA:0x7FFFF7A218E2], [b"t", b"a", b"r", b"t", b"_", b"m", b"a", b"i"]
        )
        self.assertEqual(
            mem[0x7FFFF7DF294E:0x7FFFF7DF2953], [b"f", b"\x0f", b"\x16", b"O", b"\x08"]
        )
        self.assertEqual(cpu.XMM1, 140074810698054820722452200425796689759)
        self.assertEqual(cpu.RDI, 140737347983570)
        self.assertEqual(cpu.RIP, 140737351985491)

    def test_MOVHPD_14(self):
        """ Instruction MOVHPD_14
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A20000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7A20A9B, "\x00acct\x00_n")
        mem.write(0x7FFFF7DF2953, "f\x0f\x16V\x08")
        cpu.XMM2 = 0x36766772615F6C645F
        cpu.RSI = 0x7FFFF7A20A93
        cpu.RIP = 0x7FFFF7DF2953
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7A20A9B:0x7FFFF7A20AA3],
            [b"\x00", b"a", b"c", b"c", b"t", b"\x00", b"_", b"n"],
        )
        self.assertEqual(
            mem[0x7FFFF7DF2953:0x7FFFF7DF2958], [b"f", b"\x0f", b"\x16", b"V", b"\x08"]
        )
        self.assertEqual(cpu.XMM2, 146708356959127564005328096862462043231)
        self.assertEqual(cpu.RSI, 140737347979923)
        self.assertEqual(cpu.RIP, 140737351985496)

    def test_MOVHPD_15(self):
        """ Instruction MOVHPD_15
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A23000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7A232EE, "nable_se")
        mem.write(0x7FFFF7DF2953, "f\x0f\x16V\x08")
        cpu.XMM2 = 0x36655F6362696C5F5F
        cpu.RSI = 0x7FFFF7A232E6
        cpu.RIP = 0x7FFFF7DF2953
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7A232EE:0x7FFFF7A232F6], [b"n", b"a", b"b", b"l", b"e", b"_", b"s", b"e"]
        )
        self.assertEqual(
            mem[0x7FFFF7DF2953:0x7FFFF7DF2958], [b"f", b"\x0f", b"\x16", b"V", b"\x08"]
        )
        self.assertEqual(cpu.XMM2, 134851076577508085086976746042965122911)
        self.assertEqual(cpu.RSI, 140737347990246)
        self.assertEqual(cpu.RIP, 140737351985496)

    def test_MOVHPD_16(self):
        """ Instruction MOVHPD_16
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A24000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7A248D6, "2.5\x00GLIB")
        mem.write(0x7FFFF7DF2953, "f\x0f\x16V\x08")
        cpu.XMM2 = 0x42494C4700352E322E325F4342494C47
        cpu.RSI = 0x7FFFF7A248CE
        cpu.RIP = 0x7FFFF7DF2953
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7A248D6:0x7FFFF7A248DE], [b"2", b".", b"5", b"\x00", b"G", b"L", b"I", b"B"]
        )
        self.assertEqual(
            mem[0x7FFFF7DF2953:0x7FFFF7DF2958], [b"f", b"\x0f", b"\x16", b"V", b"\x08"]
        )
        self.assertEqual(cpu.XMM2, 88109632480871197291218000195730623559)
        self.assertEqual(cpu.RSI, 140737347995854)
        self.assertEqual(cpu.RIP, 140737351985496)

    def test_MOVHPD_17(self):
        """ Instruction MOVHPD_17
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DD7000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7DD7671, "_dso_for")
        mem.write(0x7FFFF7DF294E, "f\x0f\x16O\x08")
        cpu.XMM1 = 0x646E69665F6C645F
        cpu.RDI = 0x7FFFF7DD7669
        cpu.RIP = 0x7FFFF7DF294E
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7DD7671:0x7FFFF7DD7679], [b"_", b"d", b"s", b"o", b"_", b"f", b"o", b"r"]
        )
        self.assertEqual(
            mem[0x7FFFF7DF294E:0x7FFFF7DF2953], [b"f", b"\x0f", b"\x16", b"O", b"\x08"]
        )
        self.assertEqual(cpu.XMM1, 152110412837725123259047000460919333983)
        self.assertEqual(cpu.RDI, 140737351874153)
        self.assertEqual(cpu.RIP, 140737351985491)

    def test_MOVHPD_18(self):
        """ Instruction MOVHPD_18
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A24000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7A248D6, "2.5\x00GLIB")
        mem.write(0x7FFFF7DF2953, "f\x0f\x16V\x08")
        cpu.XMM2 = 0x42494C4700352E322E325F4342494C47
        cpu.RSI = 0x7FFFF7A248CE
        cpu.RIP = 0x7FFFF7DF2953
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7A248D6:0x7FFFF7A248DE], [b"2", b".", b"5", b"\x00", b"G", b"L", b"I", b"B"]
        )
        self.assertEqual(
            mem[0x7FFFF7DF2953:0x7FFFF7DF2958], [b"f", b"\x0f", b"\x16", b"V", b"\x08"]
        )
        self.assertEqual(cpu.XMM2, 88109632480871197291218000195730623559)
        self.assertEqual(cpu.RSI, 140737347995854)
        self.assertEqual(cpu.RIP, 140737351985496)

    def test_MOVHPD_19(self):
        """ Instruction MOVHPD_19
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DD7000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7DD7750, "obal_ro\x00")
        mem.write(0x7FFFF7DF294E, "f\x0f\x16O\x08")
        cpu.XMM1 = 0x6C675F646C74725F
        cpu.RDI = 0x7FFFF7DD7748
        cpu.RIP = 0x7FFFF7DF294E
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7DD7750:0x7FFFF7DD7758], [b"o", b"b", b"a", b"l", b"_", b"r", b"o", b"\x00"]
        )
        self.assertEqual(
            mem[0x7FFFF7DF294E:0x7FFFF7DF2953], [b"f", b"\x0f", b"\x16", b"O", b"\x08"]
        )
        self.assertEqual(cpu.XMM1, 578664706209732724830403288697696863)
        self.assertEqual(cpu.RDI, 140737351874376)
        self.assertEqual(cpu.RIP, 140737351985491)

    def test_MOVHPD_2(self):
        """ Instruction MOVHPD_2
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A24000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7A248D6, "2.5\x00GLIB")
        mem.write(0x7FFFF7DF294E, "f\x0f\x16O\x08")
        cpu.XMM1 = 0xFFFFFFFF00FFFFFF2E325F4342494C47
        cpu.RDI = 0x7FFFF7A248CE
        cpu.RIP = 0x7FFFF7DF294E
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7A248D6:0x7FFFF7A248DE], [b"2", b".", b"5", b"\x00", b"G", b"L", b"I", b"B"]
        )
        self.assertEqual(
            mem[0x7FFFF7DF294E:0x7FFFF7DF2953], [b"f", b"\x0f", b"\x16", b"O", b"\x08"]
        )
        self.assertEqual(cpu.XMM1, 88109632480871197291218000195730623559)
        self.assertEqual(cpu.RDI, 140737347995854)
        self.assertEqual(cpu.RIP, 140737351985491)

    def test_MOVHPD_20(self):
        """ Instruction MOVHPD_20
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A24000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7A248B7, "-x86-64.")
        mem.write(0x7FFFF7DF294E, "f\x0f\x16O\x08")
        cpu.XMM1 = 0x78756E696C2D646C
        cpu.RDI = 0x7FFFF7A248AF
        cpu.RIP = 0x7FFFF7DF294E
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7A248B7:0x7FFFF7A248BF], [b"-", b"x", b"8", b"6", b"-", b"6", b"4", b"."]
        )
        self.assertEqual(
            mem[0x7FFFF7DF294E:0x7FFFF7DF2953], [b"f", b"\x0f", b"\x16", b"O", b"\x08"]
        )
        self.assertEqual(cpu.XMM1, 61415586074916309421369241318231729260)
        self.assertEqual(cpu.RDI, 140737347995823)
        self.assertEqual(cpu.RIP, 140737351985491)

    def test_MOVHPD_21(self):
        """ Instruction MOVHPD_21
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7B99000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7B99A30, "6\x00__vdso")
        mem.write(0x7FFFF7DF2953, "f\x0f\x16V\x08")
        cpu.XMM2 = 0x64765F5F00656D692E325F58554E494C
        cpu.RSI = 0x7FFFF7B99A28
        cpu.RIP = 0x7FFFF7DF2953
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7B99A30:0x7FFFF7B99A38], [b"6", b"\x00", b"_", b"_", b"v", b"d", b"s", b"o"]
        )
        self.assertEqual(
            mem[0x7FFFF7DF2953:0x7FFFF7DF2958], [b"f", b"\x0f", b"\x16", b"V", b"\x08"]
        )
        self.assertEqual(cpu.XMM2, 148143459290256633805182000720633547084)
        self.assertEqual(cpu.RSI, 140737349524008)
        self.assertEqual(cpu.RIP, 140737351985496)

    def test_MOVHPD_3(self):
        """ Instruction MOVHPD_3
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A24000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7A248D6, "2.5\x00GLIB")
        mem.write(0x7FFFF7DF294E, "f\x0f\x16O\x08")
        cpu.XMM1 = 0xFFFFFFFF00FFFFFF2E325F4342494C47
        cpu.RDI = 0x7FFFF7A248CE
        cpu.RIP = 0x7FFFF7DF294E
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7A248D6:0x7FFFF7A248DE], [b"2", b".", b"5", b"\x00", b"G", b"L", b"I", b"B"]
        )
        self.assertEqual(
            mem[0x7FFFF7DF294E:0x7FFFF7DF2953], [b"f", b"\x0f", b"\x16", b"O", b"\x08"]
        )
        self.assertEqual(cpu.XMM1, 88109632480871197291218000195730623559)
        self.assertEqual(cpu.RDI, 140737347995854)
        self.assertEqual(cpu.RIP, 140737351985491)

    def test_MOVHPD_4(self):
        """ Instruction MOVHPD_4
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A24000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7A248D6, "2.5\x00GLIB")
        mem.write(0x7FFFF7DF2953, "f\x0f\x16V\x08")
        cpu.XMM2 = 0x42494C4700352E322E325F4342494C47
        cpu.RSI = 0x7FFFF7A248CE
        cpu.RIP = 0x7FFFF7DF2953
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7A248D6:0x7FFFF7A248DE], [b"2", b".", b"5", b"\x00", b"G", b"L", b"I", b"B"]
        )
        self.assertEqual(
            mem[0x7FFFF7DF2953:0x7FFFF7DF2958], [b"f", b"\x0f", b"\x16", b"V", b"\x08"]
        )
        self.assertEqual(cpu.XMM2, 88109632480871197291218000195730623559)
        self.assertEqual(cpu.RSI, 140737347995854)
        self.assertEqual(cpu.RIP, 140737351985496)

    def test_MOVHPD_5(self):
        """ Instruction MOVHPD_5
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7FFA000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF294E, "f\x0f\x16O\x08")
        mem.write(0x7FFFF7FFA30C, "6\x00\x00\x00\x00\x00\x02\x00")
        cpu.XMM1 = 0xFFFFFFFF00FFFFFF2E325F58554E494C
        cpu.RDI = 0x7FFFF7FFA304
        cpu.RIP = 0x7FFFF7DF294E
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7DF294E:0x7FFFF7DF2953], [b"f", b"\x0f", b"\x16", b"O", b"\x08"]
        )
        self.assertEqual(
            mem[0x7FFFF7FFA30C:0x7FFFF7FFA314],
            [b"6", b"\x00", b"\x00", b"\x00", b"\x00", b"\x00", b"\x02", b"\x00"],
        )
        self.assertEqual(cpu.XMM1, 10384593717070654710068880547400012)
        self.assertEqual(cpu.RDI, 140737354113796)
        self.assertEqual(cpu.RIP, 140737351985491)

    def test_MOVHPD_6(self):
        """ Instruction MOVHPD_6
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A24000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7A248D6, "2.5\x00GLIB")
        mem.write(0x7FFFF7DF2953, "f\x0f\x16V\x08")
        cpu.XMM2 = 0x42494C4700352E322E325F4342494C47
        cpu.RSI = 0x7FFFF7A248CE
        cpu.RIP = 0x7FFFF7DF2953
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7A248D6:0x7FFFF7A248DE], [b"2", b".", b"5", b"\x00", b"G", b"L", b"I", b"B"]
        )
        self.assertEqual(
            mem[0x7FFFF7DF2953:0x7FFFF7DF2958], [b"f", b"\x0f", b"\x16", b"V", b"\x08"]
        )
        self.assertEqual(cpu.XMM2, 88109632480871197291218000195730623559)
        self.assertEqual(cpu.RSI, 140737347995854)
        self.assertEqual(cpu.RIP, 140737351985496)

    def test_MOVHPD_7(self):
        """ Instruction MOVHPD_7
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A24000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7A248D6, "2.5\x00GLIB")
        mem.write(0x7FFFF7DF2953, "f\x0f\x16V\x08")
        cpu.XMM2 = 0x42494C4700352E322E325F4342494C47
        cpu.RSI = 0x7FFFF7A248CE
        cpu.RIP = 0x7FFFF7DF2953
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7A248D6:0x7FFFF7A248DE], [b"2", b".", b"5", b"\x00", b"G", b"L", b"I", b"B"]
        )
        self.assertEqual(
            mem[0x7FFFF7DF2953:0x7FFFF7DF2958], [b"f", b"\x0f", b"\x16", b"V", b"\x08"]
        )
        self.assertEqual(cpu.XMM2, 88109632480871197291218000195730623559)
        self.assertEqual(cpu.RSI, 140737347995854)
        self.assertEqual(cpu.RIP, 140737351985496)

    def test_MOVHPD_8(self):
        """ Instruction MOVHPD_8
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7FF7000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF2953, "f\x0f\x16V\x08")
        mem.write(0x7FFFF7FF74A8, "_64-linu")
        cpu.XMM2 = 0x3638782F62696C2F
        cpu.RSI = 0x7FFFF7FF74A0
        cpu.RIP = 0x7FFFF7DF2953
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7DF2953:0x7FFFF7DF2958], [b"f", b"\x0f", b"\x16", b"V", b"\x08"]
        )
        self.assertEqual(
            mem[0x7FFFF7FF74A8:0x7FFFF7FF74B0], [b"_", b"6", b"4", b"-", b"l", b"i", b"n", b"u"]
        )
        self.assertEqual(cpu.XMM2, 156092966384913869483545010807748783151)
        self.assertEqual(cpu.RSI, 140737354101920)
        self.assertEqual(cpu.RIP, 140737351985496)

    def test_MOVHPD_9(self):
        """ Instruction MOVHPD_9
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A21000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7A21315, "emalign\x00")
        mem.write(0x7FFFF7DF294E, "f\x0f\x16O\x08")
        cpu.XMM1 = 0xFFFFFFFF00FFFFFF6D5F6362696C5F5F
        cpu.RDI = 0x7FFFF7A2130D
        cpu.RIP = 0x7FFFF7DF294E
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7A21315:0x7FFFF7A2131D], [b"e", b"m", b"a", b"l", b"i", b"g", b"n", b"\x00"]
        )
        self.assertEqual(
            mem[0x7FFFF7DF294E:0x7FFFF7DF2953], [b"f", b"\x0f", b"\x16", b"O", b"\x08"]
        )
        self.assertEqual(cpu.XMM1, 573250095127234633104266320675626847)
        self.assertEqual(cpu.RDI, 140737347982093)
        self.assertEqual(cpu.RIP, 140737351985491)

    def test_PSLLDQ_1(self):
        """ Instruction PSLLDQ_1
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3470, "f\x0fs\xfa\x07")
        cpu.XMM2 = 0x1
        cpu.RIP = 0x7FFFF7DF3470
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7DF3470:0x7FFFF7DF3475], [b"f", b"\x0f", b"s", b"\xfa", b"\x07"]
        )
        self.assertEqual(cpu.XMM2, 72057594037927936)
        self.assertEqual(cpu.RIP, 140737351988341)

    def test_PSLLDQ_10(self):
        """ Instruction PSLLDQ_10
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3470, "f\x0fs\xfa\x07")
        cpu.XMM2 = 0x6972705F5F00362E6F732E6362696C00
        cpu.RIP = 0x7FFFF7DF3470
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7DF3470:0x7FFFF7DF3475], [b"f", b"\x0f", b"s", b"\xfa", b"\x07"]
        )
        self.assertEqual(cpu.XMM2, 61723168909761380161964749838612430848)
        self.assertEqual(cpu.RIP, 140737351988341)

    def test_PSLLDQ_11(self):
        """ Instruction PSLLDQ_11
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3470, "f\x0fs\xfa\x07")
        cpu.XMM2 = 0x6972705F5F00362E6F732E6362696C00
        cpu.RIP = 0x7FFFF7DF3470
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7DF3470:0x7FFFF7DF3475], [b"f", b"\x0f", b"s", b"\xfa", b"\x07"]
        )
        self.assertEqual(cpu.XMM2, 61723168909761380161964749838612430848)
        self.assertEqual(cpu.RIP, 140737351988341)

    def test_PSLLDQ_12(self):
        """ Instruction PSLLDQ_12
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3470, "f\x0fs\xfa\x07")
        cpu.XMM2 = 0x6972705F5F00362E6F732E6362696C00
        cpu.RIP = 0x7FFFF7DF3470
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7DF3470:0x7FFFF7DF3475], [b"f", b"\x0f", b"s", b"\xfa", b"\x07"]
        )
        self.assertEqual(cpu.XMM2, 61723168909761380161964749838612430848)
        self.assertEqual(cpu.RIP, 140737351988341)

    def test_PSLLDQ_13(self):
        """ Instruction PSLLDQ_13
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3470, "f\x0fs\xfa\x07")
        cpu.XMM2 = 0x1
        cpu.RIP = 0x7FFFF7DF3470
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7DF3470:0x7FFFF7DF3475], [b"f", b"\x0f", b"s", b"\xfa", b"\x07"]
        )
        self.assertEqual(cpu.XMM2, 72057594037927936)
        self.assertEqual(cpu.RIP, 140737351988341)

    def test_PSLLDQ_14(self):
        """ Instruction PSLLDQ_14
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3470, "f\x0fs\xfa\x07")
        cpu.XMM2 = 0x6972705F5F00362E6F732E6362696C00
        cpu.RIP = 0x7FFFF7DF3470
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7DF3470:0x7FFFF7DF3475], [b"f", b"\x0f", b"s", b"\xfa", b"\x07"]
        )
        self.assertEqual(cpu.XMM2, 61723168909761380161964749838612430848)
        self.assertEqual(cpu.RIP, 140737351988341)

    def test_PSLLDQ_15(self):
        """ Instruction PSLLDQ_15
            Groups: sse2
            0x7ffff7df389d:	pslldq	xmm2, 4
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF389D, "f\x0fs\xfa\x04")
        cpu.XMM2 = 0x3000000020002000000352E322E32
        cpu.RIP = 0x7FFFF7DF389D
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7DF389D:0x7FFFF7DF38A2], [b"f", b"\x0f", b"s", b"\xfa", b"\x04"]
        )
        self.assertEqual(cpu.XMM2, 10384752173395664791945953216036864)
        self.assertEqual(cpu.RIP, 140737351989410)

    def test_PSLLDQ_16(self):
        """ Instruction PSLLDQ_16
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3470, "f\x0fs\xfa\x07")
        cpu.XMM2 = 0x6972705F5F00362E6F732E6362696C00
        cpu.RIP = 0x7FFFF7DF3470
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7DF3470:0x7FFFF7DF3475], [b"f", b"\x0f", b"s", b"\xfa", b"\x07"]
        )
        self.assertEqual(cpu.XMM2, 61723168909761380161964749838612430848)
        self.assertEqual(cpu.RIP, 140737351988341)

    def test_PSLLDQ_17(self):
        """ Instruction PSLLDQ_17
            Groups: sse2
            0x7ffff7df39dd:	pslldq	xmm2, 3
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF39DD, "f\x0fs\xfa\x03")
        cpu.XMM2 = 0x494C4700352E322E325F4342494C4700
        cpu.RIP = 0x7FFFF7DF39DD
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7DF39DD:0x7FFFF7DF39E2], [b"f", b"\x0f", b"s", b"\xfa", b"\x03"]
        )
        self.assertEqual(cpu.XMM2, 276128700049446162655260478745346048)
        self.assertEqual(cpu.RIP, 140737351989730)

    def test_PSLLDQ_18(self):
        """ Instruction PSLLDQ_18
            Groups: sse2
            0x7ffff7df389d:	pslldq	xmm2, 4
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF389D, "f\x0fs\xfa\x04")
        cpu.XMM2 = 0x665F4F495F006F6C6C657466006B6863
        cpu.RIP = 0x7FFFF7DF389D
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7DF389D:0x7FFFF7DF38A2], [b"f", b"\x0f", b"s", b"\xfa", b"\x04"]
        )
        self.assertEqual(cpu.XMM2, 126278919537221597046423674937331941376)
        self.assertEqual(cpu.RIP, 140737351989410)

    def test_PSLLDQ_19(self):
        """ Instruction PSLLDQ_19
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3470, "f\x0fs\xfa\x07")
        cpu.XMM2 = 0x1
        cpu.RIP = 0x7FFFF7DF3470
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7DF3470:0x7FFFF7DF3475], [b"f", b"\x0f", b"s", b"\xfa", b"\x07"]
        )
        self.assertEqual(cpu.XMM2, 72057594037927936)
        self.assertEqual(cpu.RIP, 140737351988341)

    def test_PSLLDQ_2(self):
        """ Instruction PSLLDQ_2
            Groups: sse2
            0x7ffff7df2f70:	pslldq	xmm2, 0xb
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF2F70, "f\x0fs\xfa\x0b")
        cpu.XMM2 = 0x6972705F5F00362E6F732E6362696C00
        cpu.RIP = 0x7FFFF7DF2F70
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7DF2F70:0x7FFFF7DF2F75], [b"f", b"\x0f", b"s", b"\xfa", b"\x0b"]
        )
        self.assertEqual(cpu.XMM2, 132104554884493019491015862172149350400)
        self.assertEqual(cpu.RIP, 140737351987061)

    def test_PSLLDQ_20(self):
        """ Instruction PSLLDQ_20
            Groups: sse2
            0x7ffff7df3970:	pslldq	xmm2, 3
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3970, "f\x0fs\xfa\x03")
        cpu.XMM2 = 0x322E6F732E34362D3638782D78756E69
        cpu.RIP = 0x7FFFF7DF3970
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7DF3970:0x7FFFF7DF3975], [b"f", b"\x0f", b"s", b"\xfa", b"\x03"]
        )
        self.assertEqual(cpu.XMM2, 153101124148370467217615035531131879424)
        self.assertEqual(cpu.RIP, 140737351989621)

    def test_PSLLDQ_21(self):
        """ Instruction PSLLDQ_21
            Groups: sse2
            0x7ffff7df3830:	pslldq	xmm2, 4
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3830, "f\x0fs\xfa\x04")
        cpu.XMM2 = 0x5F4342494C4700342E332E325F434249
        cpu.RIP = 0x7FFFF7DF3830
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7DF3830:0x7FFFF7DF3835], [b"f", b"\x0f", b"s", b"\xfa", b"\x04"]
        )
        self.assertEqual(cpu.XMM2, 101389984890772213670702594761716400128)
        self.assertEqual(cpu.RIP, 140737351989301)

    def test_PSLLDQ_3(self):
        """ Instruction PSLLDQ_3
            Groups: sse2
            0x7ffff7df3ab0:	pslldq	xmm2, 2
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3AB0, "f\x0fs\xfa\x02")
        cpu.XMM2 = 0x63007463656A626F5F726F665F6F7364
        cpu.RIP = 0x7FFFF7DF3AB0
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7DF3AB0:0x7FFFF7DF3AB5], [b"f", b"\x0f", b"s", b"\xfa", b"\x02"]
        )
        self.assertEqual(cpu.XMM2, 154706541852064556987039687627872927744)
        self.assertEqual(cpu.RIP, 140737351989941)

    def test_PSLLDQ_4(self):
        """ Instruction PSLLDQ_4
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3470, "f\x0fs\xfa\x07")
        cpu.XMM2 = 0x6972705F5F00362E6F732E6362696C00
        cpu.RIP = 0x7FFFF7DF3470
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7DF3470:0x7FFFF7DF3475], [b"f", b"\x0f", b"s", b"\xfa", b"\x07"]
        )
        self.assertEqual(cpu.XMM2, 61723168909761380161964749838612430848)
        self.assertEqual(cpu.RIP, 140737351988341)

    def test_PSLLDQ_5(self):
        """ Instruction PSLLDQ_5
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3470, "f\x0fs\xfa\x07")
        cpu.XMM2 = 0x6972705F5F00362E6F732E6362696C00
        cpu.RIP = 0x7FFFF7DF3470
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7DF3470:0x7FFFF7DF3475], [b"f", b"\x0f", b"s", b"\xfa", b"\x07"]
        )
        self.assertEqual(cpu.XMM2, 61723168909761380161964749838612430848)
        self.assertEqual(cpu.RIP, 140737351988341)

    def test_PSLLDQ_6(self):
        """ Instruction PSLLDQ_6
            Groups: sse2
            0x7ffff7df389d:	pslldq	xmm2, 4
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF389D, "f\x0fs\xfa\x04")
        cpu.XMM2 = 0x3000000020002000000352E322E32
        cpu.RIP = 0x7FFFF7DF389D
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7DF389D:0x7FFFF7DF38A2], [b"f", b"\x0f", b"s", b"\xfa", b"\x04"]
        )
        self.assertEqual(cpu.XMM2, 10384752173395664791945953216036864)
        self.assertEqual(cpu.RIP, 140737351989410)

    def test_PSLLDQ_7(self):
        """ Instruction PSLLDQ_7
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3470, "f\x0fs\xfa\x07")
        cpu.XMM2 = 0x1
        cpu.RIP = 0x7FFFF7DF3470
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7DF3470:0x7FFFF7DF3475], [b"f", b"\x0f", b"s", b"\xfa", b"\x07"]
        )
        self.assertEqual(cpu.XMM2, 72057594037927936)
        self.assertEqual(cpu.RIP, 140737351988341)

    def test_PSLLDQ_8(self):
        """ Instruction PSLLDQ_8
            Groups: sse2
            0x7ffff7df39dd:	pslldq	xmm2, 3
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF39DD, "f\x0fs\xfa\x03")
        cpu.XMM2 = 0x7461636F6C6C6165645F6C645F00636F
        cpu.RIP = 0x7FFFF7DF39DD
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7DF39DD:0x7FFFF7DF39E2], [b"f", b"\x0f", b"s", b"\xfa", b"\x03"]
        )
        self.assertEqual(cpu.XMM2, 148107273809595710738464457560820809728)
        self.assertEqual(cpu.RIP, 140737351989730)

    def test_PSLLDQ_9(self):
        """ Instruction PSLLDQ_9
            Groups: sse2
            0x7ffff7df3c5d:	pslldq	xmm2, 1
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3C5D, "f\x0fs\xfa\x01")
        cpu.XMM2 = 0x68252E7568254D00796164666F656D69
        cpu.RIP = 0x7FFFF7DF3C5D
        cpu.execute()

        self.assertEqual(
            mem[0x7FFFF7DF3C5D:0x7FFFF7DF3C62], [b"f", b"\x0f", b"s", b"\xfa", b"\x01"]
        )
        self.assertEqual(cpu.XMM2, 49422662792731052987857949274592340224)
        self.assertEqual(cpu.RIP, 140737351990370)

    def test_MOVHPD_1_symbolic(self):
        """ Instruction MOVHPD_1
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A24000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF294E, "f\x0f\x16")
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A249D1)
        value = cs.new_bitvec(8)
        cs.add(value == 0x49)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A249D2)
        value = cs.new_bitvec(8)
        cs.add(value == 0x56)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A249D3)
        value = cs.new_bitvec(8)
        cs.add(value == 0x41)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A249D4)
        value = cs.new_bitvec(8)
        cs.add(value == 0x54)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A249D5)
        value = cs.new_bitvec(8)
        cs.add(value == 0x45)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A249D6)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A249D7)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A249D8)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        mem.write(0x7FFFF7DF2951, "O\x08")
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xFFFFFFFFFFFF00FF52505F4342494C47)
        cpu.RDI = cs.new_bitvec(64)
        cs.add(cpu.RDI == 0x7FFFF7A249C9)
        cpu.RIP = 0x7FFFF7DF294E

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF294E, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF294F, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2950, 8) == ord("\x16"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2951, 8) == ord("O"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2952, 8) == ord("\x08"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A249D3, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A249D4, 8) == ord("T"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A249D5, 8) == ord("E"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A249D6, 8) == ord("\x00"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A249D7, 8) == ord("\x00"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A249D8, 8) == ord("\x00"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A249D1, 8) == ord("I"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A249D2, 8) == ord("V"))
        condition = Operators.AND(condition, cpu.XMM1 == 0x455441564952505F4342494C47)
        condition = Operators.AND(condition, cpu.RDI == 0x7FFFF7A249C9)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF2953)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_MOVHPD_10_symbolic(self):
        """ Instruction MOVHPD_10
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A24000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF294E, "f\x0f\x16O\x08")
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D6)
        value = cs.new_bitvec(8)
        cs.add(value == 0x32)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D7)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2E)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D8)
        value = cs.new_bitvec(8)
        cs.add(value == 0x35)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D9)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DA)
        value = cs.new_bitvec(8)
        cs.add(value == 0x47)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DB)
        value = cs.new_bitvec(8)
        cs.add(value == 0x4C)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DC)
        value = cs.new_bitvec(8)
        cs.add(value == 0x49)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DD)
        value = cs.new_bitvec(8)
        cs.add(value == 0x42)
        mem[addr] = value
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xFFFFFFFF00FFFFFF2E325F4342494C47)
        cpu.RDI = cs.new_bitvec(64)
        cs.add(cpu.RDI == 0x7FFFF7A248CE)
        cpu.RIP = 0x7FFFF7DF294E

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF294E, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF294F, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2950, 8) == ord("\x16"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2951, 8) == ord("O"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2952, 8) == ord("\x08"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D6, 8) == ord("2"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D7, 8) == ord("."))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D8, 8) == ord("5"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D9, 8) == ord("\x00"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DA, 8) == ord("G"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DB, 8) == ord("L"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DC, 8) == ord("I"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DD, 8) == ord("B"))
        condition = Operators.AND(condition, cpu.XMM1 == 0x42494C4700352E322E325F4342494C47)
        condition = Operators.AND(condition, cpu.RDI == 0x7FFFF7A248CE)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF2953)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_MOVHPD_11_symbolic(self):
        """ Instruction MOVHPD_11
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A24000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF2953, "f\x0f\x16V\x08")
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D6)
        value = cs.new_bitvec(8)
        cs.add(value == 0x32)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D7)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2E)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D8)
        value = cs.new_bitvec(8)
        cs.add(value == 0x35)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D9)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DA)
        value = cs.new_bitvec(8)
        cs.add(value == 0x47)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DB)
        value = cs.new_bitvec(8)
        cs.add(value == 0x4C)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DC)
        value = cs.new_bitvec(8)
        cs.add(value == 0x49)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DD)
        value = cs.new_bitvec(8)
        cs.add(value == 0x42)
        mem[addr] = value
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x42494C4700352E322E325F4342494C47)
        cpu.RSI = cs.new_bitvec(64)
        cs.add(cpu.RSI == 0x7FFFF7A248CE)
        cpu.RIP = 0x7FFFF7DF2953

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2956, 8) == ord("V"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D7, 8) == ord("."))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2953, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2954, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2955, 8) == ord("\x16"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D6, 8) == ord("2"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2957, 8) == ord("\x08"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D8, 8) == ord("5"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D9, 8) == ord("\x00"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DA, 8) == ord("G"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DB, 8) == ord("L"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DC, 8) == ord("I"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DD, 8) == ord("B"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x42494C4700352E322E325F4342494C47)
        condition = Operators.AND(condition, cpu.RSI == 0x7FFFF7A248CE)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF2958)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_MOVHPD_12_symbolic(self):
        """ Instruction MOVHPD_12
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A24000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF294E, "f\x0f\x16O\x08")
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D6)
        value = cs.new_bitvec(8)
        cs.add(value == 0x32)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D7)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2E)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D8)
        value = cs.new_bitvec(8)
        cs.add(value == 0x35)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D9)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DA)
        value = cs.new_bitvec(8)
        cs.add(value == 0x47)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DB)
        value = cs.new_bitvec(8)
        cs.add(value == 0x4C)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DC)
        value = cs.new_bitvec(8)
        cs.add(value == 0x49)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DD)
        value = cs.new_bitvec(8)
        cs.add(value == 0x42)
        mem[addr] = value
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xFFFFFFFF00FFFFFF2E325F4342494C47)
        cpu.RDI = cs.new_bitvec(64)
        cs.add(cpu.RDI == 0x7FFFF7A248CE)
        cpu.RIP = 0x7FFFF7DF294E

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF294E, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF294F, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2950, 8) == ord("\x16"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2951, 8) == ord("O"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2952, 8) == ord("\x08"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D6, 8) == ord("2"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D7, 8) == ord("."))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D8, 8) == ord("5"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D9, 8) == ord("\x00"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DA, 8) == ord("G"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DB, 8) == ord("L"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DC, 8) == ord("I"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DD, 8) == ord("B"))
        condition = Operators.AND(condition, cpu.XMM1 == 0x42494C4700352E322E325F4342494C47)
        condition = Operators.AND(condition, cpu.RDI == 0x7FFFF7A248CE)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF2953)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_MOVHPD_13_symbolic(self):
        """ Instruction MOVHPD_13
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A21000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF294E, "f\x0f\x16O\x08")
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A218DA)
        value = cs.new_bitvec(8)
        cs.add(value == 0x74)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A218DB)
        value = cs.new_bitvec(8)
        cs.add(value == 0x61)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A218DC)
        value = cs.new_bitvec(8)
        cs.add(value == 0x72)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A218DD)
        value = cs.new_bitvec(8)
        cs.add(value == 0x74)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A218DE)
        value = cs.new_bitvec(8)
        cs.add(value == 0x5F)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A218DF)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6D)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A218E0)
        value = cs.new_bitvec(8)
        cs.add(value == 0x61)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A218E1)
        value = cs.new_bitvec(8)
        cs.add(value == 0x69)
        mem[addr] = value
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x735F6362696C5F5F)
        cpu.RDI = cs.new_bitvec(64)
        cs.add(cpu.RDI == 0x7FFFF7A218D2)
        cpu.RIP = 0x7FFFF7DF294E

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF294E, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF294F, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2950, 8) == ord("\x16"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2951, 8) == ord("O"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2952, 8) == ord("\x08"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A218DA, 8) == ord("t"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A218DB, 8) == ord("a"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A218DC, 8) == ord("r"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A218DD, 8) == ord("t"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A218DE, 8) == ord("_"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A218DF, 8) == ord("m"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A218E0, 8) == ord("a"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A218E1, 8) == ord("i"))
        condition = Operators.AND(condition, cpu.XMM1 == 0x69616D5F74726174735F6362696C5F5F)
        condition = Operators.AND(condition, cpu.RDI == 0x7FFFF7A218D2)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF2953)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_MOVHPD_14_symbolic(self):
        """ Instruction MOVHPD_14
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A20000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF2953, "f\x0f\x16V\x08")
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A20A9B)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A20A9C)
        value = cs.new_bitvec(8)
        cs.add(value == 0x61)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A20A9D)
        value = cs.new_bitvec(8)
        cs.add(value == 0x63)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A20A9E)
        value = cs.new_bitvec(8)
        cs.add(value == 0x63)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A20A9F)
        value = cs.new_bitvec(8)
        cs.add(value == 0x74)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A20AA0)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A20AA1)
        value = cs.new_bitvec(8)
        cs.add(value == 0x5F)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A20AA2)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6E)
        mem[addr] = value
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x36766772615F6C645F)
        cpu.RSI = cs.new_bitvec(64)
        cs.add(cpu.RSI == 0x7FFFF7A20A93)
        cpu.RIP = 0x7FFFF7DF2953

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2953, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2954, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2955, 8) == ord("\x16"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2956, 8) == ord("V"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2957, 8) == ord("\x08"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A20A9B, 8) == ord("\x00"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A20A9C, 8) == ord("a"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A20A9D, 8) == ord("c"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A20A9E, 8) == ord("c"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A20A9F, 8) == ord("t"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A20AA0, 8) == ord("\x00"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A20AA1, 8) == ord("_"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A20AA2, 8) == ord("n"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x6E5F007463636100766772615F6C645F)
        condition = Operators.AND(condition, cpu.RSI == 0x7FFFF7A20A93)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF2958)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_MOVHPD_15_symbolic(self):
        """ Instruction MOVHPD_15
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A23000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF2953, "f\x0f\x16V\x08")
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A232EE)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6E)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A232EF)
        value = cs.new_bitvec(8)
        cs.add(value == 0x61)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A232F0)
        value = cs.new_bitvec(8)
        cs.add(value == 0x62)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A232F1)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6C)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A232F2)
        value = cs.new_bitvec(8)
        cs.add(value == 0x65)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A232F3)
        value = cs.new_bitvec(8)
        cs.add(value == 0x5F)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A232F4)
        value = cs.new_bitvec(8)
        cs.add(value == 0x73)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A232F5)
        value = cs.new_bitvec(8)
        cs.add(value == 0x65)
        mem[addr] = value
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x36655F6362696C5F5F)
        cpu.RSI = cs.new_bitvec(64)
        cs.add(cpu.RSI == 0x7FFFF7A232E6)
        cpu.RIP = 0x7FFFF7DF2953

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2953, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2954, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2955, 8) == ord("\x16"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2956, 8) == ord("V"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2957, 8) == ord("\x08"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A232EE, 8) == ord("n"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A232EF, 8) == ord("a"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A232F0, 8) == ord("b"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A232F1, 8) == ord("l"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A232F2, 8) == ord("e"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A232F3, 8) == ord("_"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A232F4, 8) == ord("s"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A232F5, 8) == ord("e"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x65735F656C62616E655F6362696C5F5F)
        condition = Operators.AND(condition, cpu.RSI == 0x7FFFF7A232E6)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF2958)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_MOVHPD_16_symbolic(self):
        """ Instruction MOVHPD_16
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A24000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF2953, "f\x0f\x16V\x08")
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D6)
        value = cs.new_bitvec(8)
        cs.add(value == 0x32)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D7)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2E)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D8)
        value = cs.new_bitvec(8)
        cs.add(value == 0x35)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D9)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DA)
        value = cs.new_bitvec(8)
        cs.add(value == 0x47)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DB)
        value = cs.new_bitvec(8)
        cs.add(value == 0x4C)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DC)
        value = cs.new_bitvec(8)
        cs.add(value == 0x49)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DD)
        value = cs.new_bitvec(8)
        cs.add(value == 0x42)
        mem[addr] = value
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x42494C4700352E322E325F4342494C47)
        cpu.RSI = cs.new_bitvec(64)
        cs.add(cpu.RSI == 0x7FFFF7A248CE)
        cpu.RIP = 0x7FFFF7DF2953

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2956, 8) == ord("V"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D7, 8) == ord("."))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2953, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2954, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2955, 8) == ord("\x16"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D6, 8) == ord("2"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2957, 8) == ord("\x08"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D8, 8) == ord("5"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D9, 8) == ord("\x00"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DA, 8) == ord("G"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DB, 8) == ord("L"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DC, 8) == ord("I"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DD, 8) == ord("B"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x42494C4700352E322E325F4342494C47)
        condition = Operators.AND(condition, cpu.RSI == 0x7FFFF7A248CE)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF2958)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_MOVHPD_17_symbolic(self):
        """ Instruction MOVHPD_17
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DD7000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF294E, "f\x0f\x16O\x08")
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7DD7671)
        value = cs.new_bitvec(8)
        cs.add(value == 0x5F)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7DD7672)
        value = cs.new_bitvec(8)
        cs.add(value == 0x64)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7DD7673)
        value = cs.new_bitvec(8)
        cs.add(value == 0x73)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7DD7674)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6F)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7DD7675)
        value = cs.new_bitvec(8)
        cs.add(value == 0x5F)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7DD7676)
        value = cs.new_bitvec(8)
        cs.add(value == 0x66)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7DD7677)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6F)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7DD7678)
        value = cs.new_bitvec(8)
        cs.add(value == 0x72)
        mem[addr] = value
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x646E69665F6C645F)
        cpu.RDI = cs.new_bitvec(64)
        cs.add(cpu.RDI == 0x7FFFF7DD7669)
        cpu.RIP = 0x7FFFF7DF294E

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF294E, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF294F, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2950, 8) == ord("\x16"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2951, 8) == ord("O"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2952, 8) == ord("\x08"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DD7671, 8) == ord("_"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DD7672, 8) == ord("d"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DD7673, 8) == ord("s"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DD7674, 8) == ord("o"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DD7675, 8) == ord("_"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DD7676, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DD7677, 8) == ord("o"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DD7678, 8) == ord("r"))
        condition = Operators.AND(condition, cpu.XMM1 == 0x726F665F6F73645F646E69665F6C645F)
        condition = Operators.AND(condition, cpu.RDI == 0x7FFFF7DD7669)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF2953)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_MOVHPD_18_symbolic(self):
        """ Instruction MOVHPD_18
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A24000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF2953, "f\x0f\x16V\x08")
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D6)
        value = cs.new_bitvec(8)
        cs.add(value == 0x32)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D7)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2E)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D8)
        value = cs.new_bitvec(8)
        cs.add(value == 0x35)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D9)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DA)
        value = cs.new_bitvec(8)
        cs.add(value == 0x47)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DB)
        value = cs.new_bitvec(8)
        cs.add(value == 0x4C)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DC)
        value = cs.new_bitvec(8)
        cs.add(value == 0x49)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DD)
        value = cs.new_bitvec(8)
        cs.add(value == 0x42)
        mem[addr] = value
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x42494C4700352E322E325F4342494C47)
        cpu.RSI = cs.new_bitvec(64)
        cs.add(cpu.RSI == 0x7FFFF7A248CE)
        cpu.RIP = 0x7FFFF7DF2953

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2956, 8) == ord("V"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D7, 8) == ord("."))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2953, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2954, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2955, 8) == ord("\x16"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D6, 8) == ord("2"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2957, 8) == ord("\x08"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D8, 8) == ord("5"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D9, 8) == ord("\x00"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DA, 8) == ord("G"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DB, 8) == ord("L"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DC, 8) == ord("I"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DD, 8) == ord("B"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x42494C4700352E322E325F4342494C47)
        condition = Operators.AND(condition, cpu.RSI == 0x7FFFF7A248CE)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF2958)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_MOVHPD_19_symbolic(self):
        """ Instruction MOVHPD_19
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DD7000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF294E, "f\x0f")
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7DD7750)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6F)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7DD7751)
        value = cs.new_bitvec(8)
        cs.add(value == 0x62)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7DD7752)
        value = cs.new_bitvec(8)
        cs.add(value == 0x61)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7DD7753)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6C)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7DD7754)
        value = cs.new_bitvec(8)
        cs.add(value == 0x5F)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7DD7755)
        value = cs.new_bitvec(8)
        cs.add(value == 0x72)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7DD7756)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6F)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7DD7757)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        mem.write(0x7FFFF7DF2950, "\x16O\x08")
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6C675F646C74725F)
        cpu.RDI = cs.new_bitvec(64)
        cs.add(cpu.RDI == 0x7FFFF7DD7748)
        cpu.RIP = 0x7FFFF7DF294E

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF294E, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF294F, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2950, 8) == ord("\x16"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2951, 8) == ord("O"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2952, 8) == ord("\x08"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DD7753, 8) == ord("l"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DD7754, 8) == ord("_"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DD7755, 8) == ord("r"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DD7756, 8) == ord("o"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DD7757, 8) == ord("\x00"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DD7750, 8) == ord("o"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DD7751, 8) == ord("b"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DD7752, 8) == ord("a"))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6F725F6C61626F6C675F646C74725F)
        condition = Operators.AND(condition, cpu.RDI == 0x7FFFF7DD7748)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF2953)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_MOVHPD_2_symbolic(self):
        """ Instruction MOVHPD_2
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A24000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF294E, "f\x0f\x16O\x08")
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D6)
        value = cs.new_bitvec(8)
        cs.add(value == 0x32)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D7)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2E)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D8)
        value = cs.new_bitvec(8)
        cs.add(value == 0x35)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D9)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DA)
        value = cs.new_bitvec(8)
        cs.add(value == 0x47)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DB)
        value = cs.new_bitvec(8)
        cs.add(value == 0x4C)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DC)
        value = cs.new_bitvec(8)
        cs.add(value == 0x49)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DD)
        value = cs.new_bitvec(8)
        cs.add(value == 0x42)
        mem[addr] = value
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xFFFFFFFF00FFFFFF2E325F4342494C47)
        cpu.RDI = cs.new_bitvec(64)
        cs.add(cpu.RDI == 0x7FFFF7A248CE)
        cpu.RIP = 0x7FFFF7DF294E

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF294E, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF294F, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2950, 8) == ord("\x16"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2951, 8) == ord("O"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2952, 8) == ord("\x08"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D6, 8) == ord("2"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D7, 8) == ord("."))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D8, 8) == ord("5"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D9, 8) == ord("\x00"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DA, 8) == ord("G"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DB, 8) == ord("L"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DC, 8) == ord("I"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DD, 8) == ord("B"))
        condition = Operators.AND(condition, cpu.XMM1 == 0x42494C4700352E322E325F4342494C47)
        condition = Operators.AND(condition, cpu.RDI == 0x7FFFF7A248CE)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF2953)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_MOVHPD_20_symbolic(self):
        """ Instruction MOVHPD_20
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A24000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF294E, "f\x0f\x16O\x08")
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248B7)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2D)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248B8)
        value = cs.new_bitvec(8)
        cs.add(value == 0x78)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248B9)
        value = cs.new_bitvec(8)
        cs.add(value == 0x38)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248BA)
        value = cs.new_bitvec(8)
        cs.add(value == 0x36)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248BB)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2D)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248BC)
        value = cs.new_bitvec(8)
        cs.add(value == 0x36)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248BD)
        value = cs.new_bitvec(8)
        cs.add(value == 0x34)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248BE)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2E)
        mem[addr] = value
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x78756E696C2D646C)
        cpu.RDI = cs.new_bitvec(64)
        cs.add(cpu.RDI == 0x7FFFF7A248AF)
        cpu.RIP = 0x7FFFF7DF294E

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF294E, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF294F, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2950, 8) == ord("\x16"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2951, 8) == ord("O"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2952, 8) == ord("\x08"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248B7, 8) == ord("-"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248B8, 8) == ord("x"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248B9, 8) == ord("8"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248BA, 8) == ord("6"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248BB, 8) == ord("-"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248BC, 8) == ord("6"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248BD, 8) == ord("4"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248BE, 8) == ord("."))
        condition = Operators.AND(condition, cpu.XMM1 == 0x2E34362D3638782D78756E696C2D646C)
        condition = Operators.AND(condition, cpu.RDI == 0x7FFFF7A248AF)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF2953)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_MOVHPD_21_symbolic(self):
        """ Instruction MOVHPD_21
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7B99000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF2953, "f\x0f\x16V\x08")
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7B99A30)
        value = cs.new_bitvec(8)
        cs.add(value == 0x36)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7B99A31)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7B99A32)
        value = cs.new_bitvec(8)
        cs.add(value == 0x5F)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7B99A33)
        value = cs.new_bitvec(8)
        cs.add(value == 0x5F)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7B99A34)
        value = cs.new_bitvec(8)
        cs.add(value == 0x76)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7B99A35)
        value = cs.new_bitvec(8)
        cs.add(value == 0x64)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7B99A36)
        value = cs.new_bitvec(8)
        cs.add(value == 0x73)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7B99A37)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6F)
        mem[addr] = value
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x64765F5F00656D692E325F58554E494C)
        cpu.RSI = cs.new_bitvec(64)
        cs.add(cpu.RSI == 0x7FFFF7B99A28)
        cpu.RIP = 0x7FFFF7DF2953

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2953, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2954, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2955, 8) == ord("\x16"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2956, 8) == ord("V"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2957, 8) == ord("\x08"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7B99A30, 8) == ord("6"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7B99A31, 8) == ord("\x00"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7B99A32, 8) == ord("_"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7B99A33, 8) == ord("_"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7B99A34, 8) == ord("v"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7B99A35, 8) == ord("d"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7B99A36, 8) == ord("s"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7B99A37, 8) == ord("o"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x6F7364765F5F00362E325F58554E494C)
        condition = Operators.AND(condition, cpu.RSI == 0x7FFFF7B99A28)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF2958)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_MOVHPD_3_symbolic(self):
        """ Instruction MOVHPD_3
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A24000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF294E, "f\x0f\x16O\x08")
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D6)
        value = cs.new_bitvec(8)
        cs.add(value == 0x32)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D7)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2E)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D8)
        value = cs.new_bitvec(8)
        cs.add(value == 0x35)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D9)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DA)
        value = cs.new_bitvec(8)
        cs.add(value == 0x47)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DB)
        value = cs.new_bitvec(8)
        cs.add(value == 0x4C)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DC)
        value = cs.new_bitvec(8)
        cs.add(value == 0x49)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DD)
        value = cs.new_bitvec(8)
        cs.add(value == 0x42)
        mem[addr] = value
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xFFFFFFFF00FFFFFF2E325F4342494C47)
        cpu.RDI = cs.new_bitvec(64)
        cs.add(cpu.RDI == 0x7FFFF7A248CE)
        cpu.RIP = 0x7FFFF7DF294E

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF294E, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF294F, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2950, 8) == ord("\x16"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2951, 8) == ord("O"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2952, 8) == ord("\x08"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D6, 8) == ord("2"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D7, 8) == ord("."))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D8, 8) == ord("5"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D9, 8) == ord("\x00"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DA, 8) == ord("G"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DB, 8) == ord("L"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DC, 8) == ord("I"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DD, 8) == ord("B"))
        condition = Operators.AND(condition, cpu.XMM1 == 0x42494C4700352E322E325F4342494C47)
        condition = Operators.AND(condition, cpu.RDI == 0x7FFFF7A248CE)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF2953)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_MOVHPD_4_symbolic(self):
        """ Instruction MOVHPD_4
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A24000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF2953, "f\x0f\x16V\x08")
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D6)
        value = cs.new_bitvec(8)
        cs.add(value == 0x32)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D7)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2E)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D8)
        value = cs.new_bitvec(8)
        cs.add(value == 0x35)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D9)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DA)
        value = cs.new_bitvec(8)
        cs.add(value == 0x47)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DB)
        value = cs.new_bitvec(8)
        cs.add(value == 0x4C)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DC)
        value = cs.new_bitvec(8)
        cs.add(value == 0x49)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DD)
        value = cs.new_bitvec(8)
        cs.add(value == 0x42)
        mem[addr] = value
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x42494C4700352E322E325F4342494C47)
        cpu.RSI = cs.new_bitvec(64)
        cs.add(cpu.RSI == 0x7FFFF7A248CE)
        cpu.RIP = 0x7FFFF7DF2953

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2956, 8) == ord("V"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D7, 8) == ord("."))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2953, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2954, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2955, 8) == ord("\x16"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D6, 8) == ord("2"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2957, 8) == ord("\x08"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D8, 8) == ord("5"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D9, 8) == ord("\x00"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DA, 8) == ord("G"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DB, 8) == ord("L"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DC, 8) == ord("I"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DD, 8) == ord("B"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x42494C4700352E322E325F4342494C47)
        condition = Operators.AND(condition, cpu.RSI == 0x7FFFF7A248CE)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF2958)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_MOVHPD_5_symbolic(self):
        """ Instruction MOVHPD_5
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7FFA000, 0x1000, "rwx")
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7FFA30C)
        value = cs.new_bitvec(8)
        cs.add(value == 0x36)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7FFA30D)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7FFA30E)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        mem.write(0x7FFFF7DF294F, "\x0f")
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7FFA310)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7FFA311)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        mem.write(0x7FFFF7DF2952, "\x08")
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7FFA313)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        mem.write(0x7FFFF7DF294E, "f")
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7FFA30F)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        mem.write(0x7FFFF7DF2950, "\x16O")
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7FFA312)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2)
        mem[addr] = value
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xFFFFFFFF00FFFFFF2E325F58554E494C)
        cpu.RDI = cs.new_bitvec(64)
        cs.add(cpu.RDI == 0x7FFFF7FFA304)
        cpu.RIP = 0x7FFFF7DF294E

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7FFA30C, 8) == ord("6"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7FFA30D, 8) == ord("\x00"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7FFA30E, 8) == ord("\x00"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF294F, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2950, 8) == ord("\x16"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2951, 8) == ord("O"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2952, 8) == ord("\x08"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7FFA313, 8) == ord("\x00"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF294E, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7FFA30F, 8) == ord("\x00"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7FFA310, 8) == ord("\x00"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7FFA311, 8) == ord("\x00"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7FFA312, 8) == ord("\x02"))
        condition = Operators.AND(condition, cpu.XMM1 == 0x20000000000362E325F58554E494C)
        condition = Operators.AND(condition, cpu.RDI == 0x7FFFF7FFA304)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF2953)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_MOVHPD_6_symbolic(self):
        """ Instruction MOVHPD_6
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A24000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF2953, "f\x0f\x16V\x08")
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D6)
        value = cs.new_bitvec(8)
        cs.add(value == 0x32)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D7)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2E)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D8)
        value = cs.new_bitvec(8)
        cs.add(value == 0x35)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D9)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DA)
        value = cs.new_bitvec(8)
        cs.add(value == 0x47)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DB)
        value = cs.new_bitvec(8)
        cs.add(value == 0x4C)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DC)
        value = cs.new_bitvec(8)
        cs.add(value == 0x49)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DD)
        value = cs.new_bitvec(8)
        cs.add(value == 0x42)
        mem[addr] = value
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x42494C4700352E322E325F4342494C47)
        cpu.RSI = cs.new_bitvec(64)
        cs.add(cpu.RSI == 0x7FFFF7A248CE)
        cpu.RIP = 0x7FFFF7DF2953

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2956, 8) == ord("V"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D7, 8) == ord("."))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2953, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2954, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2955, 8) == ord("\x16"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D6, 8) == ord("2"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2957, 8) == ord("\x08"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D8, 8) == ord("5"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D9, 8) == ord("\x00"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DA, 8) == ord("G"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DB, 8) == ord("L"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DC, 8) == ord("I"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DD, 8) == ord("B"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x42494C4700352E322E325F4342494C47)
        condition = Operators.AND(condition, cpu.RSI == 0x7FFFF7A248CE)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF2958)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_MOVHPD_7_symbolic(self):
        """ Instruction MOVHPD_7
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A24000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF2953, "f\x0f\x16V\x08")
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D6)
        value = cs.new_bitvec(8)
        cs.add(value == 0x32)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D7)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2E)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D8)
        value = cs.new_bitvec(8)
        cs.add(value == 0x35)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248D9)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DA)
        value = cs.new_bitvec(8)
        cs.add(value == 0x47)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DB)
        value = cs.new_bitvec(8)
        cs.add(value == 0x4C)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DC)
        value = cs.new_bitvec(8)
        cs.add(value == 0x49)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A248DD)
        value = cs.new_bitvec(8)
        cs.add(value == 0x42)
        mem[addr] = value
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x42494C4700352E322E325F4342494C47)
        cpu.RSI = cs.new_bitvec(64)
        cs.add(cpu.RSI == 0x7FFFF7A248CE)
        cpu.RIP = 0x7FFFF7DF2953

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2956, 8) == ord("V"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D7, 8) == ord("."))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2953, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2954, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2955, 8) == ord("\x16"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D6, 8) == ord("2"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2957, 8) == ord("\x08"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D8, 8) == ord("5"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248D9, 8) == ord("\x00"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DA, 8) == ord("G"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DB, 8) == ord("L"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DC, 8) == ord("I"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A248DD, 8) == ord("B"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x42494C4700352E322E325F4342494C47)
        condition = Operators.AND(condition, cpu.RSI == 0x7FFFF7A248CE)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF2958)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_MOVHPD_8_symbolic(self):
        """ Instruction MOVHPD_8
            Groups: sse2
            0x7ffff7df2953:	movhpd	xmm2, qword ptr [rsi + 8]
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7FF7000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF2953, "f\x0f\x16V\x08")
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7FF74A8)
        value = cs.new_bitvec(8)
        cs.add(value == 0x5F)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7FF74A9)
        value = cs.new_bitvec(8)
        cs.add(value == 0x36)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7FF74AA)
        value = cs.new_bitvec(8)
        cs.add(value == 0x34)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7FF74AB)
        value = cs.new_bitvec(8)
        cs.add(value == 0x2D)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7FF74AC)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6C)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7FF74AD)
        value = cs.new_bitvec(8)
        cs.add(value == 0x69)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7FF74AE)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6E)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7FF74AF)
        value = cs.new_bitvec(8)
        cs.add(value == 0x75)
        mem[addr] = value
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x3638782F62696C2F)
        cpu.RSI = cs.new_bitvec(64)
        cs.add(cpu.RSI == 0x7FFFF7FF74A0)
        cpu.RIP = 0x7FFFF7DF2953

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2953, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2954, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2955, 8) == ord("\x16"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2956, 8) == ord("V"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2957, 8) == ord("\x08"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7FF74A8, 8) == ord("_"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7FF74A9, 8) == ord("6"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7FF74AA, 8) == ord("4"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7FF74AB, 8) == ord("-"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7FF74AC, 8) == ord("l"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7FF74AD, 8) == ord("i"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7FF74AE, 8) == ord("n"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7FF74AF, 8) == ord("u"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x756E696C2D34365F3638782F62696C2F)
        condition = Operators.AND(condition, cpu.RSI == 0x7FFFF7FF74A0)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF2958)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_MOVHPD_9_symbolic(self):
        """ Instruction MOVHPD_9
            Groups: sse2
            0x7ffff7df294e:	movhpd	xmm1, qword ptr [rdi + 8]
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7A21000, 0x1000, "rwx")
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF294E, "f\x0f\x16O\x08")
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A21315)
        value = cs.new_bitvec(8)
        cs.add(value == 0x65)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A21316)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6D)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A21317)
        value = cs.new_bitvec(8)
        cs.add(value == 0x61)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A21318)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6C)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A21319)
        value = cs.new_bitvec(8)
        cs.add(value == 0x69)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A2131A)
        value = cs.new_bitvec(8)
        cs.add(value == 0x67)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A2131B)
        value = cs.new_bitvec(8)
        cs.add(value == 0x6E)
        mem[addr] = value
        addr = cs.new_bitvec(64)
        cs.add(addr == 0x7FFFF7A2131C)
        value = cs.new_bitvec(8)
        cs.add(value == 0x0)
        mem[addr] = value
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xFFFFFFFF00FFFFFF6D5F6362696C5F5F)
        cpu.RDI = cs.new_bitvec(64)
        cs.add(cpu.RDI == 0x7FFFF7A2130D)
        cpu.RIP = 0x7FFFF7DF294E

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF294E, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF294F, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2950, 8) == ord("\x16"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2951, 8) == ord("O"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2952, 8) == ord("\x08"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A21315, 8) == ord("e"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A21316, 8) == ord("m"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A21317, 8) == ord("a"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A21318, 8) == ord("l"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A21319, 8) == ord("i"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A2131A, 8) == ord("g"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A2131B, 8) == ord("n"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7A2131C, 8) == ord("\x00"))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6E67696C616D656D5F6362696C5F5F)
        condition = Operators.AND(condition, cpu.RDI == 0x7FFFF7A2130D)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF2953)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PSLLDQ_1_symbolic(self):
        """ Instruction PSLLDQ_1
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3470, "f\x0fs\xfa\x07")
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x1)
        cpu.RIP = 0x7FFFF7DF3470

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3470, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3471, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3472, 8) == ord("s"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3473, 8) == ord("\xfa"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3474, 8) == ord("\x07"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x100000000000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF3475)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PSLLDQ_10_symbolic(self):
        """ Instruction PSLLDQ_10
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3470, "f\x0fs\xfa\x07")
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x6972705F5F00362E6F732E6362696C00)
        cpu.RIP = 0x7FFFF7DF3470

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3470, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3471, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3472, 8) == ord("s"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3473, 8) == ord("\xfa"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3474, 8) == ord("\x07"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x2E6F732E6362696C0000000000000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF3475)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PSLLDQ_11_symbolic(self):
        """ Instruction PSLLDQ_11
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3470, "f\x0fs\xfa\x07")
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x6972705F5F00362E6F732E6362696C00)
        cpu.RIP = 0x7FFFF7DF3470

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3470, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3471, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3472, 8) == ord("s"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3473, 8) == ord("\xfa"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3474, 8) == ord("\x07"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x2E6F732E6362696C0000000000000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF3475)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PSLLDQ_12_symbolic(self):
        """ Instruction PSLLDQ_12
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3470, "f\x0fs\xfa\x07")
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x6972705F5F00362E6F732E6362696C00)
        cpu.RIP = 0x7FFFF7DF3470

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3470, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3471, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3472, 8) == ord("s"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3473, 8) == ord("\xfa"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3474, 8) == ord("\x07"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x2E6F732E6362696C0000000000000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF3475)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PSLLDQ_13_symbolic(self):
        """ Instruction PSLLDQ_13
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3470, "f\x0fs\xfa\x07")
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x1)
        cpu.RIP = 0x7FFFF7DF3470

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3470, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3471, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3472, 8) == ord("s"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3473, 8) == ord("\xfa"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3474, 8) == ord("\x07"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x100000000000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF3475)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PSLLDQ_14_symbolic(self):
        """ Instruction PSLLDQ_14
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3470, "f\x0fs\xfa\x07")
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x6972705F5F00362E6F732E6362696C00)
        cpu.RIP = 0x7FFFF7DF3470

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3470, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3471, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3472, 8) == ord("s"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3473, 8) == ord("\xfa"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3474, 8) == ord("\x07"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x2E6F732E6362696C0000000000000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF3475)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PSLLDQ_15_symbolic(self):
        """ Instruction PSLLDQ_15
            Groups: sse2
            0x7ffff7df389d:	pslldq	xmm2, 4
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF389D, "f\x0fs\xfa\x04")
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x3000000020002000000352E322E32)
        cpu.RIP = 0x7FFFF7DF389D

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF38A0, 8) == ord("\xfa"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF38A1, 8) == ord("\x04"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF389D, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF389E, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF389F, 8) == ord("s"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x20002000000352E322E3200000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF38A2)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PSLLDQ_16_symbolic(self):
        """ Instruction PSLLDQ_16
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3470, "f\x0fs\xfa\x07")
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x6972705F5F00362E6F732E6362696C00)
        cpu.RIP = 0x7FFFF7DF3470

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3470, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3471, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3472, 8) == ord("s"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3473, 8) == ord("\xfa"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3474, 8) == ord("\x07"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x2E6F732E6362696C0000000000000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF3475)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PSLLDQ_17_symbolic(self):
        """ Instruction PSLLDQ_17
            Groups: sse2
            0x7ffff7df39dd:	pslldq	xmm2, 3
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF39DD, "f\x0fs\xfa\x03")
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x494C4700352E322E325F4342494C4700)
        cpu.RIP = 0x7FFFF7DF39DD

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF39E0, 8) == ord("\xfa"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF39E1, 8) == ord("\x03"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF39DD, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF39DE, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF39DF, 8) == ord("s"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x352E322E325F4342494C4700000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF39E2)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PSLLDQ_18_symbolic(self):
        """ Instruction PSLLDQ_18
            Groups: sse2
            0x7ffff7df389d:	pslldq	xmm2, 4
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF389D, "f\x0fs\xfa\x04")
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x665F4F495F006F6C6C657466006B6863)
        cpu.RIP = 0x7FFFF7DF389D

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF38A0, 8) == ord("\xfa"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF38A1, 8) == ord("\x04"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF389D, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF389E, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF389F, 8) == ord("s"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x5F006F6C6C657466006B686300000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF38A2)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PSLLDQ_19_symbolic(self):
        """ Instruction PSLLDQ_19
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3470, "f\x0fs\xfa\x07")
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x1)
        cpu.RIP = 0x7FFFF7DF3470

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3470, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3471, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3472, 8) == ord("s"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3473, 8) == ord("\xfa"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3474, 8) == ord("\x07"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x100000000000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF3475)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PSLLDQ_2_symbolic(self):
        """ Instruction PSLLDQ_2
            Groups: sse2
            0x7ffff7df2f70:	pslldq	xmm2, 0xb
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF2000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF2F70, "f\x0fs\xfa\x0b")
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x6972705F5F00362E6F732E6362696C00)
        cpu.RIP = 0x7FFFF7DF2F70

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2F70, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2F71, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2F72, 8) == ord("s"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2F73, 8) == ord("\xfa"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF2F74, 8) == ord("\x0b"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x6362696C000000000000000000000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF2F75)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PSLLDQ_20_symbolic(self):
        """ Instruction PSLLDQ_20
            Groups: sse2
            0x7ffff7df3970:	pslldq	xmm2, 3
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3970, "f\x0fs\xfa\x03")
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x322E6F732E34362D3638782D78756E69)
        cpu.RIP = 0x7FFFF7DF3970

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3970, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3971, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3972, 8) == ord("s"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3973, 8) == ord("\xfa"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3974, 8) == ord("\x03"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x732E34362D3638782D78756E69000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF3975)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PSLLDQ_21_symbolic(self):
        """ Instruction PSLLDQ_21
            Groups: sse2
            0x7ffff7df3830:	pslldq	xmm2, 4
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3830, "f\x0fs\xfa\x04")
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x5F4342494C4700342E332E325F434249)
        cpu.RIP = 0x7FFFF7DF3830

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3830, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3831, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3832, 8) == ord("s"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3833, 8) == ord("\xfa"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3834, 8) == ord("\x04"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x4C4700342E332E325F43424900000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF3835)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PSLLDQ_3_symbolic(self):
        """ Instruction PSLLDQ_3
            Groups: sse2
            0x7ffff7df3ab0:	pslldq	xmm2, 2
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3AB0, "f\x0fs\xfa\x02")
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x63007463656A626F5F726F665F6F7364)
        cpu.RIP = 0x7FFFF7DF3AB0

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3AB0, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3AB1, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3AB2, 8) == ord("s"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3AB3, 8) == ord("\xfa"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3AB4, 8) == ord("\x02"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x7463656A626F5F726F665F6F73640000)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF3AB5)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PSLLDQ_4_symbolic(self):
        """ Instruction PSLLDQ_4
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3470, "f\x0fs\xfa\x07")
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x6972705F5F00362E6F732E6362696C00)
        cpu.RIP = 0x7FFFF7DF3470

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3470, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3471, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3472, 8) == ord("s"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3473, 8) == ord("\xfa"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3474, 8) == ord("\x07"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x2E6F732E6362696C0000000000000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF3475)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PSLLDQ_5_symbolic(self):
        """ Instruction PSLLDQ_5
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3470, "f\x0fs\xfa\x07")
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x6972705F5F00362E6F732E6362696C00)
        cpu.RIP = 0x7FFFF7DF3470

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3470, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3471, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3472, 8) == ord("s"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3473, 8) == ord("\xfa"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3474, 8) == ord("\x07"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x2E6F732E6362696C0000000000000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF3475)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PSLLDQ_6_symbolic(self):
        """ Instruction PSLLDQ_6
            Groups: sse2
            0x7ffff7df389d:	pslldq	xmm2, 4
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF389D, "f\x0fs\xfa\x04")
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x3000000020002000000352E322E32)
        cpu.RIP = 0x7FFFF7DF389D

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF38A0, 8) == ord("\xfa"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF38A1, 8) == ord("\x04"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF389D, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF389E, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF389F, 8) == ord("s"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x20002000000352E322E3200000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF38A2)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PSLLDQ_7_symbolic(self):
        """ Instruction PSLLDQ_7
            Groups: sse2
            0x7ffff7df3470:	pslldq	xmm2, 7
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3470, "f\x0fs\xfa\x07")
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x1)
        cpu.RIP = 0x7FFFF7DF3470

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3470, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3471, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3472, 8) == ord("s"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3473, 8) == ord("\xfa"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3474, 8) == ord("\x07"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x100000000000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF3475)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PSLLDQ_8_symbolic(self):
        """ Instruction PSLLDQ_8
            Groups: sse2
            0x7ffff7df39dd:	pslldq	xmm2, 3
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF39DD, "f\x0fs\xfa\x03")
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x7461636F6C6C6165645F6C645F00636F)
        cpu.RIP = 0x7FFFF7DF39DD

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF39E0, 8) == ord("\xfa"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF39E1, 8) == ord("\x03"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF39DD, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF39DE, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF39DF, 8) == ord("s"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x6F6C6C6165645F6C645F00636F000000)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF39E2)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PSLLDQ_9_symbolic(self):
        """ Instruction PSLLDQ_9
            Groups: sse2
            0x7ffff7df3c5d:	pslldq	xmm2, 1
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x7FFFF7DF3000, 0x1000, "rwx")
        mem.write(0x7FFFF7DF3C5D, "f\x0fs\xfa\x01")
        cpu.XMM2 = cs.new_bitvec(128)
        cs.add(cpu.XMM2 == 0x68252E7568254D00796164666F656D69)
        cpu.RIP = 0x7FFFF7DF3C5D

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
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3C60, 8) == ord("\xfa"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3C61, 8) == ord("\x01"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3C5D, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3C5E, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x7FFFF7DF3C5F, 8) == ord("s"))
        condition = Operators.AND(condition, cpu.XMM2 == 0x252E7568254D00796164666F656D6900)
        condition = Operators.AND(condition, cpu.RIP == 0x7FFFF7DF3C62)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


if __name__ == "__main__":
    unittest.main()
