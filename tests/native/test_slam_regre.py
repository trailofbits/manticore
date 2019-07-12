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

    def test_PUNPCKHDQ_1(self):
        """ Instruction PUNPCKHDQ_1
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = 0x4E0000004C0000004A00000048
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419C43
        cpu.execute()

        self.assertEqual(mem[0x419C43:0x419C48], [b"f", b"A", b"\x0f", b"j", b"\xc0"])
        self.assertEqual(cpu.XMM0, 1438846037749345026124)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848)

    def test_PUNPCKHDQ_10(self):
        """ Instruction PUNPCKHDQ_10
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = 0x36000000340000003200000030
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419C43
        cpu.execute()

        self.assertEqual(mem[0x419C43:0x419C48], [b"f", b"A", b"\x0f", b"j", b"\xc0"])
        self.assertEqual(cpu.XMM0, 996124179980315787316)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848)

    def test_PUNPCKHDQ_11(self):
        """ Instruction PUNPCKHDQ_11
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = 0x3E0000003C0000003A00000038
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419C43
        cpu.execute()

        self.assertEqual(mem[0x419C43:0x419C48], [b"f", b"A", b"\x0f", b"j", b"\xc0"])
        self.assertEqual(cpu.XMM0, 1143698132569992200252)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848)

    def test_PUNPCKHDQ_12(self):
        """ Instruction PUNPCKHDQ_12
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = 0x8E0000008C0000008A00000088
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419C43
        cpu.execute()

        self.assertEqual(mem[0x419C43:0x419C48], [b"f", b"A", b"\x0f", b"j", b"\xc0"])
        self.assertEqual(cpu.XMM0, 2619437658466756329612)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848)

    def test_PUNPCKHDQ_13(self):
        """ Instruction PUNPCKHDQ_13
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = 0xE6000000E4000000E2000000E0
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419C43
        cpu.execute()

        self.assertEqual(mem[0x419C43:0x419C48], [b"f", b"A", b"\x0f", b"j", b"\xc0"])
        self.assertEqual(cpu.XMM0, 4242751136953196871908)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848)

    def test_PUNPCKHDQ_14(self):
        """ Instruction PUNPCKHDQ_14
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = 0x7E0000007C0000007A00000078
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419C43
        cpu.execute()

        self.assertEqual(mem[0x419C43:0x419C48], [b"f", b"A", b"\x0f", b"j", b"\xc0"])
        self.assertEqual(cpu.XMM0, 2324289753287403503740)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848)

    def test_PUNPCKHDQ_15(self):
        """ Instruction PUNPCKHDQ_15
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = 0x96000000940000009200000090
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419C43
        cpu.execute()

        self.assertEqual(mem[0x419C43:0x419C48], [b"f", b"A", b"\x0f", b"j", b"\xc0"])
        self.assertEqual(cpu.XMM0, 2767011611056432742548)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848)

    def test_PUNPCKHDQ_16(self):
        """ Instruction PUNPCKHDQ_16
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = 0x6000000040000000200000000
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419C43
        cpu.execute()

        self.assertEqual(mem[0x419C43:0x419C48], [b"f", b"A", b"\x0f", b"j", b"\xc0"])
        self.assertEqual(cpu.XMM0, 110680464442257309700)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848)

    def test_PUNPCKHDQ_17(self):
        """ Instruction PUNPCKHDQ_17
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = 0xCE000000CC000000CA000000C8
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419C43
        cpu.execute()

        self.assertEqual(mem[0x419C43:0x419C48], [b"f", b"A", b"\x0f", b"j", b"\xc0"])
        self.assertEqual(cpu.XMM0, 3800029279184167633100)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848)

    def test_PUNPCKHDQ_18(self):
        """ Instruction PUNPCKHDQ_18
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = 0x9E0000009C0000009A00000098
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419C43
        cpu.execute()

        self.assertEqual(mem[0x419C43:0x419C48], [b"f", b"A", b"\x0f", b"j", b"\xc0"])
        self.assertEqual(cpu.XMM0, 2914585563646109155484)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848)

    def test_PUNPCKHDQ_19(self):
        """ Instruction PUNPCKHDQ_19
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = 0x46000000440000004200000040
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419C43
        cpu.execute()

        self.assertEqual(mem[0x419C43:0x419C48], [b"f", b"A", b"\x0f", b"j", b"\xc0"])
        self.assertEqual(cpu.XMM0, 1291272085159668613188)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848)

    def test_PUNPCKHDQ_2(self):
        """ Instruction PUNPCKHDQ_2
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = 0xBE000000BC000000BA000000B8
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419C43
        cpu.execute()

        self.assertEqual(mem[0x419C43:0x419C48], [b"f", b"A", b"\x0f", b"j", b"\xc0"])
        self.assertEqual(cpu.XMM0, 3504881374004814807228)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848)

    def test_PUNPCKHDQ_20(self):
        """ Instruction PUNPCKHDQ_20
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = 0x66000000640000006200000060
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419C43
        cpu.execute()

        self.assertEqual(mem[0x419C43:0x419C48], [b"f", b"A", b"\x0f", b"j", b"\xc0"])
        self.assertEqual(cpu.XMM0, 1881567895518374264932)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848)

    def test_PUNPCKHDQ_21(self):
        """ Instruction PUNPCKHDQ_21
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = 0x5E0000005C0000005A00000058
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419C43
        cpu.execute()

        self.assertEqual(mem[0x419C43:0x419C48], [b"f", b"A", b"\x0f", b"j", b"\xc0"])
        self.assertEqual(cpu.XMM0, 1733993942928697851996)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848)

    def test_PUNPCKHDQ_3(self):
        """ Instruction PUNPCKHDQ_3
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = 0x6E0000006C0000006A00000068
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419C43
        cpu.execute()

        self.assertEqual(mem[0x419C43:0x419C48], [b"f", b"A", b"\x0f", b"j", b"\xc0"])
        self.assertEqual(cpu.XMM0, 2029141848108050677868)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848)

    def test_PUNPCKHDQ_4(self):
        """ Instruction PUNPCKHDQ_4
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = 0xC6000000C4000000C2000000C0
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419C43
        cpu.execute()

        self.assertEqual(mem[0x419C43:0x419C48], [b"f", b"A", b"\x0f", b"j", b"\xc0"])
        self.assertEqual(cpu.XMM0, 3652455326594491220164)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848)

    def test_PUNPCKHDQ_5(self):
        """ Instruction PUNPCKHDQ_5
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = 0xB6000000B4000000B2000000B0
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419C43
        cpu.execute()

        self.assertEqual(mem[0x419C43:0x419C48], [b"f", b"A", b"\x0f", b"j", b"\xc0"])
        self.assertEqual(cpu.XMM0, 3357307421415138394292)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848)

    def test_PUNPCKHDQ_6(self):
        """ Instruction PUNPCKHDQ_6
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = 0xAE000000AC000000AA000000A8
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419C43
        cpu.execute()

        self.assertEqual(mem[0x419C43:0x419C48], [b"f", b"A", b"\x0f", b"j", b"\xc0"])
        self.assertEqual(cpu.XMM0, 3209733468825461981356)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848)

    def test_PUNPCKHDQ_7(self):
        """ Instruction PUNPCKHDQ_7
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = 0xE0000000C0000000A00000008
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419C43
        cpu.execute()

        self.assertEqual(mem[0x419C43:0x419C48], [b"f", b"A", b"\x0f", b"j", b"\xc0"])
        self.assertEqual(cpu.XMM0, 258254417031933722636)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848)

    def test_PUNPCKHDQ_8(self):
        """ Instruction PUNPCKHDQ_8
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = 0x86000000840000008200000080
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419C43
        cpu.execute()

        self.assertEqual(mem[0x419C43:0x419C48], [b"f", b"A", b"\x0f", b"j", b"\xc0"])
        self.assertEqual(cpu.XMM0, 2471863705877079916676)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848)

    def test_PUNPCKHDQ_9(self):
        """ Instruction PUNPCKHDQ_9
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = 0xD6000000D4000000D2000000D0
        cpu.XMM8 = 0x0
        cpu.RIP = 0x419C43
        cpu.execute()

        self.assertEqual(mem[0x419C43:0x419C48], [b"f", b"A", b"\x0f", b"j", b"\xc0"])
        self.assertEqual(cpu.XMM0, 3947603231773844046036)
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.RIP, 4299848)

    def test_PUNPCKHQDQ_1(self):
        """ Instruction PUNPCKHQDQ_1
            Groups: sse2
            0x419c71:	punpckhqdq	xmm1, xmm1
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C71, "f\x0fm\xc9")
        cpu.XMM1 = 0x6CBAE800000000006CBAD8
        cpu.RIP = 0x419C71
        cpu.execute()

        self.assertEqual(mem[0x419C71:0x419C75], [b"f", b"\x0f", b"m", b"\xc9"])
        self.assertEqual(cpu.XMM1, 131446628328818805501115112)
        self.assertEqual(cpu.RIP, 4299893)

    def test_PUNPCKHQDQ_10(self):
        """ Instruction PUNPCKHQDQ_10
            Groups: sse2
            0x419c71:	punpckhqdq	xmm1, xmm1
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C71, "f\x0fm\xc9")
        cpu.XMM1 = 0x6CB8E800000000006CB8D8
        cpu.RIP = 0x419C71
        cpu.execute()

        self.assertEqual(mem[0x419C71:0x419C75], [b"f", b"\x0f", b"m", b"\xc9"])
        self.assertEqual(cpu.XMM1, 131437183595853066210687208)
        self.assertEqual(cpu.RIP, 4299893)

    def test_PUNPCKHQDQ_11(self):
        """ Instruction PUNPCKHQDQ_11
            Groups: sse2
            0x419c86:	punpckhqdq	xmm0, xmm0
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C86, "f\x0fm\xc0")
        cpu.XMM0 = 0x6CBA8800000000006CBA78
        cpu.RIP = 0x419C86
        cpu.execute()

        self.assertEqual(mem[0x419C86:0x419C8A], [b"f", b"\x0f", b"m", b"\xc0"])
        self.assertEqual(cpu.XMM0, 131444857441387729384159880)
        self.assertEqual(cpu.RIP, 4299914)

    def test_PUNPCKHQDQ_12(self):
        """ Instruction PUNPCKHQDQ_12
            Groups: sse2
            0x419c71:	punpckhqdq	xmm1, xmm1
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C71, "f\x0fm\xc9")
        cpu.XMM1 = 0x6CBAA800000000006CBA98
        cpu.RIP = 0x419C71
        cpu.execute()

        self.assertEqual(mem[0x419C71:0x419C75], [b"f", b"\x0f", b"m", b"\xc9"])
        self.assertEqual(cpu.XMM1, 131445447737198088089811624)
        self.assertEqual(cpu.RIP, 4299893)

    def test_PUNPCKHQDQ_13(self):
        """ Instruction PUNPCKHQDQ_13
            Groups: sse2
            0x419c71:	punpckhqdq	xmm1, xmm1
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C71, "f\x0fm\xc9")
        cpu.XMM1 = 0x6CBEE800000000006CBED8
        cpu.RIP = 0x419C71
        cpu.execute()

        self.assertEqual(mem[0x419C71:0x419C75], [b"f", b"\x0f", b"m", b"\xc9"])
        self.assertEqual(cpu.XMM1, 131465517794750284081970920)
        self.assertEqual(cpu.RIP, 4299893)

    def test_PUNPCKHQDQ_14(self):
        """ Instruction PUNPCKHQDQ_14
            Groups: sse2
            0x419c86:	punpckhqdq	xmm0, xmm0
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C86, "f\x0fm\xc0")
        cpu.XMM0 = 0x6CBF4800000000006CBF38
        cpu.RIP = 0x419C86
        cpu.execute()

        self.assertEqual(mem[0x419C86:0x419C8A], [b"f", b"\x0f", b"m", b"\xc0"])
        self.assertEqual(cpu.XMM0, 131467288682181360198926152)
        self.assertEqual(cpu.RIP, 4299914)

    def test_PUNPCKHQDQ_15(self):
        """ Instruction PUNPCKHQDQ_15
            Groups: sse2
            0x419c86:	punpckhqdq	xmm0, xmm0
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C86, "f\x0fm\xc0")
        cpu.XMM0 = 0x6CBDC800000000006CBDB8
        cpu.RIP = 0x419C86
        cpu.execute()

        self.assertEqual(mem[0x419C86:0x419C8A], [b"f", b"\x0f", b"m", b"\xc0"])
        self.assertEqual(cpu.XMM0, 131460205132457055731105224)
        self.assertEqual(cpu.RIP, 4299914)

    def test_PUNPCKHQDQ_16(self):
        """ Instruction PUNPCKHQDQ_16
            Groups: sse2
            0x419c71:	punpckhqdq	xmm1, xmm1
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C71, "f\x0fm\xc9")
        cpu.XMM1 = 0x6CB96800000000006CB958
        cpu.RIP = 0x419C71
        cpu.execute()

        self.assertEqual(mem[0x419C71:0x419C75], [b"f", b"\x0f", b"m", b"\xc9"])
        self.assertEqual(cpu.XMM1, 131439544779094501033294184)
        self.assertEqual(cpu.RIP, 4299893)

    def test_PUNPCKHQDQ_17(self):
        """ Instruction PUNPCKHQDQ_17
            Groups: sse2
            0x419c86:	punpckhqdq	xmm0, xmm0
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C86, "f\x0fm\xc0")
        cpu.XMM0 = 0x6CBB4800000000006CBB38
        cpu.RIP = 0x419C86
        cpu.execute()

        self.assertEqual(mem[0x419C86:0x419C8A], [b"f", b"\x0f", b"m", b"\xc0"])
        self.assertEqual(cpu.XMM0, 131448399216249881618070344)
        self.assertEqual(cpu.RIP, 4299914)

    def test_PUNPCKHQDQ_18(self):
        """ Instruction PUNPCKHQDQ_18
            Groups: sse2
            0x419c86:	punpckhqdq	xmm0, xmm0
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C86, "f\x0fm\xc0")
        cpu.XMM0 = 0x6CB90800000000006CB8F8
        cpu.RIP = 0x419C86
        cpu.execute()

        self.assertEqual(mem[0x419C86:0x419C8A], [b"f", b"\x0f", b"m", b"\xc0"])
        self.assertEqual(cpu.XMM0, 131437773891663424916338952)
        self.assertEqual(cpu.RIP, 4299914)

    def test_PUNPCKHQDQ_19(self):
        """ Instruction PUNPCKHQDQ_19
            Groups: sse2
            0x419c71:	punpckhqdq	xmm1, xmm1
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C71, "f\x0fm\xc9")
        cpu.XMM1 = 0x6CBFE800000000006CBFD8
        cpu.RIP = 0x419C71
        cpu.execute()

        self.assertEqual(mem[0x419C71:0x419C75], [b"f", b"\x0f", b"m", b"\xc9"])
        self.assertEqual(cpu.XMM1, 131470240161233153727184872)
        self.assertEqual(cpu.RIP, 4299893)

    def test_PUNPCKHQDQ_2(self):
        """ Instruction PUNPCKHQDQ_2
            Groups: sse2
            0x419c86:	punpckhqdq	xmm0, xmm0
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C86, "f\x0fm\xc0")
        cpu.XMM0 = 0x6CB88800000000006CB878
        cpu.RIP = 0x419C86
        cpu.execute()

        self.assertEqual(mem[0x419C86:0x419C8A], [b"f", b"\x0f", b"m", b"\xc0"])
        self.assertEqual(cpu.XMM0, 131435412708421990093731976)
        self.assertEqual(cpu.RIP, 4299914)

    def test_PUNPCKHQDQ_20(self):
        """ Instruction PUNPCKHQDQ_20
            Groups: sse2
            0x419c71:	punpckhqdq	xmm1, xmm1
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C71, "f\x0fm\xc9")
        cpu.XMM1 = 0x6CB92800000000006CB918
        cpu.RIP = 0x419C71
        cpu.execute()

        self.assertEqual(mem[0x419C71:0x419C75], [b"f", b"\x0f", b"m", b"\xc9"])
        self.assertEqual(cpu.XMM1, 131438364187473783621990696)
        self.assertEqual(cpu.RIP, 4299893)

    def test_PUNPCKHQDQ_21(self):
        """ Instruction PUNPCKHQDQ_21
            Groups: sse2
            0x419c86:	punpckhqdq	xmm0, xmm0
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C86, "f\x0fm\xc0")
        cpu.XMM0 = 0x6CBAC800000000006CBAB8
        cpu.RIP = 0x419C86
        cpu.execute()

        self.assertEqual(mem[0x419C86:0x419C8A], [b"f", b"\x0f", b"m", b"\xc0"])
        self.assertEqual(cpu.XMM0, 131446038033008446795463368)
        self.assertEqual(cpu.RIP, 4299914)

    def test_PUNPCKHQDQ_3(self):
        """ Instruction PUNPCKHQDQ_3
            Groups: sse2
            0x419c71:	punpckhqdq	xmm1, xmm1
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C71, "f\x0fm\xc9")
        cpu.XMM1 = 0x6CBBE800000000006CBBD8
        cpu.RIP = 0x419C71
        cpu.execute()

        self.assertEqual(mem[0x419C71:0x419C75], [b"f", b"\x0f", b"m", b"\xc9"])
        self.assertEqual(cpu.XMM1, 131451350695301675146329064)
        self.assertEqual(cpu.RIP, 4299893)

    def test_PUNPCKHQDQ_4(self):
        """ Instruction PUNPCKHQDQ_4
            Groups: sse2
            0x419c86:	punpckhqdq	xmm0, xmm0
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C86, "f\x0fm\xc0")
        cpu.XMM0 = 0x6CBD8800000000006CBD78
        cpu.RIP = 0x419C86
        cpu.execute()

        self.assertEqual(mem[0x419C86:0x419C8A], [b"f", b"\x0f", b"m", b"\xc0"])
        self.assertEqual(cpu.XMM0, 131459024540836338319801736)
        self.assertEqual(cpu.RIP, 4299914)

    def test_PUNPCKHQDQ_5(self):
        """ Instruction PUNPCKHQDQ_5
            Groups: sse2
            0x419c71:	punpckhqdq	xmm1, xmm1
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C71, "f\x0fm\xc9")
        cpu.XMM1 = 0x6CB86800000000006CB858
        cpu.RIP = 0x419C71
        cpu.execute()

        self.assertEqual(mem[0x419C71:0x419C75], [b"f", b"\x0f", b"m", b"\xc9"])
        self.assertEqual(cpu.XMM1, 131434822412611631388080232)
        self.assertEqual(cpu.RIP, 4299893)

    def test_PUNPCKHQDQ_6(self):
        """ Instruction PUNPCKHQDQ_6
            Groups: sse2
            0x419c71:	punpckhqdq	xmm1, xmm1
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C71, "f\x0fm\xc9")
        cpu.XMM1 = 0x6CBDE800000000006CBDD8
        cpu.RIP = 0x419C71
        cpu.execute()

        self.assertEqual(mem[0x419C71:0x419C75], [b"f", b"\x0f", b"m", b"\xc9"])
        self.assertEqual(cpu.XMM1, 131460795428267414436756968)
        self.assertEqual(cpu.RIP, 4299893)

    def test_PUNPCKHQDQ_7(self):
        """ Instruction PUNPCKHQDQ_7
            Groups: sse2
            0x419c71:	punpckhqdq	xmm1, xmm1
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C71, "f\x0fm\xc9")
        cpu.XMM1 = 0x6CBD2800000000006CBD18
        cpu.RIP = 0x419C71
        cpu.execute()

        self.assertEqual(mem[0x419C71:0x419C75], [b"f", b"\x0f", b"m", b"\xc9"])
        self.assertEqual(cpu.XMM1, 131457253653405262202846504)
        self.assertEqual(cpu.RIP, 4299893)

    def test_PUNPCKHQDQ_8(self):
        """ Instruction PUNPCKHQDQ_8
            Groups: sse2
            0x419c71:	punpckhqdq	xmm1, xmm1
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C71, "f\x0fm\xc9")
        cpu.XMM1 = 0x6CB8A800000000006CB898
        cpu.RIP = 0x419C71
        cpu.execute()

        self.assertEqual(mem[0x419C71:0x419C75], [b"f", b"\x0f", b"m", b"\xc9"])
        self.assertEqual(cpu.XMM1, 131436003004232348799383720)
        self.assertEqual(cpu.RIP, 4299893)

    def test_PUNPCKHQDQ_9(self):
        """ Instruction PUNPCKHQDQ_9
            Groups: sse2
            0x419c86:	punpckhqdq	xmm0, xmm0
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C86, "f\x0fm\xc0")
        cpu.XMM0 = 0x6CB94800000000006CB938
        cpu.RIP = 0x419C86
        cpu.execute()

        self.assertEqual(mem[0x419C86:0x419C8A], [b"f", b"\x0f", b"m", b"\xc0"])
        self.assertEqual(cpu.XMM0, 131438954483284142327642440)
        self.assertEqual(cpu.RIP, 4299914)

    def test_PUNPCKLBW_1(self):
        """ Instruction PUNPCKLBW_1
            Groups: sse2
            0x4668ac:	punpcklbw	xmm1, xmm1
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00466000, 0x1000, "rwx")
        mem.write(0x4668AC, "f\x0f`\xc9")
        cpu.XMM1 = 0x2F
        cpu.RIP = 0x4668AC
        cpu.execute()

        self.assertEqual(mem[0x4668AC:0x4668B0], [b"f", b"\x0f", b"`", b"\xc9"])
        self.assertEqual(cpu.XMM1, 12079)
        self.assertEqual(cpu.RIP, 4614320)

    def test_PUNPCKLDQ_1(self):
        """ Instruction PUNPCKLDQ_1
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0xA6000000A4000000A2000000A0
        cpu.RIP = 0x419C48
        cpu.execute()

        self.assertEqual(mem[0x419C48:0x419C4D], [b"f", b"A", b"\x0f", b"b", b"\xc8"])
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 2988372539940947361952)
        self.assertEqual(cpu.RIP, 4299853)

    def test_PUNPCKLDQ_10(self):
        """ Instruction PUNPCKLDQ_10
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0x3E0000003C0000003A00000038
        cpu.RIP = 0x419C48
        cpu.execute()

        self.assertEqual(mem[0x419C48:0x419C4D], [b"f", b"A", b"\x0f", b"b", b"\xc8"])
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 1069911156275153993784)
        self.assertEqual(cpu.RIP, 4299853)

    def test_PUNPCKLDQ_11(self):
        """ Instruction PUNPCKLDQ_11
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0x6000000040000000200000000
        cpu.RIP = 0x419C48
        cpu.execute()

        self.assertEqual(mem[0x419C48:0x419C4D], [b"f", b"A", b"\x0f", b"b", b"\xc8"])
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 36893488147419103232)
        self.assertEqual(cpu.RIP, 4299853)

    def test_PUNPCKLDQ_12(self):
        """ Instruction PUNPCKLDQ_12
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0x1E0000001C0000001A00000018
        cpu.RIP = 0x419C48
        cpu.execute()

        self.assertEqual(mem[0x419C48:0x419C4D], [b"f", b"A", b"\x0f", b"b", b"\xc8"])
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 479615345916448342040)
        self.assertEqual(cpu.RIP, 4299853)

    def test_PUNPCKLDQ_13(self):
        """ Instruction PUNPCKLDQ_13
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0xE0000000C0000000A00000008
        cpu.RIP = 0x419C48
        cpu.execute()

        self.assertEqual(mem[0x419C48:0x419C4D], [b"f", b"A", b"\x0f", b"b", b"\xc8"])
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 184467440737095516168)
        self.assertEqual(cpu.RIP, 4299853)

    def test_PUNPCKLDQ_14(self):
        """ Instruction PUNPCKLDQ_14
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0xEE000000EC000000EA000000E8
        cpu.RIP = 0x419C48
        cpu.execute()

        self.assertEqual(mem[0x419C48:0x419C4D], [b"f", b"A", b"\x0f", b"b", b"\xc8"])
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 4316538113248035078376)
        self.assertEqual(cpu.RIP, 4299853)

    def test_PUNPCKLDQ_15(self):
        """ Instruction PUNPCKLDQ_15
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0x2E0000002C0000002A00000028
        cpu.RIP = 0x419C48
        cpu.execute()

        self.assertEqual(mem[0x419C48:0x419C4D], [b"f", b"A", b"\x0f", b"b", b"\xc8"])
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 774763251095801167912)
        self.assertEqual(cpu.RIP, 4299853)

    def test_PUNPCKLDQ_16(self):
        """ Instruction PUNPCKLDQ_16
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0xF6000000F4000000F2000000F0
        cpu.RIP = 0x419C48
        cpu.execute()

        self.assertEqual(mem[0x419C48:0x419C4D], [b"f", b"A", b"\x0f", b"b", b"\xc8"])
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 4464112065837711491312)
        self.assertEqual(cpu.RIP, 4299853)

    def test_PUNPCKLDQ_17(self):
        """ Instruction PUNPCKLDQ_17
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0x9E0000009C0000009A00000098
        cpu.RIP = 0x419C48
        cpu.execute()

        self.assertEqual(mem[0x419C48:0x419C4D], [b"f", b"A", b"\x0f", b"b", b"\xc8"])
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 2840798587351270949016)
        self.assertEqual(cpu.RIP, 4299853)

    def test_PUNPCKLDQ_18(self):
        """ Instruction PUNPCKLDQ_18
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0x16000000140000001200000010
        cpu.RIP = 0x419C48
        cpu.execute()

        self.assertEqual(mem[0x419C48:0x419C4D], [b"f", b"A", b"\x0f", b"b", b"\xc8"])
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 332041393326771929104)
        self.assertEqual(cpu.RIP, 4299853)

    def test_PUNPCKLDQ_19(self):
        """ Instruction PUNPCKLDQ_19
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0x96000000940000009200000090
        cpu.RIP = 0x419C48
        cpu.execute()

        self.assertEqual(mem[0x419C48:0x419C4D], [b"f", b"A", b"\x0f", b"b", b"\xc8"])
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 2693224634761594536080)
        self.assertEqual(cpu.RIP, 4299853)

    def test_PUNPCKLDQ_2(self):
        """ Instruction PUNPCKLDQ_2
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0x76000000740000007200000070
        cpu.RIP = 0x419C48
        cpu.execute()

        self.assertEqual(mem[0x419C48:0x419C4D], [b"f", b"A", b"\x0f", b"b", b"\xc8"])
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 2102928824402888884336)
        self.assertEqual(cpu.RIP, 4299853)

    def test_PUNPCKLDQ_20(self):
        """ Instruction PUNPCKLDQ_20
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0xDE000000DC000000DA000000D8
        cpu.RIP = 0x419C48
        cpu.execute()

        self.assertEqual(mem[0x419C48:0x419C4D], [b"f", b"A", b"\x0f", b"b", b"\xc8"])
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 4021390208068682252504)
        self.assertEqual(cpu.RIP, 4299853)

    def test_PUNPCKLDQ_21(self):
        """ Instruction PUNPCKLDQ_21
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0xE6000000E4000000E2000000E0
        cpu.RIP = 0x419C48
        cpu.execute()

        self.assertEqual(mem[0x419C48:0x419C4D], [b"f", b"A", b"\x0f", b"b", b"\xc8"])
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 4168964160658358665440)
        self.assertEqual(cpu.RIP, 4299853)

    def test_PUNPCKLDQ_3(self):
        """ Instruction PUNPCKLDQ_3
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0x36000000340000003200000030
        cpu.RIP = 0x419C48
        cpu.execute()

        self.assertEqual(mem[0x419C48:0x419C4D], [b"f", b"A", b"\x0f", b"b", b"\xc8"])
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 922337203685477580848)
        self.assertEqual(cpu.RIP, 4299853)

    def test_PUNPCKLDQ_4(self):
        """ Instruction PUNPCKLDQ_4
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0x6E0000006C0000006A00000068
        cpu.RIP = 0x419C48
        cpu.execute()

        self.assertEqual(mem[0x419C48:0x419C4D], [b"f", b"A", b"\x0f", b"b", b"\xc8"])
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 1955354871813212471400)
        self.assertEqual(cpu.RIP, 4299853)

    def test_PUNPCKLDQ_5(self):
        """ Instruction PUNPCKLDQ_5
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0x7E0000007C0000007A00000078
        cpu.RIP = 0x419C48
        cpu.execute()

        self.assertEqual(mem[0x419C48:0x419C4D], [b"f", b"A", b"\x0f", b"b", b"\xc8"])
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 2250502776992565297272)
        self.assertEqual(cpu.RIP, 4299853)

    def test_PUNPCKLDQ_6(self):
        """ Instruction PUNPCKLDQ_6
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0x26000000240000002200000020
        cpu.RIP = 0x419C48
        cpu.execute()

        self.assertEqual(mem[0x419C48:0x419C4D], [b"f", b"A", b"\x0f", b"b", b"\xc8"])
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 627189298506124754976)
        self.assertEqual(cpu.RIP, 4299853)

    def test_PUNPCKLDQ_7(self):
        """ Instruction PUNPCKLDQ_7
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0xBE000000BC000000BA000000B8
        cpu.RIP = 0x419C48
        cpu.execute()

        self.assertEqual(mem[0x419C48:0x419C4D], [b"f", b"A", b"\x0f", b"b", b"\xc8"])
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 3431094397709976600760)
        self.assertEqual(cpu.RIP, 4299853)

    def test_PUNPCKLDQ_8(self):
        """ Instruction PUNPCKLDQ_8
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0xCE000000CC000000CA000000C8
        cpu.RIP = 0x419C48
        cpu.execute()

        self.assertEqual(mem[0x419C48:0x419C4D], [b"f", b"A", b"\x0f", b"b", b"\xc8"])
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 3726242302889329426632)
        self.assertEqual(cpu.RIP, 4299853)

    def test_PUNPCKLDQ_9(self):
        """ Instruction PUNPCKLDQ_9
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = 0x0
        cpu.XMM1 = 0x46000000440000004200000040
        cpu.RIP = 0x419C48
        cpu.execute()

        self.assertEqual(mem[0x419C48:0x419C4D], [b"f", b"A", b"\x0f", b"b", b"\xc8"])
        self.assertEqual(cpu.XMM8, 0)
        self.assertEqual(cpu.XMM1, 1217485108864830406720)
        self.assertEqual(cpu.RIP, 4299853)

    def test_PUNPCKLQDQ_1(self):
        """ Instruction PUNPCKLQDQ_1
            Groups: sse2
            0x419c82:	punpcklqdq	xmm1, xmm0
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C82, "f\x0fl\xc8")
        cpu.XMM0 = 0x6CBFC800000000006CBFB8
        cpu.XMM1 = 0x6CBFC800000000006CBFB8
        cpu.RIP = 0x419C82
        cpu.execute()

        self.assertEqual(mem[0x419C82:0x419C86], [b"f", b"\x0f", b"l", b"\xc8"])
        self.assertEqual(cpu.XMM0, 131469649865422795021533112)
        self.assertEqual(cpu.XMM1, 131469354717517615668707256)
        self.assertEqual(cpu.RIP, 4299910)

    def test_PUNPCKLQDQ_10(self):
        """ Instruction PUNPCKLQDQ_10
            Groups: sse2
            0x419c6c:	punpcklqdq	xmm8, xmm1
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C6C, "fD\x0fl\xc1")
        cpu.XMM8 = 0x6CBC6800000000006CBC58
        cpu.XMM1 = 0x6CBC6800000000006CBC58
        cpu.RIP = 0x419C6C
        cpu.execute()

        self.assertEqual(mem[0x419C6C:0x419C71], [b"f", b"D", b"\x0f", b"l", b"\xc1"])
        self.assertEqual(cpu.XMM8, 131453416730637930616110168)
        self.assertEqual(cpu.XMM1, 131453711878543109968936024)
        self.assertEqual(cpu.RIP, 4299889)

    def test_PUNPCKLQDQ_11(self):
        """ Instruction PUNPCKLQDQ_11
            Groups: sse2
            0x419c82:	punpcklqdq	xmm1, xmm0
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C82, "f\x0fl\xc8")
        cpu.XMM0 = 0x6CBB4800000000006CBB38
        cpu.XMM1 = 0x6CBB4800000000006CBB38
        cpu.RIP = 0x419C82
        cpu.execute()

        self.assertEqual(mem[0x419C82:0x419C86], [b"f", b"\x0f", b"l", b"\xc8"])
        self.assertEqual(cpu.XMM0, 131448399216249881618070328)
        self.assertEqual(cpu.XMM1, 131448104068344702265244472)
        self.assertEqual(cpu.RIP, 4299910)

    def test_PUNPCKLQDQ_12(self):
        """ Instruction PUNPCKLQDQ_12
            Groups: sse2
            0x419c6c:	punpcklqdq	xmm8, xmm1
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C6C, "fD\x0fl\xc1")
        cpu.XMM8 = 0x6CBDE800000000006CBDD8
        cpu.XMM1 = 0x6CBDE800000000006CBDD8
        cpu.RIP = 0x419C6C
        cpu.execute()

        self.assertEqual(mem[0x419C6C:0x419C71], [b"f", b"D", b"\x0f", b"l", b"\xc1"])
        self.assertEqual(cpu.XMM8, 131460500280362235083931096)
        self.assertEqual(cpu.XMM1, 131460795428267414436756952)
        self.assertEqual(cpu.RIP, 4299889)

    def test_PUNPCKLQDQ_13(self):
        """ Instruction PUNPCKLQDQ_13
            Groups: sse2
            0x419c6c:	punpcklqdq	xmm8, xmm1
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C6C, "fD\x0fl\xc1")
        cpu.XMM8 = 0x6CBEE800000000006CBED8
        cpu.XMM1 = 0x6CBEE800000000006CBED8
        cpu.RIP = 0x419C6C
        cpu.execute()

        self.assertEqual(mem[0x419C6C:0x419C71], [b"f", b"D", b"\x0f", b"l", b"\xc1"])
        self.assertEqual(cpu.XMM8, 131465222646845104729145048)
        self.assertEqual(cpu.XMM1, 131465517794750284081970904)
        self.assertEqual(cpu.RIP, 4299889)

    def test_PUNPCKLQDQ_14(self):
        """ Instruction PUNPCKLQDQ_14
            Groups: sse2
            0x419c6c:	punpcklqdq	xmm8, xmm1
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C6C, "fD\x0fl\xc1")
        cpu.XMM8 = 0x6CBBA800000000006CBB98
        cpu.XMM1 = 0x6CBBA800000000006CBB98
        cpu.RIP = 0x419C6C
        cpu.execute()

        self.assertEqual(mem[0x419C6C:0x419C71], [b"f", b"D", b"\x0f", b"l", b"\xc1"])
        self.assertEqual(cpu.XMM8, 131449874955775778382199704)
        self.assertEqual(cpu.XMM1, 131450170103680957735025560)
        self.assertEqual(cpu.RIP, 4299889)

    def test_PUNPCKLQDQ_15(self):
        """ Instruction PUNPCKLQDQ_15
            Groups: sse2
            0x419c82:	punpcklqdq	xmm1, xmm0
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C82, "f\x0fl\xc8")
        cpu.XMM0 = 0x6CBCC800000000006CBCB8
        cpu.XMM1 = 0x6CBCC800000000006CBCB8
        cpu.RIP = 0x419C82
        cpu.execute()

        self.assertEqual(mem[0x419C82:0x419C86], [b"f", b"\x0f", b"l", b"\xc8"])
        self.assertEqual(cpu.XMM0, 131455482765974186085891256)
        self.assertEqual(cpu.XMM1, 131455187618069006733065400)
        self.assertEqual(cpu.RIP, 4299910)

    def test_PUNPCKLQDQ_16(self):
        """ Instruction PUNPCKLQDQ_16
            Groups: sse2
            0x419c82:	punpcklqdq	xmm1, xmm0
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C82, "f\x0fl\xc8")
        cpu.XMM0 = 0x6CBE0800000000006CBDF8
        cpu.XMM1 = 0x6CBE0800000000006CBDF8
        cpu.RIP = 0x419C82
        cpu.execute()

        self.assertEqual(mem[0x419C82:0x419C86], [b"f", b"\x0f", b"l", b"\xc8"])
        self.assertEqual(cpu.XMM0, 131461385724077773142408696)
        self.assertEqual(cpu.XMM1, 131461090576172593789582840)
        self.assertEqual(cpu.RIP, 4299910)

    def test_PUNPCKLQDQ_17(self):
        """ Instruction PUNPCKLQDQ_17
            Groups: sse2
            0x419c82:	punpcklqdq	xmm1, xmm0
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C82, "f\x0fl\xc8")
        cpu.XMM0 = 0x6CBEC800000000006CBEB8
        cpu.XMM1 = 0x6CBEC800000000006CBEB8
        cpu.RIP = 0x419C82
        cpu.execute()

        self.assertEqual(mem[0x419C82:0x419C86], [b"f", b"\x0f", b"l", b"\xc8"])
        self.assertEqual(cpu.XMM0, 131464927498939925376319160)
        self.assertEqual(cpu.XMM1, 131464632351034746023493304)
        self.assertEqual(cpu.RIP, 4299910)

    def test_PUNPCKLQDQ_18(self):
        """ Instruction PUNPCKLQDQ_18
            Groups: sse2
            0x419c6c:	punpcklqdq	xmm8, xmm1
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C6C, "fD\x0fl\xc1")
        cpu.XMM8 = 0x6CBBE800000000006CBBD8
        cpu.XMM1 = 0x6CBBE800000000006CBBD8
        cpu.RIP = 0x419C6C
        cpu.execute()

        self.assertEqual(mem[0x419C6C:0x419C71], [b"f", b"D", b"\x0f", b"l", b"\xc1"])
        self.assertEqual(cpu.XMM8, 131451055547396495793503192)
        self.assertEqual(cpu.XMM1, 131451350695301675146329048)
        self.assertEqual(cpu.RIP, 4299889)

    def test_PUNPCKLQDQ_19(self):
        """ Instruction PUNPCKLQDQ_19
            Groups: sse2
            0x419c82:	punpcklqdq	xmm1, xmm0
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C82, "f\x0fl\xc8")
        cpu.XMM0 = 0x6CBC8800000000006CBC78
        cpu.XMM1 = 0x6CBC8800000000006CBC78
        cpu.RIP = 0x419C82
        cpu.execute()

        self.assertEqual(mem[0x419C82:0x419C86], [b"f", b"\x0f", b"l", b"\xc8"])
        self.assertEqual(cpu.XMM0, 131454302174353468674587768)
        self.assertEqual(cpu.XMM1, 131454007026448289321761912)
        self.assertEqual(cpu.RIP, 4299910)

    def test_PUNPCKLQDQ_2(self):
        """ Instruction PUNPCKLQDQ_2
            Groups: sse2
            0x419c6c:	punpcklqdq	xmm8, xmm1
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C6C, "fD\x0fl\xc1")
        cpu.XMM8 = 0x6CBF6800000000006CBF58
        cpu.XMM1 = 0x6CBF6800000000006CBF58
        cpu.RIP = 0x419C6C
        cpu.execute()

        self.assertEqual(mem[0x419C6C:0x419C71], [b"f", b"D", b"\x0f", b"l", b"\xc1"])
        self.assertEqual(cpu.XMM8, 131467583830086539551752024)
        self.assertEqual(cpu.XMM1, 131467878977991718904577880)
        self.assertEqual(cpu.RIP, 4299889)

    def test_PUNPCKLQDQ_20(self):
        """ Instruction PUNPCKLQDQ_20
            Groups: sse2
            0x419c82:	punpcklqdq	xmm1, xmm0
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C82, "f\x0fl\xc8")
        cpu.XMM0 = 0x6CBA8800000000006CBA78
        cpu.XMM1 = 0x6CBA8800000000006CBA78
        cpu.RIP = 0x419C82
        cpu.execute()

        self.assertEqual(mem[0x419C82:0x419C86], [b"f", b"\x0f", b"l", b"\xc8"])
        self.assertEqual(cpu.XMM0, 131444857441387729384159864)
        self.assertEqual(cpu.XMM1, 131444562293482550031334008)
        self.assertEqual(cpu.RIP, 4299910)

    def test_PUNPCKLQDQ_21(self):
        """ Instruction PUNPCKLQDQ_21
            Groups: sse2
            0x419c6c:	punpcklqdq	xmm8, xmm1
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C6C, "fD\x0fl\xc1")
        cpu.XMM8 = 0x6CB96800000000006CB958
        cpu.XMM1 = 0x6CB96800000000006CB958
        cpu.RIP = 0x419C6C
        cpu.execute()

        self.assertEqual(mem[0x419C6C:0x419C71], [b"f", b"D", b"\x0f", b"l", b"\xc1"])
        self.assertEqual(cpu.XMM8, 131439249631189321680468312)
        self.assertEqual(cpu.XMM1, 131439544779094501033294168)
        self.assertEqual(cpu.RIP, 4299889)

    def test_PUNPCKLQDQ_3(self):
        """ Instruction PUNPCKLQDQ_3
            Groups: sse2
            0x419c6c:	punpcklqdq	xmm8, xmm1
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C6C, "fD\x0fl\xc1")
        cpu.XMM8 = 0x6CBB2800000000006CBB18
        cpu.XMM1 = 0x6CBB2800000000006CBB18
        cpu.RIP = 0x419C6C
        cpu.execute()

        self.assertEqual(mem[0x419C6C:0x419C71], [b"f", b"D", b"\x0f", b"l", b"\xc1"])
        self.assertEqual(cpu.XMM8, 131447513772534343559592728)
        self.assertEqual(cpu.XMM1, 131447808920439522912418584)
        self.assertEqual(cpu.RIP, 4299889)

    def test_PUNPCKLQDQ_4(self):
        """ Instruction PUNPCKLQDQ_4
            Groups: sse2
            0x419c6c:	punpcklqdq	xmm8, xmm1
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C6C, "fD\x0fl\xc1")
        cpu.XMM8 = 0x6CB8A800000000006CB898
        cpu.XMM1 = 0x6CB8A800000000006CB898
        cpu.RIP = 0x419C6C
        cpu.execute()

        self.assertEqual(mem[0x419C6C:0x419C71], [b"f", b"D", b"\x0f", b"l", b"\xc1"])
        self.assertEqual(cpu.XMM8, 131435707856327169446557848)
        self.assertEqual(cpu.XMM1, 131436003004232348799383704)
        self.assertEqual(cpu.RIP, 4299889)

    def test_PUNPCKLQDQ_5(self):
        """ Instruction PUNPCKLQDQ_5
            Groups: sse2
            0x419c6c:	punpcklqdq	xmm8, xmm1
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C6C, "fD\x0fl\xc1")
        cpu.XMM8 = 0x6CBC2800000000006CBC18
        cpu.XMM1 = 0x6CBC2800000000006CBC18
        cpu.RIP = 0x419C6C
        cpu.execute()

        self.assertEqual(mem[0x419C6C:0x419C71], [b"f", b"D", b"\x0f", b"l", b"\xc1"])
        self.assertEqual(cpu.XMM8, 131452236139017213204806680)
        self.assertEqual(cpu.XMM1, 131452531286922392557632536)
        self.assertEqual(cpu.RIP, 4299889)

    def test_PUNPCKLQDQ_6(self):
        """ Instruction PUNPCKLQDQ_6
            Groups: sse2
            0x419c82:	punpcklqdq	xmm1, xmm0
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C82, "f\x0fl\xc8")
        cpu.XMM0 = 0x6CBF4800000000006CBF38
        cpu.XMM1 = 0x6CBF4800000000006CBF38
        cpu.RIP = 0x419C82
        cpu.execute()

        self.assertEqual(mem[0x419C82:0x419C86], [b"f", b"\x0f", b"l", b"\xc8"])
        self.assertEqual(cpu.XMM0, 131467288682181360198926136)
        self.assertEqual(cpu.XMM1, 131466993534276180846100280)
        self.assertEqual(cpu.RIP, 4299910)

    def test_PUNPCKLQDQ_7(self):
        """ Instruction PUNPCKLQDQ_7
            Groups: sse2
            0x419c6c:	punpcklqdq	xmm8, xmm1
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C6C, "fD\x0fl\xc1")
        cpu.XMM8 = 0x6CBA6800000000006CBA58
        cpu.XMM1 = 0x6CBA6800000000006CBA58
        cpu.RIP = 0x419C6C
        cpu.execute()

        self.assertEqual(mem[0x419C6C:0x419C71], [b"f", b"D", b"\x0f", b"l", b"\xc1"])
        self.assertEqual(cpu.XMM8, 131443971997672191325682264)
        self.assertEqual(cpu.XMM1, 131444267145577370678508120)
        self.assertEqual(cpu.RIP, 4299889)

    def test_PUNPCKLQDQ_8(self):
        """ Instruction PUNPCKLQDQ_8
            Groups: sse2
            0x419c82:	punpcklqdq	xmm1, xmm0
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C82, "f\x0fl\xc8")
        cpu.XMM0 = 0x6CBA0800000000006CB9F8
        cpu.XMM1 = 0x6CBA0800000000006CB9F8
        cpu.RIP = 0x419C82
        cpu.execute()

        self.assertEqual(mem[0x419C82:0x419C86], [b"f", b"\x0f", b"l", b"\xc8"])
        self.assertEqual(cpu.XMM0, 131442496258146294561552888)
        self.assertEqual(cpu.XMM1, 131442201110241115208727032)
        self.assertEqual(cpu.RIP, 4299910)

    def test_PUNPCKLQDQ_9(self):
        """ Instruction PUNPCKLQDQ_9
            Groups: sse2
            0x419c82:	punpcklqdq	xmm1, xmm0
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C82, "f\x0fl\xc8")
        cpu.XMM0 = 0x6CBDC800000000006CBDB8
        cpu.XMM1 = 0x6CBDC800000000006CBDB8
        cpu.RIP = 0x419C82
        cpu.execute()

        self.assertEqual(mem[0x419C82:0x419C86], [b"f", b"\x0f", b"l", b"\xc8"])
        self.assertEqual(cpu.XMM0, 131460205132457055731105208)
        self.assertEqual(cpu.XMM1, 131459909984551876378279352)
        self.assertEqual(cpu.RIP, 4299910)

    def test_PUNPCKLWD_1(self):
        """ Instruction PUNPCKLWD_1
            Groups: sse2
            0x4668b6:	punpcklwd	xmm1, xmm1
        """
        mem = Memory64()
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00466000, 0x1000, "rwx")
        mem.write(0x4668B6, "f\x0fa\xc9")
        cpu.XMM1 = 0x2F2F
        cpu.RIP = 0x4668B6
        cpu.execute()

        self.assertEqual(mem[0x4668B6:0x4668BA], [b"f", b"\x0f", b"a", b"\xc9"])
        self.assertEqual(cpu.XMM1, 791621423)
        self.assertEqual(cpu.RIP, 4614330)

    def test_PUNPCKHDQ_1_symbolic(self):
        """ Instruction PUNPCKHDQ_1
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x4E0000004C0000004A00000048)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419C43

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
        condition = Operators.AND(condition, cpu.read_int(0x419C43, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C44, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C45, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C46, 8) == ord("j"))
        condition = Operators.AND(condition, cpu.read_int(0x419C47, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x4E000000000000004C)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419C48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHDQ_10_symbolic(self):
        """ Instruction PUNPCKHDQ_10
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x36000000340000003200000030)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419C43

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
        condition = Operators.AND(condition, cpu.read_int(0x419C43, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C44, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C45, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C46, 8) == ord("j"))
        condition = Operators.AND(condition, cpu.read_int(0x419C47, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x360000000000000034)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419C48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHDQ_11_symbolic(self):
        """ Instruction PUNPCKHDQ_11
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x3E0000003C0000003A00000038)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419C43

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
        condition = Operators.AND(condition, cpu.read_int(0x419C43, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C44, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C45, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C46, 8) == ord("j"))
        condition = Operators.AND(condition, cpu.read_int(0x419C47, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x3E000000000000003C)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419C48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHDQ_12_symbolic(self):
        """ Instruction PUNPCKHDQ_12
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x8E0000008C0000008A00000088)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419C43

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
        condition = Operators.AND(condition, cpu.read_int(0x419C43, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C44, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C45, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C46, 8) == ord("j"))
        condition = Operators.AND(condition, cpu.read_int(0x419C47, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x8E000000000000008C)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419C48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHDQ_13_symbolic(self):
        """ Instruction PUNPCKHDQ_13
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0xE6000000E4000000E2000000E0)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419C43

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
        condition = Operators.AND(condition, cpu.read_int(0x419C43, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C44, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C45, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C46, 8) == ord("j"))
        condition = Operators.AND(condition, cpu.read_int(0x419C47, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.XMM0 == 0xE600000000000000E4)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419C48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHDQ_14_symbolic(self):
        """ Instruction PUNPCKHDQ_14
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x7E0000007C0000007A00000078)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419C43

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
        condition = Operators.AND(condition, cpu.read_int(0x419C43, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C44, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C45, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C46, 8) == ord("j"))
        condition = Operators.AND(condition, cpu.read_int(0x419C47, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x7E000000000000007C)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419C48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHDQ_15_symbolic(self):
        """ Instruction PUNPCKHDQ_15
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x96000000940000009200000090)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419C43

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
        condition = Operators.AND(condition, cpu.read_int(0x419C43, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C44, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C45, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C46, 8) == ord("j"))
        condition = Operators.AND(condition, cpu.read_int(0x419C47, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x960000000000000094)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419C48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHDQ_16_symbolic(self):
        """ Instruction PUNPCKHDQ_16
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6000000040000000200000000)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419C43

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
        condition = Operators.AND(condition, cpu.read_int(0x419C43, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C44, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C45, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C46, 8) == ord("j"))
        condition = Operators.AND(condition, cpu.read_int(0x419C47, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x60000000000000004)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419C48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHDQ_17_symbolic(self):
        """ Instruction PUNPCKHDQ_17
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0xCE000000CC000000CA000000C8)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419C43

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
        condition = Operators.AND(condition, cpu.read_int(0x419C43, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C44, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C45, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C46, 8) == ord("j"))
        condition = Operators.AND(condition, cpu.read_int(0x419C47, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.XMM0 == 0xCE00000000000000CC)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419C48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHDQ_18_symbolic(self):
        """ Instruction PUNPCKHDQ_18
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x9E0000009C0000009A00000098)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419C43

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
        condition = Operators.AND(condition, cpu.read_int(0x419C43, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C44, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C45, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C46, 8) == ord("j"))
        condition = Operators.AND(condition, cpu.read_int(0x419C47, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x9E000000000000009C)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419C48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHDQ_19_symbolic(self):
        """ Instruction PUNPCKHDQ_19
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x46000000440000004200000040)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419C43

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
        condition = Operators.AND(condition, cpu.read_int(0x419C43, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C44, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C45, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C46, 8) == ord("j"))
        condition = Operators.AND(condition, cpu.read_int(0x419C47, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x460000000000000044)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419C48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHDQ_2_symbolic(self):
        """ Instruction PUNPCKHDQ_2
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0xBE000000BC000000BA000000B8)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419C43

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
        condition = Operators.AND(condition, cpu.read_int(0x419C43, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C44, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C45, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C46, 8) == ord("j"))
        condition = Operators.AND(condition, cpu.read_int(0x419C47, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.XMM0 == 0xBE00000000000000BC)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419C48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHDQ_20_symbolic(self):
        """ Instruction PUNPCKHDQ_20
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x66000000640000006200000060)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419C43

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
        condition = Operators.AND(condition, cpu.read_int(0x419C43, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C44, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C45, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C46, 8) == ord("j"))
        condition = Operators.AND(condition, cpu.read_int(0x419C47, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x660000000000000064)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419C48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHDQ_21_symbolic(self):
        """ Instruction PUNPCKHDQ_21
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x5E0000005C0000005A00000058)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419C43

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
        condition = Operators.AND(condition, cpu.read_int(0x419C43, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C44, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C45, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C46, 8) == ord("j"))
        condition = Operators.AND(condition, cpu.read_int(0x419C47, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x5E000000000000005C)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419C48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHDQ_3_symbolic(self):
        """ Instruction PUNPCKHDQ_3
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6E0000006C0000006A00000068)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419C43

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
        condition = Operators.AND(condition, cpu.read_int(0x419C43, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C44, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C45, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C46, 8) == ord("j"))
        condition = Operators.AND(condition, cpu.read_int(0x419C47, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6E000000000000006C)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419C48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHDQ_4_symbolic(self):
        """ Instruction PUNPCKHDQ_4
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0xC6000000C4000000C2000000C0)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419C43

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
        condition = Operators.AND(condition, cpu.read_int(0x419C43, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C44, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C45, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C46, 8) == ord("j"))
        condition = Operators.AND(condition, cpu.read_int(0x419C47, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.XMM0 == 0xC600000000000000C4)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419C48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHDQ_5_symbolic(self):
        """ Instruction PUNPCKHDQ_5
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0xB6000000B4000000B2000000B0)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419C43

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
        condition = Operators.AND(condition, cpu.read_int(0x419C43, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C44, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C45, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C46, 8) == ord("j"))
        condition = Operators.AND(condition, cpu.read_int(0x419C47, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.XMM0 == 0xB600000000000000B4)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419C48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHDQ_6_symbolic(self):
        """ Instruction PUNPCKHDQ_6
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0xAE000000AC000000AA000000A8)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419C43

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
        condition = Operators.AND(condition, cpu.read_int(0x419C43, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C44, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C45, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C46, 8) == ord("j"))
        condition = Operators.AND(condition, cpu.read_int(0x419C47, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.XMM0 == 0xAE00000000000000AC)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419C48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHDQ_7_symbolic(self):
        """ Instruction PUNPCKHDQ_7
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0xE0000000C0000000A00000008)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419C43

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
        condition = Operators.AND(condition, cpu.read_int(0x419C43, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C44, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C45, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C46, 8) == ord("j"))
        condition = Operators.AND(condition, cpu.read_int(0x419C47, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.XMM0 == 0xE000000000000000C)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419C48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHDQ_8_symbolic(self):
        """ Instruction PUNPCKHDQ_8
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x86000000840000008200000080)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419C43

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
        condition = Operators.AND(condition, cpu.read_int(0x419C43, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C44, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C45, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C46, 8) == ord("j"))
        condition = Operators.AND(condition, cpu.read_int(0x419C47, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x860000000000000084)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419C48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHDQ_9_symbolic(self):
        """ Instruction PUNPCKHDQ_9
            Groups: sse2
            0x419c43:	punpckhdq	xmm0, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C43, "fA\x0fj\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0xD6000000D4000000D2000000D0)
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.RIP = 0x419C43

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
        condition = Operators.AND(condition, cpu.read_int(0x419C43, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C44, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C45, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C46, 8) == ord("j"))
        condition = Operators.AND(condition, cpu.read_int(0x419C47, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.XMM0 == 0xD600000000000000D4)
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.RIP == 0x419C48)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHQDQ_1_symbolic(self):
        """ Instruction PUNPCKHQDQ_1
            Groups: sse2
            0x419c71:	punpckhqdq	xmm1, xmm1
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C71, "f\x0fm\xc9")
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CBAE800000000006CBAD8)
        cpu.RIP = 0x419C71

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
        condition = Operators.AND(condition, cpu.read_int(0x419C71, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C72, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C73, 8) == ord("m"))
        condition = Operators.AND(condition, cpu.read_int(0x419C74, 8) == ord("\xc9"))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CBAE800000000006CBAE8)
        condition = Operators.AND(condition, cpu.RIP == 0x419C75)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHQDQ_10_symbolic(self):
        """ Instruction PUNPCKHQDQ_10
            Groups: sse2
            0x419c71:	punpckhqdq	xmm1, xmm1
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C71, "f\x0fm\xc9")
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CB8E800000000006CB8D8)
        cpu.RIP = 0x419C71

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
        condition = Operators.AND(condition, cpu.read_int(0x419C71, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C72, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C73, 8) == ord("m"))
        condition = Operators.AND(condition, cpu.read_int(0x419C74, 8) == ord("\xc9"))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CB8E800000000006CB8E8)
        condition = Operators.AND(condition, cpu.RIP == 0x419C75)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHQDQ_11_symbolic(self):
        """ Instruction PUNPCKHQDQ_11
            Groups: sse2
            0x419c86:	punpckhqdq	xmm0, xmm0
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C86, "f\x0fm\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6CBA8800000000006CBA78)
        cpu.RIP = 0x419C86

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
        condition = Operators.AND(condition, cpu.read_int(0x419C88, 8) == ord("m"))
        condition = Operators.AND(condition, cpu.read_int(0x419C89, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.read_int(0x419C86, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C87, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6CBA8800000000006CBA88)
        condition = Operators.AND(condition, cpu.RIP == 0x419C8A)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHQDQ_12_symbolic(self):
        """ Instruction PUNPCKHQDQ_12
            Groups: sse2
            0x419c71:	punpckhqdq	xmm1, xmm1
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C71, "f\x0fm\xc9")
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CBAA800000000006CBA98)
        cpu.RIP = 0x419C71

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
        condition = Operators.AND(condition, cpu.read_int(0x419C71, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C72, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C73, 8) == ord("m"))
        condition = Operators.AND(condition, cpu.read_int(0x419C74, 8) == ord("\xc9"))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CBAA800000000006CBAA8)
        condition = Operators.AND(condition, cpu.RIP == 0x419C75)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHQDQ_13_symbolic(self):
        """ Instruction PUNPCKHQDQ_13
            Groups: sse2
            0x419c71:	punpckhqdq	xmm1, xmm1
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C71, "f\x0fm\xc9")
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CBEE800000000006CBED8)
        cpu.RIP = 0x419C71

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
        condition = Operators.AND(condition, cpu.read_int(0x419C71, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C72, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C73, 8) == ord("m"))
        condition = Operators.AND(condition, cpu.read_int(0x419C74, 8) == ord("\xc9"))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CBEE800000000006CBEE8)
        condition = Operators.AND(condition, cpu.RIP == 0x419C75)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHQDQ_14_symbolic(self):
        """ Instruction PUNPCKHQDQ_14
            Groups: sse2
            0x419c86:	punpckhqdq	xmm0, xmm0
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C86, "f\x0fm\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6CBF4800000000006CBF38)
        cpu.RIP = 0x419C86

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
        condition = Operators.AND(condition, cpu.read_int(0x419C88, 8) == ord("m"))
        condition = Operators.AND(condition, cpu.read_int(0x419C89, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.read_int(0x419C86, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C87, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6CBF4800000000006CBF48)
        condition = Operators.AND(condition, cpu.RIP == 0x419C8A)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHQDQ_15_symbolic(self):
        """ Instruction PUNPCKHQDQ_15
            Groups: sse2
            0x419c86:	punpckhqdq	xmm0, xmm0
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C86, "f\x0fm\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6CBDC800000000006CBDB8)
        cpu.RIP = 0x419C86

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
        condition = Operators.AND(condition, cpu.read_int(0x419C88, 8) == ord("m"))
        condition = Operators.AND(condition, cpu.read_int(0x419C89, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.read_int(0x419C86, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C87, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6CBDC800000000006CBDC8)
        condition = Operators.AND(condition, cpu.RIP == 0x419C8A)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHQDQ_16_symbolic(self):
        """ Instruction PUNPCKHQDQ_16
            Groups: sse2
            0x419c71:	punpckhqdq	xmm1, xmm1
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C71, "f\x0fm\xc9")
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CB96800000000006CB958)
        cpu.RIP = 0x419C71

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
        condition = Operators.AND(condition, cpu.read_int(0x419C71, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C72, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C73, 8) == ord("m"))
        condition = Operators.AND(condition, cpu.read_int(0x419C74, 8) == ord("\xc9"))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CB96800000000006CB968)
        condition = Operators.AND(condition, cpu.RIP == 0x419C75)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHQDQ_17_symbolic(self):
        """ Instruction PUNPCKHQDQ_17
            Groups: sse2
            0x419c86:	punpckhqdq	xmm0, xmm0
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C86, "f\x0fm\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6CBB4800000000006CBB38)
        cpu.RIP = 0x419C86

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
        condition = Operators.AND(condition, cpu.read_int(0x419C88, 8) == ord("m"))
        condition = Operators.AND(condition, cpu.read_int(0x419C89, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.read_int(0x419C86, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C87, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6CBB4800000000006CBB48)
        condition = Operators.AND(condition, cpu.RIP == 0x419C8A)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHQDQ_18_symbolic(self):
        """ Instruction PUNPCKHQDQ_18
            Groups: sse2
            0x419c86:	punpckhqdq	xmm0, xmm0
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C86, "f\x0fm\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6CB90800000000006CB8F8)
        cpu.RIP = 0x419C86

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
        condition = Operators.AND(condition, cpu.read_int(0x419C88, 8) == ord("m"))
        condition = Operators.AND(condition, cpu.read_int(0x419C89, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.read_int(0x419C86, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C87, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6CB90800000000006CB908)
        condition = Operators.AND(condition, cpu.RIP == 0x419C8A)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHQDQ_19_symbolic(self):
        """ Instruction PUNPCKHQDQ_19
            Groups: sse2
            0x419c71:	punpckhqdq	xmm1, xmm1
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C71, "f\x0fm\xc9")
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CBFE800000000006CBFD8)
        cpu.RIP = 0x419C71

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
        condition = Operators.AND(condition, cpu.read_int(0x419C71, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C72, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C73, 8) == ord("m"))
        condition = Operators.AND(condition, cpu.read_int(0x419C74, 8) == ord("\xc9"))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CBFE800000000006CBFE8)
        condition = Operators.AND(condition, cpu.RIP == 0x419C75)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHQDQ_2_symbolic(self):
        """ Instruction PUNPCKHQDQ_2
            Groups: sse2
            0x419c86:	punpckhqdq	xmm0, xmm0
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C86, "f\x0fm\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6CB88800000000006CB878)
        cpu.RIP = 0x419C86

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
        condition = Operators.AND(condition, cpu.read_int(0x419C88, 8) == ord("m"))
        condition = Operators.AND(condition, cpu.read_int(0x419C89, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.read_int(0x419C86, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C87, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6CB88800000000006CB888)
        condition = Operators.AND(condition, cpu.RIP == 0x419C8A)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHQDQ_20_symbolic(self):
        """ Instruction PUNPCKHQDQ_20
            Groups: sse2
            0x419c71:	punpckhqdq	xmm1, xmm1
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C71, "f\x0fm\xc9")
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CB92800000000006CB918)
        cpu.RIP = 0x419C71

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
        condition = Operators.AND(condition, cpu.read_int(0x419C71, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C72, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C73, 8) == ord("m"))
        condition = Operators.AND(condition, cpu.read_int(0x419C74, 8) == ord("\xc9"))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CB92800000000006CB928)
        condition = Operators.AND(condition, cpu.RIP == 0x419C75)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHQDQ_21_symbolic(self):
        """ Instruction PUNPCKHQDQ_21
            Groups: sse2
            0x419c86:	punpckhqdq	xmm0, xmm0
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C86, "f\x0fm\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6CBAC800000000006CBAB8)
        cpu.RIP = 0x419C86

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
        condition = Operators.AND(condition, cpu.read_int(0x419C88, 8) == ord("m"))
        condition = Operators.AND(condition, cpu.read_int(0x419C89, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.read_int(0x419C86, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C87, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6CBAC800000000006CBAC8)
        condition = Operators.AND(condition, cpu.RIP == 0x419C8A)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHQDQ_3_symbolic(self):
        """ Instruction PUNPCKHQDQ_3
            Groups: sse2
            0x419c71:	punpckhqdq	xmm1, xmm1
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C71, "f\x0fm\xc9")
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CBBE800000000006CBBD8)
        cpu.RIP = 0x419C71

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
        condition = Operators.AND(condition, cpu.read_int(0x419C71, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C72, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C73, 8) == ord("m"))
        condition = Operators.AND(condition, cpu.read_int(0x419C74, 8) == ord("\xc9"))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CBBE800000000006CBBE8)
        condition = Operators.AND(condition, cpu.RIP == 0x419C75)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHQDQ_4_symbolic(self):
        """ Instruction PUNPCKHQDQ_4
            Groups: sse2
            0x419c86:	punpckhqdq	xmm0, xmm0
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C86, "f\x0fm\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6CBD8800000000006CBD78)
        cpu.RIP = 0x419C86

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
        condition = Operators.AND(condition, cpu.read_int(0x419C88, 8) == ord("m"))
        condition = Operators.AND(condition, cpu.read_int(0x419C89, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.read_int(0x419C86, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C87, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6CBD8800000000006CBD88)
        condition = Operators.AND(condition, cpu.RIP == 0x419C8A)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHQDQ_5_symbolic(self):
        """ Instruction PUNPCKHQDQ_5
            Groups: sse2
            0x419c71:	punpckhqdq	xmm1, xmm1
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C71, "f\x0fm\xc9")
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CB86800000000006CB858)
        cpu.RIP = 0x419C71

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
        condition = Operators.AND(condition, cpu.read_int(0x419C71, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C72, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C73, 8) == ord("m"))
        condition = Operators.AND(condition, cpu.read_int(0x419C74, 8) == ord("\xc9"))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CB86800000000006CB868)
        condition = Operators.AND(condition, cpu.RIP == 0x419C75)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHQDQ_6_symbolic(self):
        """ Instruction PUNPCKHQDQ_6
            Groups: sse2
            0x419c71:	punpckhqdq	xmm1, xmm1
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C71, "f\x0fm\xc9")
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CBDE800000000006CBDD8)
        cpu.RIP = 0x419C71

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
        condition = Operators.AND(condition, cpu.read_int(0x419C71, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C72, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C73, 8) == ord("m"))
        condition = Operators.AND(condition, cpu.read_int(0x419C74, 8) == ord("\xc9"))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CBDE800000000006CBDE8)
        condition = Operators.AND(condition, cpu.RIP == 0x419C75)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHQDQ_7_symbolic(self):
        """ Instruction PUNPCKHQDQ_7
            Groups: sse2
            0x419c71:	punpckhqdq	xmm1, xmm1
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C71, "f\x0fm\xc9")
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CBD2800000000006CBD18)
        cpu.RIP = 0x419C71

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
        condition = Operators.AND(condition, cpu.read_int(0x419C71, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C72, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C73, 8) == ord("m"))
        condition = Operators.AND(condition, cpu.read_int(0x419C74, 8) == ord("\xc9"))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CBD2800000000006CBD28)
        condition = Operators.AND(condition, cpu.RIP == 0x419C75)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHQDQ_8_symbolic(self):
        """ Instruction PUNPCKHQDQ_8
            Groups: sse2
            0x419c71:	punpckhqdq	xmm1, xmm1
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C71, "f\x0fm\xc9")
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CB8A800000000006CB898)
        cpu.RIP = 0x419C71

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
        condition = Operators.AND(condition, cpu.read_int(0x419C71, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C72, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C73, 8) == ord("m"))
        condition = Operators.AND(condition, cpu.read_int(0x419C74, 8) == ord("\xc9"))
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CB8A800000000006CB8A8)
        condition = Operators.AND(condition, cpu.RIP == 0x419C75)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKHQDQ_9_symbolic(self):
        """ Instruction PUNPCKHQDQ_9
            Groups: sse2
            0x419c86:	punpckhqdq	xmm0, xmm0
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C86, "f\x0fm\xc0")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6CB94800000000006CB938)
        cpu.RIP = 0x419C86

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
        condition = Operators.AND(condition, cpu.read_int(0x419C88, 8) == ord("m"))
        condition = Operators.AND(condition, cpu.read_int(0x419C89, 8) == ord("\xc0"))
        condition = Operators.AND(condition, cpu.read_int(0x419C86, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C87, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6CB94800000000006CB948)
        condition = Operators.AND(condition, cpu.RIP == 0x419C8A)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLBW_1_symbolic(self):
        """ Instruction PUNPCKLBW_1
            Groups: sse2
            0x4668ac:	punpcklbw	xmm1, xmm1
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00466000, 0x1000, "rwx")
        mem.write(0x4668AC, "f\x0f`\xc9")
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x2F)
        cpu.RIP = 0x4668AC

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
        condition = Operators.AND(condition, cpu.read_int(0x4668AC, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x4668AD, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x4668AE, 8) == ord("`"))
        condition = Operators.AND(condition, cpu.read_int(0x4668AF, 8) == ord("\xc9"))
        condition = Operators.AND(condition, cpu.XMM1 == 0x2F2F)
        condition = Operators.AND(condition, cpu.RIP == 0x4668B0)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLDQ_1_symbolic(self):
        """ Instruction PUNPCKLDQ_1
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xA6000000A4000000A2000000A0)
        cpu.RIP = 0x419C48

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
        condition = Operators.AND(condition, cpu.read_int(0x419C48, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C49, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4A, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4B, 8) == ord("b"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4C, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0xA200000000000000A0)
        condition = Operators.AND(condition, cpu.RIP == 0x419C4D)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLDQ_10_symbolic(self):
        """ Instruction PUNPCKLDQ_10
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x3E0000003C0000003A00000038)
        cpu.RIP = 0x419C48

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
        condition = Operators.AND(condition, cpu.read_int(0x419C48, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C49, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4A, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4B, 8) == ord("b"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4C, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0x3A0000000000000038)
        condition = Operators.AND(condition, cpu.RIP == 0x419C4D)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLDQ_11_symbolic(self):
        """ Instruction PUNPCKLDQ_11
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6000000040000000200000000)
        cpu.RIP = 0x419C48

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
        condition = Operators.AND(condition, cpu.read_int(0x419C48, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C49, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4A, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4B, 8) == ord("b"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4C, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0x20000000000000000)
        condition = Operators.AND(condition, cpu.RIP == 0x419C4D)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLDQ_12_symbolic(self):
        """ Instruction PUNPCKLDQ_12
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x1E0000001C0000001A00000018)
        cpu.RIP = 0x419C48

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
        condition = Operators.AND(condition, cpu.read_int(0x419C48, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C49, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4A, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4B, 8) == ord("b"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4C, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0x1A0000000000000018)
        condition = Operators.AND(condition, cpu.RIP == 0x419C4D)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLDQ_13_symbolic(self):
        """ Instruction PUNPCKLDQ_13
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xE0000000C0000000A00000008)
        cpu.RIP = 0x419C48

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
        condition = Operators.AND(condition, cpu.read_int(0x419C48, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C49, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4A, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4B, 8) == ord("b"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4C, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0xA0000000000000008)
        condition = Operators.AND(condition, cpu.RIP == 0x419C4D)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLDQ_14_symbolic(self):
        """ Instruction PUNPCKLDQ_14
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xEE000000EC000000EA000000E8)
        cpu.RIP = 0x419C48

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
        condition = Operators.AND(condition, cpu.read_int(0x419C48, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C49, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4A, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4B, 8) == ord("b"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4C, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0xEA00000000000000E8)
        condition = Operators.AND(condition, cpu.RIP == 0x419C4D)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLDQ_15_symbolic(self):
        """ Instruction PUNPCKLDQ_15
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x2E0000002C0000002A00000028)
        cpu.RIP = 0x419C48

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
        condition = Operators.AND(condition, cpu.read_int(0x419C48, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C49, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4A, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4B, 8) == ord("b"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4C, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0x2A0000000000000028)
        condition = Operators.AND(condition, cpu.RIP == 0x419C4D)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLDQ_16_symbolic(self):
        """ Instruction PUNPCKLDQ_16
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xF6000000F4000000F2000000F0)
        cpu.RIP = 0x419C48

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
        condition = Operators.AND(condition, cpu.read_int(0x419C48, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C49, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4A, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4B, 8) == ord("b"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4C, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0xF200000000000000F0)
        condition = Operators.AND(condition, cpu.RIP == 0x419C4D)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLDQ_17_symbolic(self):
        """ Instruction PUNPCKLDQ_17
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x9E0000009C0000009A00000098)
        cpu.RIP = 0x419C48

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
        condition = Operators.AND(condition, cpu.read_int(0x419C48, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C49, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4A, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4B, 8) == ord("b"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4C, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0x9A0000000000000098)
        condition = Operators.AND(condition, cpu.RIP == 0x419C4D)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLDQ_18_symbolic(self):
        """ Instruction PUNPCKLDQ_18
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x16000000140000001200000010)
        cpu.RIP = 0x419C48

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
        condition = Operators.AND(condition, cpu.read_int(0x419C48, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C49, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4A, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4B, 8) == ord("b"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4C, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0x120000000000000010)
        condition = Operators.AND(condition, cpu.RIP == 0x419C4D)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLDQ_19_symbolic(self):
        """ Instruction PUNPCKLDQ_19
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x96000000940000009200000090)
        cpu.RIP = 0x419C48

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
        condition = Operators.AND(condition, cpu.read_int(0x419C48, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C49, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4A, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4B, 8) == ord("b"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4C, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0x920000000000000090)
        condition = Operators.AND(condition, cpu.RIP == 0x419C4D)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLDQ_2_symbolic(self):
        """ Instruction PUNPCKLDQ_2
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x76000000740000007200000070)
        cpu.RIP = 0x419C48

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
        condition = Operators.AND(condition, cpu.read_int(0x419C48, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C49, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4A, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4B, 8) == ord("b"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4C, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0x720000000000000070)
        condition = Operators.AND(condition, cpu.RIP == 0x419C4D)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLDQ_20_symbolic(self):
        """ Instruction PUNPCKLDQ_20
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xDE000000DC000000DA000000D8)
        cpu.RIP = 0x419C48

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
        condition = Operators.AND(condition, cpu.read_int(0x419C48, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C49, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4A, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4B, 8) == ord("b"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4C, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0xDA00000000000000D8)
        condition = Operators.AND(condition, cpu.RIP == 0x419C4D)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLDQ_21_symbolic(self):
        """ Instruction PUNPCKLDQ_21
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xE6000000E4000000E2000000E0)
        cpu.RIP = 0x419C48

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
        condition = Operators.AND(condition, cpu.read_int(0x419C48, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C49, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4A, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4B, 8) == ord("b"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4C, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0xE200000000000000E0)
        condition = Operators.AND(condition, cpu.RIP == 0x419C4D)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLDQ_3_symbolic(self):
        """ Instruction PUNPCKLDQ_3
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x36000000340000003200000030)
        cpu.RIP = 0x419C48

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
        condition = Operators.AND(condition, cpu.read_int(0x419C48, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C49, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4A, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4B, 8) == ord("b"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4C, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0x320000000000000030)
        condition = Operators.AND(condition, cpu.RIP == 0x419C4D)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLDQ_4_symbolic(self):
        """ Instruction PUNPCKLDQ_4
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6E0000006C0000006A00000068)
        cpu.RIP = 0x419C48

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
        condition = Operators.AND(condition, cpu.read_int(0x419C48, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C49, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4A, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4B, 8) == ord("b"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4C, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6A0000000000000068)
        condition = Operators.AND(condition, cpu.RIP == 0x419C4D)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLDQ_5_symbolic(self):
        """ Instruction PUNPCKLDQ_5
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x7E0000007C0000007A00000078)
        cpu.RIP = 0x419C48

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
        condition = Operators.AND(condition, cpu.read_int(0x419C48, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C49, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4A, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4B, 8) == ord("b"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4C, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0x7A0000000000000078)
        condition = Operators.AND(condition, cpu.RIP == 0x419C4D)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLDQ_6_symbolic(self):
        """ Instruction PUNPCKLDQ_6
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x26000000240000002200000020)
        cpu.RIP = 0x419C48

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
        condition = Operators.AND(condition, cpu.read_int(0x419C48, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C49, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4A, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4B, 8) == ord("b"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4C, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0x220000000000000020)
        condition = Operators.AND(condition, cpu.RIP == 0x419C4D)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLDQ_7_symbolic(self):
        """ Instruction PUNPCKLDQ_7
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xBE000000BC000000BA000000B8)
        cpu.RIP = 0x419C48

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
        condition = Operators.AND(condition, cpu.read_int(0x419C48, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C49, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4A, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4B, 8) == ord("b"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4C, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0xBA00000000000000B8)
        condition = Operators.AND(condition, cpu.RIP == 0x419C4D)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLDQ_8_symbolic(self):
        """ Instruction PUNPCKLDQ_8
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0xCE000000CC000000CA000000C8)
        cpu.RIP = 0x419C48

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
        condition = Operators.AND(condition, cpu.read_int(0x419C48, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C49, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4A, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4B, 8) == ord("b"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4C, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0xCA00000000000000C8)
        condition = Operators.AND(condition, cpu.RIP == 0x419C4D)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLDQ_9_symbolic(self):
        """ Instruction PUNPCKLDQ_9
            Groups: sse2
            0x419c48:	punpckldq	xmm1, xmm8
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C48, "fA\x0fb\xc8")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x0)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x46000000440000004200000040)
        cpu.RIP = 0x419C48

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
        condition = Operators.AND(condition, cpu.read_int(0x419C48, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C49, 8) == ord("A"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4A, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4B, 8) == ord("b"))
        condition = Operators.AND(condition, cpu.read_int(0x419C4C, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x0)
        condition = Operators.AND(condition, cpu.XMM1 == 0x420000000000000040)
        condition = Operators.AND(condition, cpu.RIP == 0x419C4D)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLQDQ_1_symbolic(self):
        """ Instruction PUNPCKLQDQ_1
            Groups: sse2
            0x419c82:	punpcklqdq	xmm1, xmm0
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C82, "f\x0fl\xc8")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6CBFC800000000006CBFB8)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CBFC800000000006CBFB8)
        cpu.RIP = 0x419C82

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
        condition = Operators.AND(condition, cpu.read_int(0x419C82, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C83, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C84, 8) == ord("l"))
        condition = Operators.AND(condition, cpu.read_int(0x419C85, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6CBFC800000000006CBFB8)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CBFB800000000006CBFB8)
        condition = Operators.AND(condition, cpu.RIP == 0x419C86)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLQDQ_10_symbolic(self):
        """ Instruction PUNPCKLQDQ_10
            Groups: sse2
            0x419c6c:	punpcklqdq	xmm8, xmm1
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C6C, "fD\x0fl\xc1")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x6CBC6800000000006CBC58)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CBC6800000000006CBC58)
        cpu.RIP = 0x419C6C

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
        condition = Operators.AND(condition, cpu.read_int(0x419C70, 8) == ord("\xc1"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6C, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6D, 8) == ord("D"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6E, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6F, 8) == ord("l"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x6CBC5800000000006CBC58)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CBC6800000000006CBC58)
        condition = Operators.AND(condition, cpu.RIP == 0x419C71)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLQDQ_11_symbolic(self):
        """ Instruction PUNPCKLQDQ_11
            Groups: sse2
            0x419c82:	punpcklqdq	xmm1, xmm0
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C82, "f\x0fl\xc8")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6CBB4800000000006CBB38)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CBB4800000000006CBB38)
        cpu.RIP = 0x419C82

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
        condition = Operators.AND(condition, cpu.read_int(0x419C82, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C83, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C84, 8) == ord("l"))
        condition = Operators.AND(condition, cpu.read_int(0x419C85, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6CBB4800000000006CBB38)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CBB3800000000006CBB38)
        condition = Operators.AND(condition, cpu.RIP == 0x419C86)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLQDQ_12_symbolic(self):
        """ Instruction PUNPCKLQDQ_12
            Groups: sse2
            0x419c6c:	punpcklqdq	xmm8, xmm1
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C6C, "fD\x0fl\xc1")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x6CBDE800000000006CBDD8)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CBDE800000000006CBDD8)
        cpu.RIP = 0x419C6C

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
        condition = Operators.AND(condition, cpu.read_int(0x419C70, 8) == ord("\xc1"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6C, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6D, 8) == ord("D"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6E, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6F, 8) == ord("l"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x6CBDD800000000006CBDD8)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CBDE800000000006CBDD8)
        condition = Operators.AND(condition, cpu.RIP == 0x419C71)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLQDQ_13_symbolic(self):
        """ Instruction PUNPCKLQDQ_13
            Groups: sse2
            0x419c6c:	punpcklqdq	xmm8, xmm1
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C6C, "fD\x0fl\xc1")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x6CBEE800000000006CBED8)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CBEE800000000006CBED8)
        cpu.RIP = 0x419C6C

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
        condition = Operators.AND(condition, cpu.read_int(0x419C70, 8) == ord("\xc1"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6C, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6D, 8) == ord("D"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6E, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6F, 8) == ord("l"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x6CBED800000000006CBED8)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CBEE800000000006CBED8)
        condition = Operators.AND(condition, cpu.RIP == 0x419C71)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLQDQ_14_symbolic(self):
        """ Instruction PUNPCKLQDQ_14
            Groups: sse2
            0x419c6c:	punpcklqdq	xmm8, xmm1
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C6C, "fD\x0fl\xc1")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x6CBBA800000000006CBB98)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CBBA800000000006CBB98)
        cpu.RIP = 0x419C6C

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
        condition = Operators.AND(condition, cpu.read_int(0x419C70, 8) == ord("\xc1"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6C, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6D, 8) == ord("D"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6E, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6F, 8) == ord("l"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x6CBB9800000000006CBB98)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CBBA800000000006CBB98)
        condition = Operators.AND(condition, cpu.RIP == 0x419C71)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLQDQ_15_symbolic(self):
        """ Instruction PUNPCKLQDQ_15
            Groups: sse2
            0x419c82:	punpcklqdq	xmm1, xmm0
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C82, "f\x0fl\xc8")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6CBCC800000000006CBCB8)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CBCC800000000006CBCB8)
        cpu.RIP = 0x419C82

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
        condition = Operators.AND(condition, cpu.read_int(0x419C82, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C83, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C84, 8) == ord("l"))
        condition = Operators.AND(condition, cpu.read_int(0x419C85, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6CBCC800000000006CBCB8)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CBCB800000000006CBCB8)
        condition = Operators.AND(condition, cpu.RIP == 0x419C86)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLQDQ_16_symbolic(self):
        """ Instruction PUNPCKLQDQ_16
            Groups: sse2
            0x419c82:	punpcklqdq	xmm1, xmm0
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C82, "f\x0fl\xc8")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6CBE0800000000006CBDF8)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CBE0800000000006CBDF8)
        cpu.RIP = 0x419C82

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
        condition = Operators.AND(condition, cpu.read_int(0x419C82, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C83, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C84, 8) == ord("l"))
        condition = Operators.AND(condition, cpu.read_int(0x419C85, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6CBE0800000000006CBDF8)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CBDF800000000006CBDF8)
        condition = Operators.AND(condition, cpu.RIP == 0x419C86)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLQDQ_17_symbolic(self):
        """ Instruction PUNPCKLQDQ_17
            Groups: sse2
            0x419c82:	punpcklqdq	xmm1, xmm0
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C82, "f\x0fl\xc8")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6CBEC800000000006CBEB8)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CBEC800000000006CBEB8)
        cpu.RIP = 0x419C82

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
        condition = Operators.AND(condition, cpu.read_int(0x419C82, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C83, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C84, 8) == ord("l"))
        condition = Operators.AND(condition, cpu.read_int(0x419C85, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6CBEC800000000006CBEB8)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CBEB800000000006CBEB8)
        condition = Operators.AND(condition, cpu.RIP == 0x419C86)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLQDQ_18_symbolic(self):
        """ Instruction PUNPCKLQDQ_18
            Groups: sse2
            0x419c6c:	punpcklqdq	xmm8, xmm1
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C6C, "fD\x0fl\xc1")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x6CBBE800000000006CBBD8)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CBBE800000000006CBBD8)
        cpu.RIP = 0x419C6C

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
        condition = Operators.AND(condition, cpu.read_int(0x419C70, 8) == ord("\xc1"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6C, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6D, 8) == ord("D"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6E, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6F, 8) == ord("l"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x6CBBD800000000006CBBD8)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CBBE800000000006CBBD8)
        condition = Operators.AND(condition, cpu.RIP == 0x419C71)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLQDQ_19_symbolic(self):
        """ Instruction PUNPCKLQDQ_19
            Groups: sse2
            0x419c82:	punpcklqdq	xmm1, xmm0
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C82, "f\x0fl\xc8")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6CBC8800000000006CBC78)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CBC8800000000006CBC78)
        cpu.RIP = 0x419C82

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
        condition = Operators.AND(condition, cpu.read_int(0x419C82, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C83, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C84, 8) == ord("l"))
        condition = Operators.AND(condition, cpu.read_int(0x419C85, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6CBC8800000000006CBC78)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CBC7800000000006CBC78)
        condition = Operators.AND(condition, cpu.RIP == 0x419C86)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLQDQ_2_symbolic(self):
        """ Instruction PUNPCKLQDQ_2
            Groups: sse2
            0x419c6c:	punpcklqdq	xmm8, xmm1
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C6C, "fD\x0fl\xc1")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x6CBF6800000000006CBF58)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CBF6800000000006CBF58)
        cpu.RIP = 0x419C6C

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
        condition = Operators.AND(condition, cpu.read_int(0x419C70, 8) == ord("\xc1"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6C, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6D, 8) == ord("D"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6E, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6F, 8) == ord("l"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x6CBF5800000000006CBF58)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CBF6800000000006CBF58)
        condition = Operators.AND(condition, cpu.RIP == 0x419C71)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLQDQ_20_symbolic(self):
        """ Instruction PUNPCKLQDQ_20
            Groups: sse2
            0x419c82:	punpcklqdq	xmm1, xmm0
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C82, "f\x0fl\xc8")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6CBA8800000000006CBA78)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CBA8800000000006CBA78)
        cpu.RIP = 0x419C82

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
        condition = Operators.AND(condition, cpu.read_int(0x419C82, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C83, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C84, 8) == ord("l"))
        condition = Operators.AND(condition, cpu.read_int(0x419C85, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6CBA8800000000006CBA78)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CBA7800000000006CBA78)
        condition = Operators.AND(condition, cpu.RIP == 0x419C86)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLQDQ_21_symbolic(self):
        """ Instruction PUNPCKLQDQ_21
            Groups: sse2
            0x419c6c:	punpcklqdq	xmm8, xmm1
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C6C, "fD\x0fl\xc1")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x6CB96800000000006CB958)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CB96800000000006CB958)
        cpu.RIP = 0x419C6C

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
        condition = Operators.AND(condition, cpu.read_int(0x419C70, 8) == ord("\xc1"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6C, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6D, 8) == ord("D"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6E, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6F, 8) == ord("l"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x6CB95800000000006CB958)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CB96800000000006CB958)
        condition = Operators.AND(condition, cpu.RIP == 0x419C71)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLQDQ_3_symbolic(self):
        """ Instruction PUNPCKLQDQ_3
            Groups: sse2
            0x419c6c:	punpcklqdq	xmm8, xmm1
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C6C, "fD\x0fl\xc1")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x6CBB2800000000006CBB18)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CBB2800000000006CBB18)
        cpu.RIP = 0x419C6C

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
        condition = Operators.AND(condition, cpu.read_int(0x419C70, 8) == ord("\xc1"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6C, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6D, 8) == ord("D"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6E, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6F, 8) == ord("l"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x6CBB1800000000006CBB18)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CBB2800000000006CBB18)
        condition = Operators.AND(condition, cpu.RIP == 0x419C71)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLQDQ_4_symbolic(self):
        """ Instruction PUNPCKLQDQ_4
            Groups: sse2
            0x419c6c:	punpcklqdq	xmm8, xmm1
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C6C, "fD\x0fl\xc1")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x6CB8A800000000006CB898)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CB8A800000000006CB898)
        cpu.RIP = 0x419C6C

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
        condition = Operators.AND(condition, cpu.read_int(0x419C70, 8) == ord("\xc1"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6C, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6D, 8) == ord("D"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6E, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6F, 8) == ord("l"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x6CB89800000000006CB898)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CB8A800000000006CB898)
        condition = Operators.AND(condition, cpu.RIP == 0x419C71)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLQDQ_5_symbolic(self):
        """ Instruction PUNPCKLQDQ_5
            Groups: sse2
            0x419c6c:	punpcklqdq	xmm8, xmm1
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C6C, "fD\x0fl\xc1")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x6CBC2800000000006CBC18)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CBC2800000000006CBC18)
        cpu.RIP = 0x419C6C

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
        condition = Operators.AND(condition, cpu.read_int(0x419C70, 8) == ord("\xc1"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6C, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6D, 8) == ord("D"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6E, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6F, 8) == ord("l"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x6CBC1800000000006CBC18)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CBC2800000000006CBC18)
        condition = Operators.AND(condition, cpu.RIP == 0x419C71)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLQDQ_6_symbolic(self):
        """ Instruction PUNPCKLQDQ_6
            Groups: sse2
            0x419c82:	punpcklqdq	xmm1, xmm0
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C82, "f\x0fl\xc8")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6CBF4800000000006CBF38)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CBF4800000000006CBF38)
        cpu.RIP = 0x419C82

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
        condition = Operators.AND(condition, cpu.read_int(0x419C82, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C83, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C84, 8) == ord("l"))
        condition = Operators.AND(condition, cpu.read_int(0x419C85, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6CBF4800000000006CBF38)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CBF3800000000006CBF38)
        condition = Operators.AND(condition, cpu.RIP == 0x419C86)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLQDQ_7_symbolic(self):
        """ Instruction PUNPCKLQDQ_7
            Groups: sse2
            0x419c6c:	punpcklqdq	xmm8, xmm1
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C6C, "fD\x0fl\xc1")
        cpu.XMM8 = cs.new_bitvec(128)
        cs.add(cpu.XMM8 == 0x6CBA6800000000006CBA58)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CBA6800000000006CBA58)
        cpu.RIP = 0x419C6C

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
        condition = Operators.AND(condition, cpu.read_int(0x419C70, 8) == ord("\xc1"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6C, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6D, 8) == ord("D"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6E, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C6F, 8) == ord("l"))
        condition = Operators.AND(condition, cpu.XMM8 == 0x6CBA5800000000006CBA58)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CBA6800000000006CBA58)
        condition = Operators.AND(condition, cpu.RIP == 0x419C71)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLQDQ_8_symbolic(self):
        """ Instruction PUNPCKLQDQ_8
            Groups: sse2
            0x419c82:	punpcklqdq	xmm1, xmm0
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C82, "f\x0fl\xc8")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6CBA0800000000006CB9F8)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CBA0800000000006CB9F8)
        cpu.RIP = 0x419C82

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
        condition = Operators.AND(condition, cpu.read_int(0x419C82, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C83, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C84, 8) == ord("l"))
        condition = Operators.AND(condition, cpu.read_int(0x419C85, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6CBA0800000000006CB9F8)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CB9F800000000006CB9F8)
        condition = Operators.AND(condition, cpu.RIP == 0x419C86)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLQDQ_9_symbolic(self):
        """ Instruction PUNPCKLQDQ_9
            Groups: sse2
            0x419c82:	punpcklqdq	xmm1, xmm0
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00419000, 0x1000, "rwx")
        mem.write(0x419C82, "f\x0fl\xc8")
        cpu.XMM0 = cs.new_bitvec(128)
        cs.add(cpu.XMM0 == 0x6CBDC800000000006CBDB8)
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x6CBDC800000000006CBDB8)
        cpu.RIP = 0x419C82

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
        condition = Operators.AND(condition, cpu.read_int(0x419C82, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C83, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.read_int(0x419C84, 8) == ord("l"))
        condition = Operators.AND(condition, cpu.read_int(0x419C85, 8) == ord("\xc8"))
        condition = Operators.AND(condition, cpu.XMM0 == 0x6CBDC800000000006CBDB8)
        condition = Operators.AND(condition, cpu.XMM1 == 0x6CBDB800000000006CBDB8)
        condition = Operators.AND(condition, cpu.RIP == 0x419C86)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))

    def test_PUNPCKLWD_1_symbolic(self):
        """ Instruction PUNPCKLWD_1
            Groups: sse2
            0x4668b6:	punpcklwd	xmm1, xmm1
        """
        cs = ConstraintSet()
        mem = SMemory64(cs)
        cpu = AMD64Cpu(mem)
        mem.mmap(0x00466000, 0x1000, "rwx")
        mem.write(0x4668B6, "f\x0fa\xc9")
        cpu.XMM1 = cs.new_bitvec(128)
        cs.add(cpu.XMM1 == 0x2F2F)
        cpu.RIP = 0x4668B6

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
        condition = Operators.AND(condition, cpu.read_int(0x4668B8, 8) == ord("a"))
        condition = Operators.AND(condition, cpu.read_int(0x4668B9, 8) == ord("\xc9"))
        condition = Operators.AND(condition, cpu.read_int(0x4668B6, 8) == ord("f"))
        condition = Operators.AND(condition, cpu.read_int(0x4668B7, 8) == ord("\x0f"))
        condition = Operators.AND(condition, cpu.XMM1 == 0x2F2F2F2F)
        condition = Operators.AND(condition, cpu.RIP == 0x4668BA)

        with cs as temp_cs:
            temp_cs.add(condition)
            self.assertTrue(solver.check(temp_cs))
        with cs as temp_cs:
            temp_cs.add(condition == False)
            self.assertFalse(solver.check(temp_cs))


if __name__ == "__main__":
    unittest.main()
