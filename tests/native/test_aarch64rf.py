import unittest

from manticore.native.cpu.aarch64 import Aarch64RegisterFile as RF

MAX_128 = 2 ** 128 - 1
MAX_64 = 2 ** 64 - 1
MAX_32 = 2 ** 32 - 1
MAX_16 = 2 ** 16 - 1
MAX_8 = 2 ** 8 - 1

MAGIC_128 = 0x41424344454647484950515253545556
MAGIC_64 = MAGIC_128 & MAX_64
MAGIC_32 = MAGIC_128 & MAX_32
MAGIC_16 = MAGIC_128 & MAX_16
MAGIC_8 = MAGIC_128 & MAX_8


# XXX: Test vectors.
class Aarch64RFTest(unittest.TestCase):
    _multiprocess_can_split_ = True

    def setUp(self):
        self.r = RF()

    def test_init_state(self):
        for i in range(31):
            self.assertEqual(self.r.read(f"X{i}"), 0)
            self.assertEqual(self.r.read(f"W{i}"), 0)

        self.assertEqual(self.r.read("SP"), 0)
        self.assertEqual(self.r.read("WSP"), 0)

        self.assertEqual(self.r.read("PC"), 0)

        for i in range(32):
            self.assertEqual(self.r.read(f"Q{i}"), 0)
            self.assertEqual(self.r.read(f"D{i}"), 0)
            self.assertEqual(self.r.read(f"S{i}"), 0)
            self.assertEqual(self.r.read(f"H{i}"), 0)
            self.assertEqual(self.r.read(f"B{i}"), 0)

        self.assertEqual(self.r.read("FPCR"), 0)
        self.assertEqual(self.r.read("FPSR"), 0)

        self.assertEqual(self.r.read("NZCV"), 0)

        self.assertEqual(self.r.read("XZR"), 0)
        self.assertEqual(self.r.read("WZR"), 0)

        # Aliases.
        self.assertEqual(self.r.read("STACK"), 0)
        self.assertEqual(self.r.read("FP"), 0)
        self.assertEqual(self.r.read("IP1"), 0)
        self.assertEqual(self.r.read("IP0"), 0)
        self.assertEqual(self.r.read("LR"), 0)

    def test_register_independence(self):
        for i in range(31):
            self.r.write(f"X{i}", i)

        self.r.write("SP", 31)
        self.r.write("PC", 32)

        for i in range(33, 65):
            self.r.write(f"Q{i - 33}", i)

        self.r.write("FPCR", 65)
        self.r.write("FPSR", 66)
        self.r.write("NZCV", 67)
        self.r.write("XZR", 68)

        for i in range(31):
            self.assertEqual(self.r.read(f"X{i}"), i)
            self.assertEqual(self.r.read(f"W{i}"), i)

        self.assertEqual(self.r.read("IP0"), 16)
        self.assertEqual(self.r.read("IP1"), 17)
        self.assertEqual(self.r.read("FP"), 29)
        self.assertEqual(self.r.read("LR"), 30)

        self.assertEqual(self.r.read("STACK"), 31)
        self.assertEqual(self.r.read("SP"), 31)
        self.assertEqual(self.r.read("WSP"), 31)

        self.assertEqual(self.r.read("PC"), 32)

        for i in range(33, 65):
            self.assertEqual(self.r.read(f"Q{i - 33}"), i)
            self.assertEqual(self.r.read(f"D{i - 33}"), i)
            self.assertEqual(self.r.read(f"S{i - 33}"), i)
            self.assertEqual(self.r.read(f"H{i - 33}"), i)
            self.assertEqual(self.r.read(f"B{i - 33}"), i)

        self.assertEqual(self.r.read("FPCR"), 65)
        self.assertEqual(self.r.read("FPSR"), 66)
        self.assertEqual(self.r.read("NZCV"), 67)
        self.assertEqual(self.r.read("XZR"), 0)
        self.assertEqual(self.r.read("WZR"), 0)

    def test_write_read_same(self):
        self.r.write("PC", MAGIC_64)
        self.assertEqual(self.r.read("PC"), MAGIC_64)

        self.r.write("FPCR", MAGIC_64)
        self.assertEqual(self.r.read("FPCR"), MAGIC_64)

        self.r.write("FPSR", MAGIC_64)
        self.assertEqual(self.r.read("FPSR"), MAGIC_64)

        self.r.write("NZCV", MAGIC_64)
        self.assertEqual(self.r.read("NZCV"), MAGIC_64)

    def test_write_read_large_small(self):
        for i in range(31):
            self.r.write(f"X{i}", MAGIC_64)
            self.assertEqual(self.r.read(f"X{i}"), MAGIC_64)
            self.assertEqual(self.r.read(f"W{i}"), MAGIC_32)

        self.assertEqual(self.r.read("IP0"), MAGIC_64)
        self.assertEqual(self.r.read("IP1"), MAGIC_64)
        self.assertEqual(self.r.read("FP"), MAGIC_64)
        self.assertEqual(self.r.read("LR"), MAGIC_64)

        self.r.write("SP", MAGIC_64)
        self.assertEqual(self.r.read("STACK"), MAGIC_64)
        self.assertEqual(self.r.read("SP"), MAGIC_64)
        self.assertEqual(self.r.read("WSP"), MAGIC_32)

        for i in range(32):
            self.r.write(f"Q{i}", MAGIC_128)
            self.assertEqual(self.r.read(f"Q{i}"), MAGIC_128)
            self.assertEqual(self.r.read(f"D{i}"), MAGIC_64)
            self.assertEqual(self.r.read(f"S{i}"), MAGIC_32)
            self.assertEqual(self.r.read(f"H{i}"), MAGIC_16)
            self.assertEqual(self.r.read(f"B{i}"), MAGIC_8)

        self.r.write("XZR", MAGIC_64)
        self.assertEqual(self.r.read("XZR"), 0)
        self.assertEqual(self.r.read("WZR"), 0)

    def test_write_read_small_large(self):
        for i in range(31):
            self.r.write(f"W{i}", MAGIC_32)
            self.assertEqual(self.r.read(f"X{i}"), MAGIC_32)
            self.assertEqual(self.r.read(f"W{i}"), MAGIC_32)

        self.assertEqual(self.r.read("IP0"), MAGIC_32)
        self.assertEqual(self.r.read("IP1"), MAGIC_32)
        self.assertEqual(self.r.read("FP"), MAGIC_32)
        self.assertEqual(self.r.read("LR"), MAGIC_32)

        self.r.write("WSP", MAGIC_32)
        self.assertEqual(self.r.read("STACK"), MAGIC_32)
        self.assertEqual(self.r.read("SP"), MAGIC_32)
        self.assertEqual(self.r.read("WSP"), MAGIC_32)

        for i in range(32):
            self.r.write(f"B{i}", MAGIC_8)
            self.assertEqual(self.r.read(f"Q{i}"), MAGIC_8)

            self.r.write(f"H{i}", MAGIC_16)
            self.assertEqual(self.r.read(f"Q{i}"), MAGIC_16)

            self.r.write(f"S{i}", MAGIC_32)
            self.assertEqual(self.r.read(f"Q{i}"), MAGIC_32)

            self.r.write(f"D{i}", MAGIC_64)
            self.assertEqual(self.r.read(f"Q{i}"), MAGIC_64)

            self.r.write(f"Q{i}", MAGIC_128)
            self.assertEqual(self.r.read(f"Q{i}"), MAGIC_128)

        self.r.write("WZR", MAGIC_32)
        self.assertEqual(self.r.read("XZR"), 0)
        self.assertEqual(self.r.read("WZR"), 0)

    def test_invalid_write_size(self):
        with self.assertRaises(AssertionError):
            self.r.write("PC", MAX_64 + 1)

        with self.assertRaises(AssertionError):
            self.r.write("FPCR", MAX_64 + 1)

        with self.assertRaises(AssertionError):
            self.r.write("FPSR", MAX_64 + 1)

        with self.assertRaises(AssertionError):
            self.r.write("NZCV", MAX_64 + 1)

        for i in range(31):
            with self.assertRaises(AssertionError):
                self.r.write(f"X{i}", MAX_64 + 1)
            with self.assertRaises(AssertionError):
                self.r.write(f"W{i}", MAX_32 + 1)

        with self.assertRaises(AssertionError):
            self.r.write("SP", MAX_64 + 1)
        with self.assertRaises(AssertionError):
            self.r.write("WSP", MAX_32 + 1)

        for i in range(32):
            with self.assertRaises(AssertionError):
                self.r.write(f"B{i}", MAX_8 + 1)
            with self.assertRaises(AssertionError):
                self.r.write(f"H{i}", MAX_16 + 1)
            with self.assertRaises(AssertionError):
                self.r.write(f"S{i}", MAX_32 + 1)
            with self.assertRaises(AssertionError):
                self.r.write(f"D{i}", MAX_64 + 1)
            with self.assertRaises(AssertionError):
                self.r.write(f"Q{i}", MAX_128 + 1)

        with self.assertRaises(AssertionError):
            self.r.write("XZR", MAX_64 + 1)
        with self.assertRaises(AssertionError):
            self.r.write("WZR", MAX_32 + 1)

        # Aliases.
        with self.assertRaises(AssertionError):
            self.r.write("STACK", MAX_64 + 1)
        with self.assertRaises(AssertionError):
            self.r.write("FP", MAX_64 + 1)
        with self.assertRaises(AssertionError):
            self.r.write("IP1", MAX_64 + 1)
        with self.assertRaises(AssertionError):
            self.r.write("IP0", MAX_64 + 1)
        with self.assertRaises(AssertionError):
            self.r.write("LR", MAX_64 + 1)

    def test_invalid_write_name(self):
        with self.assertRaises(AssertionError):
            self.r.write("INVALID", 42)

    def test_invalid_read_name(self):
        with self.assertRaises(AssertionError):
            self.r.read("INVALID")

    # Write to aliases first.
    def test_write_read_aliases(self):
        self.r.write("STACK", MAGIC_64)
        self.assertEqual(self.r.read("STACK"), MAGIC_64)
        self.assertEqual(self.r.read("SP"), MAGIC_64)
        self.assertEqual(self.r.read("WSP"), MAGIC_32)

        self.r.write("FP", MAGIC_64)
        self.assertEqual(self.r.read("FP"), MAGIC_64)
        self.assertEqual(self.r.read("X29"), MAGIC_64)

        self.r.write("IP1", MAGIC_64)
        self.assertEqual(self.r.read("IP1"), MAGIC_64)
        self.assertEqual(self.r.read("X17"), MAGIC_64)

        self.r.write("IP0", MAGIC_64)
        self.assertEqual(self.r.read("IP0"), MAGIC_64)
        self.assertEqual(self.r.read("X16"), MAGIC_64)

        self.r.write("LR", MAGIC_64)
        self.assertEqual(self.r.read("LR"), MAGIC_64)
        self.assertEqual(self.r.read("X30"), MAGIC_64)
