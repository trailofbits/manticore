import unittest
 
from manticore.core.cpu import bitwise


class Armv7RF(unittest.TestCase):

    def test_mask(self):
        masked = bitwise.Mask(8)
        self.assertEqual(masked, 0xff)

    def test_get_bits(self):
        val = 0xAABBCCDD
        result = bitwise.GetNBits(val, 8)
        self.assertEqual(result, 0xDD)

    def test_lsl_nocarry(self):
        val = 0xAA00
        result, carry = bitwise.LSL_C(val, 4, 32)
        self.assertEqual(result, 0x0AA000)
        self.assertEqual(carry , 0)

    def test_lsl_carry(self):
        val = 0x80000000
        result, carry = bitwise.LSL_C(val, 1, 32)
        print hex(result), "", hex(carry)
        self.assertEqual(result, 0)
        self.assertEqual(carry , 1)

    def test_lsr_nocarry(self):
        val = 0xFFF7
        result, carry = bitwise.LSR_C(val, 4, 32)
        self.assertEqual(result, 0x0FFF)
        self.assertEqual(carry , 0)

    def test_lsr_carry(self):
        val = 0xFFF8
        result, carry = bitwise.LSR_C(val, 4, 32)
        self.assertEqual(result, 0x0FFF)
        self.assertEqual(carry , 1)

    def test_asr_nocarry(self):
        val = 0x00F0
        result, carry = bitwise.ASR_C(val, 4, 32)
        self.assertEqual(result, 0xF)
        self.assertEqual(carry, 0)

    def test_asr_carry(self):
        val = 0x0003
        result, carry = bitwise.ASR_C(val, 1, 32)
        self.assertEqual(result, 1)
        self.assertEqual(carry, 1)

    def test_ror_nocarry(self):
        val = 0x00F0
        result, carry = bitwise.ROR_C(val, 4, 32)
        print hex(result)
        self.assertEqual(result, 0xF)
        self.assertEqual(carry, 0)

    def test_ror_carry(self):
        val = 0x0003
        result, carry = bitwise.ROR_C(val, 1, 32)
        print hex(result)
        self.assertEqual(result, 0x80000001)
        self.assertEqual(carry, 1)

    def test_rrx_nocarry(self):
        val = 0x000F
        result, carry = bitwise.RRX_C(val, 0, 32)
        self.assertEqual(result, 0x7)
        self.assertEqual(carry, 1)

    def test_rrx_carry(self):
        val = 0x0001
        result, carry = bitwise.RRX_C(val, 1, 32)
        print hex(result)
        self.assertEqual(result, 0x80000000)
        self.assertEqual(carry, 1)

    def test_sint(self):
        val = 0xFFFFFFFF
        result = bitwise.SInt(val, 32)
        self.assertEqual(result, -1)

    def test_sint_2(self):
        val = 0xFFFFFFFE
        result = bitwise.SInt(val, 32)
        self.assertEqual(result, -2)
