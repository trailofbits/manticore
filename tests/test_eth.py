import struct
import unittest
import os

from manticore.ethereum import ManticoreEVM, IntegerOverflow
from manticore.ethereum import ABI

THIS_DIR = os.path.dirname(os.path.abspath(__file__))

# FIXME(mark): Remove these two lines when logging works for ManticoreEVM
from manticore.utils.log import init_logging
init_logging()

class EthDetectors(unittest.TestCase):
    def test_int_ovf(self):
        mevm = ManticoreEVM()
        mevm.register_detector(IntegerOverflow())
        filename = os.path.join(THIS_DIR, 'binaries/int_overflow.sol')
        mevm.multi_tx_analysis(filename)
        self.assertEqual(len(mevm.global_findings), 3)
        all_findings = ''.join(map(lambda x: x[2], mevm.global_findings))
        self.assertIn('underflow at SUB', all_findings)
        self.assertIn('overflow at ADD', all_findings)
        self.assertIn('overflow at MUL', all_findings)

class EthereumAbiTests(unittest.TestCase):
    @staticmethod
    def _pack_int_to_32(x):
        return '\x00' * 28 + struct.pack('>I', x)

    def test_dyn_address(self):
        d = [
            'AAAA',                    # function hash
            self._pack_int_to_32(32),  # offset to data start
            self._pack_int_to_32(2),   # data start; # of elements
            self._pack_int_to_32(42),  # element 1
            self._pack_int_to_32(43),  # element 2
        ]
        d = ''.join(d)

        funcname, dynargs = ABI.parse(type_spec='func(address[])', data=d)

        self.assertEqual(funcname, 'func')
        self.assertEqual(dynargs, ([42, 43],))

    def test_dyn_bytes(self):
        d = [
            'AAAA',                    # function hash
            self._pack_int_to_32(32),  # offset to data start
            self._pack_int_to_32(30),   # data start; # of elements
            'Z'*30, '\x00'*2
        ]
        d = ''.join(d)

        funcname, dynargs = ABI.parse(type_spec='func(bytes)', data=d)

        self.assertEqual(funcname, 'func')
        self.assertEqual(dynargs, ('Z'*30,))

    def test_mult_dyn_types(self):
        d = [
            'AAAA',                    # function hash
            self._pack_int_to_32(0x40),  # offset to data 1 start
            self._pack_int_to_32(0x80),  # offset to data 2 start
            self._pack_int_to_32(10),  # data 1 size
            'helloworld'.ljust(32, '\x00'), # data 1
            self._pack_int_to_32(3),  # data 2 size
            self._pack_int_to_32(3),  # data 2
            self._pack_int_to_32(4),
            self._pack_int_to_32(5),
        ]
        d = ''.join(d)

        funcname, dynargs = ABI.parse(type_spec='func(bytes,address[])', data=d)

        self.assertEqual(funcname, 'func')
        self.assertEqual(dynargs, ('helloworld', [3, 4, 5]))

    def test_self_make_and_parse_multi_dyn(self):
        d = ABI.make_function_call('func', 'h'*50, [1, 1, 2, 2, 3, 3] )
        d = ''.join(d)
        funcname, dynargs = ABI.parse(type_spec='func(bytes,address[])', data=d)
        self.assertEqual(funcname, 'func')
        self.assertEqual(dynargs, ('h'*50, [1, 1, 2, 2, 3, 3]))
