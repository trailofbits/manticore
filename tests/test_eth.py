import struct
import unittest
import os

from manticore.core.smtlib import ConstraintSet, operators
from manticore.core.state import State
from manticore.ethereum import ManticoreEVM, IntegerOverflow, Detector, ABI
from manticore.platforms.evm import EVMWorld

THIS_DIR = os.path.dirname(os.path.abspath(__file__))

# FIXME(mark): Remove these two lines when logging works for ManticoreEVM
from manticore.utils.log import init_logging

init_logging()


class EthDetectorsIntegrationTest(unittest.TestCase):
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

    def test_simple_types(self):
        d = [
            'AAAA',                    # function hash
            self._pack_int_to_32(32),
            '\xff' * 32,
            '\xff'.rjust(32, '\0'),
            self._pack_int_to_32(0x424242),
            '\x7f' + '\xff' *31, # int256 max
            '\x80'.ljust(32, '\0'), # int256 min


        ]
        d = ''.join(d)

        funcname, dynargs = ABI.parse(type_spec='func(uint256,uint256,bool,address,int256,int256)', data=d)

        self.assertEqual(funcname, 'func')
        self.assertEqual(dynargs, (32, 2**256 - 1, 0xff, 0x424242, 2**255 - 1,-(2**255) ))

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


class EthDetectors(unittest.TestCase):
    def setUp(self):
        self.io = IntegerOverflow()
        self.state = self.make_mock_evm_state()

    @staticmethod
    def make_mock_evm_state():
        cs = ConstraintSet()
        fakestate = State(cs, EVMWorld(cs))
        return fakestate

    def test_mul_no_overflow(self):
        """
        Regression test added for issue 714, where we were using the ADD ovf check for MUL
        """
        arguments = [1 << (8 * 31), self.state.new_symbolic_value(256)]
        self.state.constrain(operators.ULT(arguments[1], 256))

        # TODO(mark) We should actually call into the EVM cpu here, and below, rather than
        # effectively copy pasting what the MUL does
        result = arguments[0] * arguments[1]

        check = self.io._can_mul_overflow(self.state, result, *arguments)
        self.assertFalse(check)

    def test_mul_overflow0(self):
        arguments = [2 << (8 * 31), self.state.new_symbolic_value(256)]
        self.state.constrain(operators.ULT(arguments[1], 256))

        result = arguments[0] * arguments[1]

        check = self.io._can_mul_overflow(self.state, result, *arguments)
        self.assertTrue(check)

    def test_mul_overflow1(self):
        arguments = [1 << 255, self.state.new_symbolic_value(256)]

        result = arguments[0] * arguments[1]

        check = self.io._can_mul_overflow(self.state, result, *arguments)
        self.assertTrue(check)


class EthTests(unittest.TestCase):
    def test_emit_did_execute_end_instructions(self):
        class TestDetector(Detector):
            def did_evm_execute_instruction_callback(self, state, instruction, arguments, result):
                if instruction.semantics in ('REVERT', 'STOP'):
                    with self.locked_context('insns', dict) as d:
                        d[instruction.semantics] = True

        mevm = ManticoreEVM()
        p = TestDetector()
        mevm.register_detector(p)

        filename = os.path.join(THIS_DIR, 'binaries/int_overflow.sol')
        mevm.multi_tx_analysis(filename, tx_limit=1)

        self.assertIn('insns', p.context)
        context = p.context['insns']
        self.assertIn('STOP', context)
        self.assertIn('REVERT', context)
