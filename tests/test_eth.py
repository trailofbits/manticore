import unittest
import os

from manticore.core.smtlib import ConstraintSet
from manticore.core.state import State
from manticore.ethereum import ManticoreEVM, IntegerOverflow, Detector
from manticore.platforms.evm import EVMWorld

THIS_DIR = os.path.dirname(os.path.abspath(__file__))

# FIXME(mark): Remove these two lines when logging works for ManticoreEVM
from manticore.utils.log import init_logging
init_logging()

class EthDetectors(unittest.TestCase):
    @staticmethod
    def make_mock_evm_state():
        cs = ConstraintSet()
        fakestate = State(cs, EVMWorld(cs))
        return fakestate

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

    def test_mul_no_overflow(self):
        """
        Regression test added for issue 714, where we were using the ADD ovf check for MUL
        """
        io = IntegerOverflow()
        state = self.make_mock_evm_state()
        arguments = [1 << (8 * 31), state.new_symbolic_value(8)]
        result = arguments[0] * arguments[1]

        check = io._can_mul_overflow(state, arguments, result)
        self.assertFalse(check)

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
