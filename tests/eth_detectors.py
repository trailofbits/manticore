"""
File name is purposefully not test_* to run this test separately.
"""

import inspect
import shutil
import struct
import tempfile
import unittest
import os

from manticore.core.smtlib import operators
from eth_general import make_mock_evm_state
from manticore.ethereum import ManticoreEVM, DetectInvalid, DetectIntegerOverflow, Detector, NoAliveStates, ABI, \
    EthereumError, DetectReentrancyAdvanced, DetectUnusedRetVal, DetectSelfdestruct, LoopDepthLimiter, DetectEtherLeak

import shutil

THIS_DIR = os.path.dirname(os.path.abspath(__file__))

# FIXME(mark): Remove these two lines when logging works for ManticoreEVM
from manticore.utils.log import init_logging, set_verbosity

init_logging()
set_verbosity(0)


class EthDetectorTest(unittest.TestCase):
    """
    Subclasses must assign this class variable to the class for the detector
    """
    DETECTOR_CLASS = None

    def setUp(self):
        self.mevm = ManticoreEVM()
        self.mevm.verbosity(0)
        self.worksp = self.mevm.workspace

    def tearDown(self):
        self.mevm = None
        shutil.rmtree(self.worksp)

    def _test(self, name, should_find):
        """
        Tests DetectInvalid over the consensys benchmark suit
        """
        mevm = self.mevm

        filename = os.path.join(THIS_DIR, 'binaries', 'detectors', '{}.sol'.format(name))

        self.mevm.register_detector(self.DETECTOR_CLASS())
        mevm.multi_tx_analysis(filename, contract_name='DetectThis', args=(mevm.make_symbolic_value(),))

        expected_findings = set(((c, d) for b, c, d in should_find))
        actual_findings = set(((c, d) for a, b, c, d in mevm.global_findings))
        self.assertEqual(expected_findings, actual_findings)

class EthRetVal(EthDetectorTest):
    """ https://consensys.net/diligence/evm-analyzer-benchmark-suite/ """
    DETECTOR_CLASS = DetectUnusedRetVal

    def test_retval_ok(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    def test_retval_not_ok(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {(337, 'Returned value at CALL instruction is not used', False)})

    def test_retval_crazy(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    def test_retval_lunatic(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())


class EthSelfdestruct(EthDetectorTest):
    DETECTOR_CLASS = DetectSelfdestruct

    def test_selfdestruct_true_pos(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {(307, 'Reachable SELFDESTRUCT', False)})

    def test_selfdestruct_true_pos1(self):
        self.mevm.register_plugin(LoopDepthLimiter(2))
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {(307, 'Reachable SELFDESTRUCT', False)})

    def test_selfdestruct_true_neg(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    def test_selfdestruct_true_neg1(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())


class EthEtherLeak(EthDetectorTest):
    DETECTOR_CLASS = DetectEtherLeak

    def test_etherleak_true_neg(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    def test_etherleak_true_neg1(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    def test_etherleak_true_neg2(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    def test_etherleak_true_neg3(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    def test_etherleak_true_pos_argument(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {(0x1c5, "Reachable ether leak to sender via argument", False)})

    def test_etherleak_true_pos_argument1(self):
        self.mevm.register_plugin(LoopDepthLimiter(5))
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {(0x1c5, "Reachable ether leak to sender via argument", False)})

    def test_etherleak_true_pos_argument2(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {(0x1c5, "Reachable ether leak to user controlled address via argument", False)})

    def test_etherleak_true_pos_msgsender(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {(0x1c5, "Reachable ether leak to sender", False)})

    def test_etherleak_true_pos_msgsender1(self):
        self.mevm.register_plugin(LoopDepthLimiter(5))
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {(0x1c5, "Reachable ether leak to sender", False)})


class EthIntegerOverflow(unittest.TestCase):
    def setUp(self):
        self.io = DetectIntegerOverflow()
        self.state = make_mock_evm_state()

    def test_mul_no_overflow(self):
        """
        Regression test added for issue 714, where we were using the ADD ovf check for MUL
        """
        arguments = [1 << 248, self.state.new_symbolic_value(256)]
        self.state.constrain(operators.ULT(arguments[1], 256))

        cond = self.io._unsigned_mul_overflow(self.state, *arguments)
        check = self.state.can_be_true(cond)
        self.assertFalse(check)

    def test_mul_overflow0(self):
        arguments = [1 << 249, self.state.new_symbolic_value(256)]
        self.state.constrain(operators.ULT(arguments[1], 256))

        cond = self.io._unsigned_mul_overflow(self.state, *arguments)
        check = self.state.can_be_true(cond)
        self.assertTrue(check)

    def test_mul_overflow1(self):
        arguments = [1 << 255, self.state.new_symbolic_value(256)]

        cond = self.io._unsigned_mul_overflow(self.state, *arguments)
        check = self.state.can_be_true(cond)
        self.assertTrue(check)


