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
    EthereumError, DetectReentrancySimple, DetectReentrancyAdvanced, DetectUnusedRetVal, DetectSelfdestruct, LoopDepthLimiter, DetectDelegatecall, \
    DetectEnvInstruction, DetectExternalCallAndLeak, DetectEnvInstruction

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

    def _test(self, name, should_find, use_ctor_sym_arg=False):
        """
        Tests DetectInvalid over the consensys benchmark suit
        """
        mevm = self.mevm

        filename = os.path.join(THIS_DIR, 'binaries', 'detectors', f'{name}.sol')

        if use_ctor_sym_arg:
            ctor_arg = (mevm.make_symbolic_value(),)
        else:
            ctor_arg = ()

        self.mevm.register_detector(self.DETECTOR_CLASS())
        mevm.multi_tx_analysis(filename, contract_name='DetectThis', args=ctor_arg)

        expected_findings = set(((c, d) for b, c, d in should_find))
        actual_findings = set(((c, d) for a, b, c, d in mevm.global_findings))
        self.assertEqual(expected_findings, actual_findings)

class EthRetVal(EthDetectorTest):
    """ Detect when a return value of a low level transaction instruction is ignored """
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


class EthExternalCallAndLeak(EthDetectorTest):
    DETECTOR_CLASS = DetectExternalCallAndLeak

    def test_etherleak_true_neg(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    def test_etherleak_true_neg1(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    def test_etherleak_true_neg2(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {(0x1c5, "Reachable external call to sender", False)})

    def test_etherleak_true_neg3(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {(0x1c5, "Reachable external call to sender", False)})

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
        self._test(name, {(0x1c5, "Reachable external call to sender", False), (0x1c5, "Reachable ether leak to sender", False)})

    def test_etherleak_true_pos_msgsender1(self):
        self.mevm.register_plugin(LoopDepthLimiter(5))
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {(0x1c5, "Reachable external call to sender", False), (0x1c5, "Reachable ether leak to sender", False)})


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

class DetectEnvInstruction(EthDetectorTest):
    DETECTOR_CLASS = DetectEnvInstruction

    def test_predictable_not_ok(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {(174, 'Warning ORIGIN instruction used', False), (157, 'Warning DIFFICULTY instruction used', False), (129, 'Warning TIMESTAMP instruction used', False), (165, 'Warning NUMBER instruction used', False), (132, 'Warning COINBASE instruction used', False), (167, 'Warning BLOCKHASH instruction used', False), (160, 'Warning NUMBER instruction used', False), (199, 'Warning GASPRICE instruction used', False), (202, 'Warning GASLIMIT instruction used', False)})



class EthDelegatecall(EthDetectorTest):
    """ Test the detection of funny delegatecalls """
    DETECTOR_CLASS = DetectDelegatecall

    def test_delegatecall_ok(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    def test_delegatecall_ok1(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    def test_delegatecall_ok2(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    @unittest.skip("Too slow for this modern times")
    def test_delegatecall_ok3(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    def test_delegatecall_not_ok(self):
        self.mevm.register_plugin(LoopDepthLimiter())
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {(179, 'Delegatecall to user controlled function', False), (179, 'Delegatecall to user controlled address', False)})

    @unittest.skip("Too slow for this modern times")
    def test_delegatecall_not_ok1(self):
        self.mevm.register_plugin(LoopDepthLimiter(loop_count_threshold=500))
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {(179, 'Delegatecall to user controlled function', False)})


