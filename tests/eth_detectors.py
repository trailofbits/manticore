"""
File name is purposefully not test_* to run this test separately.
"""

import inspect
import unittest

import os
import shutil
from eth_general import make_mock_evm_state

from manticore.core.smtlib import operators
from manticore.ethereum import ManticoreEVM, DetectIntegerOverflow, DetectUnusedRetVal, DetectSelfdestruct, \
    LoopDepthLimiter, DetectDelegatecall, \
    DetectExternalCallAndLeak, DetectEnvInstruction, DetectRaceCondition

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

        expected_findings = set(((finding, at_init) for finding, at_init in should_find))
        actual_findings = set(((finding, at_init) for _addr, _pc, finding, at_init in mevm.global_findings))
        self.assertEqual(expected_findings, actual_findings)


class EthRetVal(EthDetectorTest):
    """ Detect when a return value of a low level transaction instruction is ignored """
    DETECTOR_CLASS = DetectUnusedRetVal

    def test_retval_ok(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    def test_retval_not_ok(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {('Returned value at CALL instruction is not used', False)})

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
        self._test(name, {('Reachable SELFDESTRUCT', False)})

    def test_selfdestruct_true_pos1(self):
        self.mevm.register_plugin(LoopDepthLimiter(2))
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {('Reachable SELFDESTRUCT', False)})

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
        self._test(name, {("Reachable external call to sender", False)})

    def test_etherleak_true_neg3(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {("Reachable external call to sender", False)})

    def test_etherleak_true_pos_argument(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {("Reachable ether leak to sender via argument", False)})

    def test_etherleak_true_pos_argument1(self):
        self.mevm.register_plugin(LoopDepthLimiter(5))
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {("Reachable ether leak to sender via argument", False)})

    def test_etherleak_true_pos_argument2(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {("Reachable ether leak to user controlled address via argument", False)})

    def test_etherleak_true_pos_msgsender(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {("Reachable external call to sender", False),
                          ("Reachable ether leak to sender", False)})

    def test_etherleak_true_pos_msgsender1(self):
        self.mevm.register_plugin(LoopDepthLimiter(5))
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {("Reachable external call to sender", False),
                          ("Reachable ether leak to sender", False)})


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
        self._test(name, {('Warning ORIGIN instruction used', False),
                          ('Warning DIFFICULTY instruction used', False),
                          ('Warning TIMESTAMP instruction used', False),
                          ('Warning NUMBER instruction used', False),
                          ('Warning COINBASE instruction used', False),
                          ('Warning BLOCKHASH instruction used', False),
                          ('Warning NUMBER instruction used', False),
                          ('Warning GASPRICE instruction used', False),
                          ('Warning GASLIMIT instruction used', False)})


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
        self._test(name, {('Delegatecall to user controlled function', False),
                          ('Delegatecall to user controlled address', False)})

    @unittest.skip("Too slow for this modern times")
    def test_delegatecall_not_ok1(self):
        self.mevm.register_plugin(LoopDepthLimiter(loop_count_threshold=500))
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {('Delegatecall to user controlled function', False)})


class EthRaceCondition(EthDetectorTest):
    DETECTOR_CLASS = DetectRaceCondition

    def test_race_condition(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {
            (
                'Potential race condition (transaction order dependency):\n'
                'Value has been stored in storage slot/index 0 in transaction that called setStoredAddress(address)'
                ' and is now used in transaction that calls callStoredAddress().\n'
                'An attacker seeing a transaction to callStoredAddress() could create a transaction to '
                'setStoredAddress(address) with high gas and win a race.',
                False
            ),
            (
                'Potential race condition (transaction order dependency):\n'
                'Value has been stored in storage slot/index 0 in transaction that called setStoredAddress(address)'
                ' and is now used in transaction that calls stored_address().\nAn attacker seeing a transaction to'
                ' stored_address() could create a transaction to setStoredAddress(address) '
                'with high gas and win a race.',
                False
            ),
            (
                'Potential race condition (transaction order dependency):\n'
                'Value has been stored in storage slot/index 0 in transaction that called setStoredAddress(address)'
                ' and is now used in transaction that calls setStoredAddress(address).\n'
                'An attacker seeing a transaction to setStoredAddress(address) could create a transaction to'
                ' setStoredAddress(address) with high gas and win a race.',
                False
            )
        })

    def test_race_condition2(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {
            (
                'Potential race condition (transaction order dependency):\n'
                'Value has been stored in storage slot/index which is symbolic in transaction that called'
                ' transfer(address,uint256) and is now used in transaction that calls withdrawBalance().\n'
                'An attacker seeing a transaction to withdrawBalance() could create a transaction to'
                ' transfer(address,uint256) with high gas and win a race.',
                False
            ),
            (
                'Potential race condition (transaction order dependency):\n'
                'Value has been stored in storage slot/index'
                ' 78115272392584470974389034602766755727256711949031588331321780670270669005627 in transaction'
                ' that called withdrawBalance() and is now used in transaction that calls transfer(address,uint256).\n'
                'An attacker seeing a transaction to transfer(address,uint256) could create a transaction to'
                ' withdrawBalance() with high gas and win a race.',
                False
            ),
            (
                'Potential race condition (transaction order dependency):\n'
                'Value has been stored in storage slot/index'
                ' 78115272392584470974389034602766755727256711949031588331321780670270669005627 in transaction'
                ' that called withdrawBalance() and is now used in transaction that calls withdrawBalance().\n'
                'An attacker seeing a transaction to withdrawBalance() could create a transaction to withdrawBalance()'
                ' with high gas and win a race.',
                False
            ),
            (
                'Potential race condition (transaction order dependency):\n'
                'Value has been stored in storage slot/index'
                ' 78115272392584470974389034602766755727256711949031588331321780670270669005627 in transaction'
                ' that called transfer(address,uint256) and is now used in transaction that calls withdrawBalance().\n'
                'An attacker seeing a transaction to withdrawBalance() could create a transaction to'
                ' transfer(address,uint256) with high gas and win a race.',
                False
            ),
            (
                'Potential race condition (transaction order dependency):\n'
                'Value has been stored in storage slot/index which is symbolic in transaction that called'
                ' transfer(address,uint256) and is now used in transaction that calls transfer(address,uint256).\n'
                'An attacker seeing a transaction to transfer(address,uint256) could create a transaction to'
                ' transfer(address,uint256) with high gas and win a race.',
                False
            ),
            (
                'Potential race condition (transaction order dependency):\n'
                'Value has been stored in storage slot/index'
                ' 78115272392584470974389034602766755727256711949031588331321780670270669005627 in transaction'
                ' that called transfer(address,uint256) and is now used in transaction that calls'
                ' transfer(address,uint256).\nAn attacker seeing a transaction to transfer(address,uint256)'
                ' could create a transaction to transfer(address,uint256) with high gas and win a race.',
                False
            )
        })
