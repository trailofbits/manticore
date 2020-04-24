"""
File name is purposefully not test_* to run this test separately.
"""

import inspect
import unittest

import os
import shutil
from manticore.platforms.evm import EVMWorld

from manticore.core.smtlib import operators, ConstraintSet
from manticore.ethereum import (
    DetectDelegatecall,
    DetectEnvInstruction,
    DetectExternalCallAndLeak,
    DetectIntegerOverflow,
    DetectManipulableBalance,
    Detector,
    DetectRaceCondition,
    DetectSuicidal,
    DetectUnusedRetVal,
    ManticoreEVM,
    State,
)
from manticore.ethereum.plugins import LoopDepthLimiter, KeepOnlyIfStorageChanges

from manticore.utils import config, log

from typing import Tuple, Type

consts = config.get_group("core")
consts.mprocessing = consts.mprocessing.single

THIS_DIR = os.path.dirname(os.path.abspath(__file__))


def make_mock_evm_state():
    cs = ConstraintSet()
    fakestate = State(cs, EVMWorld(cs))
    return fakestate


class EthDetectorTest(unittest.TestCase):
    # Subclasses must assign this class variable to the class for the detector
    DETECTOR_CLASS: Type[Detector]

    def setUp(self):
        self.mevm = ManticoreEVM()
        self.mevm.register_plugin(KeepOnlyIfStorageChanges())
        log.set_verbosity(0)
        self.worksp = self.mevm.workspace

    def tearDown(self):
        self.mevm = None
        shutil.rmtree(self.worksp)

    def _test(self, name: str, should_find, use_ctor_sym_arg=False):
        """
        Tests DetectInvalid over the consensys benchmark suit
        """
        mevm = self.mevm

        dir = os.path.join(THIS_DIR, "contracts", "detectors")
        filepath = os.path.join(dir, f"{name}.sol")

        if use_ctor_sym_arg:
            ctor_arg: Tuple = (mevm.make_symbolic_value(),)
        else:
            ctor_arg = ()

        self.mevm.register_detector(self.DETECTOR_CLASS())

        with self.mevm.kill_timeout(240):
            mevm.multi_tx_analysis(
                filepath,
                contract_name="DetectThis",
                args=ctor_arg,
                compile_args={"solc_working_dir": dir},
            )
        mevm.finalize()
        expected_findings = set(((finding, at_init) for finding, at_init in should_find))
        actual_findings = set(
            ((finding, at_init) for _addr, _pc, finding, at_init in mevm.global_findings)
        )
        self.assertEqual(expected_findings, actual_findings)


class EthRetVal(EthDetectorTest):
    """ Detect when a return value of a low level transaction instruction is ignored """

    DETECTOR_CLASS = DetectUnusedRetVal

    def test_retval_ok(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    def test_retval_not_ok(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {("Returned value at CALL instruction is not used", False)})

    def test_retval_crazy(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    def test_retval_lunatic(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())


class EthSuicidal(EthDetectorTest):
    DETECTOR_CLASS = DetectSuicidal

    def test_selfdestruct_true_pos(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {("Reachable SELFDESTRUCT", False)})

    @unittest.skip("Too slow for these modern times")
    def test_selfdestruct_true_pos1(self):
        self.mevm.register_plugin(LoopDepthLimiter(2))
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {("Reachable SELFDESTRUCT", False)})

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

    @unittest.skip("Too slow for these modern times")
    def test_etherleak_true_pos_argument(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(
            name,
            {
                ("Reachable ether leak to sender via argument", False),
                ("Reachable external call to sender via argument", False),
            },
        )

    @unittest.skip("Too slow for these modern times")
    def test_etherleak_true_pos_argument1(self):
        self.mevm.register_plugin(LoopDepthLimiter(5))
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(
            name,
            {
                ("Reachable ether leak to sender via argument", False),
                ("Reachable external call to sender via argument", False),
            },
        )

    @unittest.skip("Too slow for these modern times")
    def test_etherleak_true_pos_argument2(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(
            name,
            {
                ("Reachable ether leak to user controlled address via argument", False),
                ("Reachable external call to user controlled address via argument", False),
            },
        )

    def test_etherleak_true_pos_msgsender(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(
            name,
            {
                ("Reachable external call to sender", False),
                ("Reachable ether leak to sender", False),
            },
        )

    @unittest.skip("Too slow for these modern times")
    def test_etherleak_true_pos_msgsender1(self):
        self.mevm.register_plugin(LoopDepthLimiter(5))
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(
            name,
            {
                ("Reachable external call to sender", False),
                ("Reachable ether leak to sender", False),
            },
        )


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


class EthEnvInstruction(EthDetectorTest):
    DETECTOR_CLASS = DetectEnvInstruction

    def test_predictable_not_ok(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(
            name,
            {
                ("Warning ORIGIN instruction used", False),
                ("Warning DIFFICULTY instruction used", False),
                ("Warning TIMESTAMP instruction used", False),
                ("Warning NUMBER instruction used", False),
                ("Warning COINBASE instruction used", False),
                ("Warning BLOCKHASH instruction used", False),
                ("Warning NUMBER instruction used", False),
                ("Warning GASPRICE instruction used", False),
                ("Warning GASLIMIT instruction used", False),
            },
        )


class EthDelegatecall(EthDetectorTest):
    """ Test the detection of funny delegatecalls """

    DETECTOR_CLASS = DetectDelegatecall

    def test_delegatecall_ok(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    @unittest.skip("Too slow for these modern times")
    def test_delegatecall_ok1(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    @unittest.skip("Too slow for these modern times")
    def test_delegatecall_ok2(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    @unittest.skip("Too slow for these modern times")
    def test_delegatecall_ok3(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    @unittest.skip("Too slow for these modern times")
    def test_delegatecall_not_ok(self):
        self.mevm.register_plugin(LoopDepthLimiter())
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(
            name,
            {
                ("Delegatecall to user controlled function", False),
                ("Delegatecall to user controlled address", False),
            },
        )

    @unittest.skip("Too slow for these modern times")
    def test_delegatecall_not_ok1(self):
        self.mevm.register_plugin(LoopDepthLimiter(loop_count_threshold=500))
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {("Delegatecall to user controlled function", False)})


class EthRaceCondition(EthDetectorTest):
    DETECTOR_CLASS = DetectRaceCondition

    def test_race_condition(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(
            name,
            {
                (
                    "Potential race condition (transaction order dependency):\n"
                    "Value has been stored in storage slot/index 0 in transaction that called setStoredAddress(address)"
                    " and is now used in transaction that calls callStoredAddress().\n"
                    "An attacker seeing a transaction to callStoredAddress() could create a transaction to "
                    "setStoredAddress(address) with high gas and win a race.",
                    False,
                ),
                (
                    "Potential race condition (transaction order dependency):\n"
                    "Value has been stored in storage slot/index 0 in transaction that called setStoredAddress(address)"
                    " and is now used in transaction that calls stored_address().\nAn attacker seeing a transaction to"
                    " stored_address() could create a transaction to setStoredAddress(address) "
                    "with high gas and win a race.",
                    False,
                ),
                (
                    "Potential race condition (transaction order dependency):\n"
                    "Value has been stored in storage slot/index 0 in transaction that called setStoredAddress(address)"
                    " and is now used in transaction that calls setStoredAddress(address).\n"
                    "An attacker seeing a transaction to setStoredAddress(address) could create a transaction to"
                    " setStoredAddress(address) with high gas and win a race.",
                    False,
                ),
            },
        )

    @unittest.skip("The slot/index are not as deterministic as before")
    def test_race_condition2(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(
            name,
            {
                (
                    "Potential race condition (transaction order dependency):\n"
                    "Value has been stored in storage slot/index which is symbolic in transaction that called"
                    " transfer(address,uint256) and is now used in transaction that calls withdrawBalance().\n"
                    "An attacker seeing a transaction to withdrawBalance() could create a transaction to"
                    " transfer(address,uint256) with high gas and win a race.",
                    False,
                ),
                (
                    "Potential race condition (transaction order dependency):\n"
                    "Value has been stored in storage slot/index"
                    " 13160600963563308326224873642176029774424365052281081785364337067673953740705 in transaction"
                    " that called withdrawBalance() and is now used in transaction that calls transfer(address,uint256).\n"
                    "An attacker seeing a transaction to transfer(address,uint256) could create a transaction to"
                    " withdrawBalance() with high gas and win a race.",
                    False,
                ),
                (
                    "Potential race condition (transaction order dependency):\n"
                    "Value has been stored in storage slot/index"
                    " 13160600963563308326224873642176029774424365052281081785364337067673953740705 in transaction"
                    " that called withdrawBalance() and is now used in transaction that calls withdrawBalance().\n"
                    "An attacker seeing a transaction to withdrawBalance() could create a transaction to withdrawBalance()"
                    " with high gas and win a race.",
                    False,
                ),
                (
                    "Potential race condition (transaction order dependency):\n"
                    "Value has been stored in storage slot/index"
                    " 13160600963563308326224873642176029774424365052281081785364337067673953740705 in transaction"
                    " that called transfer(address,uint256) and is now used in transaction that calls withdrawBalance().\n"
                    "An attacker seeing a transaction to withdrawBalance() could create a transaction to"
                    " transfer(address,uint256) with high gas and win a race.",
                    False,
                ),
                (
                    "Potential race condition (transaction order dependency):\n"
                    "Value has been stored in storage slot/index which is symbolic in transaction that called"
                    " transfer(address,uint256) and is now used in transaction that calls transfer(address,uint256).\n"
                    "An attacker seeing a transaction to transfer(address,uint256) could create a transaction to"
                    " transfer(address,uint256) with high gas and win a race.",
                    False,
                ),
                (
                    "Potential race condition (transaction order dependency):\n"
                    "Value has been stored in storage slot/index"
                    " 13160600963563308326224873642176029774424365052281081785364337067673953740705 in transaction"
                    " that called transfer(address,uint256) and is now used in transaction that calls"
                    " transfer(address,uint256).\nAn attacker seeing a transaction to transfer(address,uint256)"
                    " could create a transaction to transfer(address,uint256) with high gas and win a race.",
                    False,
                ),
            },
        )


class EthBalance(EthDetectorTest):
    """ Test the detection of funny delegatecalls """

    DETECTOR_CLASS = DetectManipulableBalance

    def test_balance_ok(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    def test_balance_not_ok(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, {(("Manipulable balance used in a strict comparison", False))})


if __name__ == "__main__":
    unittest.main()
