"""
File name is purposefully not test_* to run this test separately.
"""

import inspect
import shutil
import struct
import tempfile
import unittest
import os

from manticore.core.plugin import Plugin
from manticore.core.smtlib import ConstraintSet, operators
from manticore.core.smtlib.expression import BitVec
from manticore.core.smtlib import solver
from manticore.core.state import State
from manticore.ethereum import ManticoreEVM, DetectInvalid, DetectIntegerOverflow, Detector, NoAliveStates, ABI, EthereumError, DetectReentrancy, DetectUnusedRetVal
from manticore.platforms.evm import EVMWorld, ConcretizeStack, concretized_args, Return, Stop
from manticore.core.smtlib.visitors import pretty_print, translate_to_smtlib, simplify, to_constant

import shutil

THIS_DIR = os.path.dirname(os.path.abspath(__file__))

# FIXME(mark): Remove these two lines when logging works for ManticoreEVM
from manticore.utils.log import init_logging, set_verbosity
init_logging()
set_verbosity(0)

class EthRetVal(unittest.TestCase):
    """ https://consensys.net/diligence/evm-analyzer-benchmark-suite/ """
    def setUp(self):
        self.mevm = ManticoreEVM()
        self.mevm.verbosity(0)
        self.worksp = self.mevm.workspace

    def tearDown(self):
        self.mevm=None
        shutil.rmtree(self.worksp)

    def _test(self, name, should_find):
        """
        Tests DetectInvalid over the consensys benchmark suit
        """
        mevm = self.mevm

        filename = os.path.join(THIS_DIR, 'binaries', 'detectors', '{}.sol'.format(name))

        self.mevm.register_detector(DetectUnusedRetVal())
        mevm.multi_tx_analysis(filename, contract_name='DetectThis', args=(mevm.make_symbolic_value(),))

        expected_findings = set(((c, d) for b, c, d in should_find))
        actual_findings = set(((c, d) for a, b, c, d in mevm.global_findings))
        self.assertEqual(expected_findings, actual_findings)

    def test_retval_ok(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    def test_retval_not_ok(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set([(337, 'Returned value at CALL instruction is not used', False)]))

    def test_retval_crazy(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

    def test_retval_lunatic(self):
        name = inspect.currentframe().f_code.co_name[5:]
        self._test(name, set())

