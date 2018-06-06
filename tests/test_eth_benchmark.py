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
from manticore.ethereum import ManticoreEVM, DetectInvalid, DetectIntegerOverflow, Detector, NoAliveStates, ABI, EthereumError
from manticore.platforms.evm import EVMWorld, ConcretizeStack, concretized_args, Return, Stop
from manticore.core.smtlib.visitors import pretty_print, translate_to_smtlib, simplify, to_constant

import shutil

THIS_DIR = os.path.dirname(os.path.abspath(__file__))

# FIXME(mark): Remove these two lines when logging works for ManticoreEVM
from manticore.utils.log import init_logging, set_verbosity
init_logging()
set_verbosity(0)

class EthBenchmark(unittest.TestCase):
    """ https://consensys.net/diligence/evm-analyzer-benchmark-suite/ """
    def setUp(self):
        self.mevm = ManticoreEVM()
        self.mevm.verbosity(0)
        self.worksp = self.mevm.workspace

    def tearDown(self):
        self.mevm=None
        shutil.rmtree(self.worksp)

    def _test_assert(self, name, should_find):
        """
        Tests DetectInvalid over the consensys benchmark suit
        """
        mevm = self.mevm

        d = DetectInvalid()
        mevm.register_detector(d)

        filename = os.path.join(THIS_DIR, 'binaries', 'benchmark', '{}.sol'.format(name))

        mevm.multi_tx_analysis(filename, tx_limit=3)

        actual_findings = set(( (b, c, d) for a, b, c, d in d.global_findings))
        self.assertEqual(should_find, actual_findings)

    def test_assert_minimal(self):
        self._test_assert('assert_minimal', set([(95, 'INVALID intruction', False)]))

    def test_assert_constructor(self):
        self._test_assert('assert_constructor', set([(23, 'INVALID intruction', True)]))

    def test_assert_multitx_1(self):
        self._test_assert('assert_multitx_1', set())

    def test_assert_multitx_2(self):
        self._test_assert('assert_multitx_2', set([(150, 'INVALID intruction', False)]))



