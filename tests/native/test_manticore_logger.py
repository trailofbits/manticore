import unittest
import os
import logging
import filecmp

from manticore.native import Manticore
from manticore.utils.log import get_verbosity, set_verbosity


class ManticoreLogger(unittest.TestCase):
    """Make sure we set the logging levels correctly"""

    _multiprocess_can_split_ = False

    def test_logging(self):
        set_verbosity(5)
        self.assertEqual(get_verbosity("manticore.native.cpu.abstractcpu"), logging.DEBUG)
        self.assertEqual(get_verbosity("manticore.ethereum.abi"), logging.DEBUG)

        set_verbosity(1)
        self.assertEqual(get_verbosity("manticore.native.cpu.abstractcpu"), logging.WARNING)
        self.assertEqual(get_verbosity("manticore.ethereum.abi"), logging.INFO)

        set_verbosity(0)  # this is global and does not work in concurrent envs
