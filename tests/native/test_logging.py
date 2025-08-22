import unittest
import logging

from manticore.utils.log import get_verbosity, set_verbosity, DEFAULT_LOG_LEVEL


import pytest

# Test markers for categorization
pytestmark = pytest.mark.native
pytestmark = pytest.mark.unit

class ManticoreLogger(unittest.TestCase):
    """Make sure we set the logging levels correctly"""

    _multiprocess_can_split_ = True

    def test_logging(self):
        set_verbosity(1)
        self.assertEqual(get_verbosity("manticore.native.cpu.abstractcpu"), logging.WARNING)
        self.assertEqual(get_verbosity("manticore.ethereum.abi"), logging.INFO)

        set_verbosity(0)
        self.assertEqual(get_verbosity("manticore.native.cpu.abstractcpu"), DEFAULT_LOG_LEVEL)
        self.assertEqual(get_verbosity("manticore.ethereum.abi"), DEFAULT_LOG_LEVEL)
