import unittest

import os
import shutil
import tempfile

from manticore import issymbolic
from manticore.core.smtlib import BitVecVariable
from manticore.native import Manticore


class ManticoreDriverTest(unittest.TestCase):
    _multiprocess_can_split_ = True

    def setUp(self):
        # Create a temporary directory
        self.test_dir = tempfile.mkdtemp()

    def tearDown(self):
        # Remove the directory after the test
        shutil.rmtree(self.test_dir)

    def testCreating(self):
        dirname = os.path.dirname(__file__)
        m = Manticore(os.path.join(dirname, "binaries", "basic_linux_amd64"))
        m.log_file = "/dev/null"

    def test_issymbolic(self):
        v = BitVecVariable(32, "sym")
        self.assertTrue(issymbolic(v))

    def test_issymbolic_neg(self):
        v = 1
        self.assertFalse(issymbolic(v))
