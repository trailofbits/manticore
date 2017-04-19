
import unittest
import sys
import shutil
import tempfile
import os
import hashlib
import subprocess
import collections
import time

from manticore import Manticore, issymbolic
from manticore.core.smtlib import BitVecVariable

class ManticoreDriver(unittest.TestCase):
    def setUp(self):
        # Create a temporary directory
        self.test_dir = tempfile.mkdtemp()

    def tearDown(self):
        # Remove the directory after the test
        shutil.rmtree(self.test_dir)


    def testCreating(self):
        m = Manticore('/bin/ls')
        m.log_file = '/dev/null'
        
    def test_issymbolic(self):
        v = BitVecVariable(32, 'sym')
        self.assertTrue(issymbolic(v))

    def test_issymbolic_neg(self):
        v = 1
        self.assertFalse(issymbolic(v))

