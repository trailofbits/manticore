import unittest

import os

from manticore.native import Manticore


class RustTest(unittest.TestCase):
    BIN_PATH = os.path.join(os.path.dirname(__file__), "binaries", "hello_world")

    def setUp(self):
        self.m = Manticore.linux(self.BIN_PATH)

    def test_hello_world(self):
        self.m.run()
