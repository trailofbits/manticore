import unittest

import os

from manticore.binary import Elf, CGCElf

DIRPATH = os.path.dirname(__file__)


class TestBinaryPackage(unittest.TestCase):
    _multiprocess_can_split_ = True

    def test_elf(self):
        filename = os.path.join(DIRPATH, "binaries", "basic_linux_amd64")
        f = Elf(filename)
        self.assertTrue(
            [
                (4194304, 823262, "r x", "tests/binaries/basic_linux_amd64", 0, 823262),
                (7118520, 16112, "rw ", "tests/binaries/basic_linux_amd64", 827064, 7320),
            ],
            list(f.maps()),
        )
        self.assertTrue([("Running", {"EIP": 4196624})], list(f.threads()))
        self.assertIsNone(f.getInterpreter())
        f.elf.stream.close()

    def test_decree(self):
        filename = os.path.join(DIRPATH, "binaries", "cadet_decree_x86")
        f = CGCElf(filename)
        self.assertTrue(
            [(134512640, 1478, "r x", "tests/binaries/cadet_decree_x86", 0, 1478)], list(f.maps())
        )
        self.assertTrue([("Running", {"EIP": 134513708})], list(f.threads()))
        f.elf.stream.close()
