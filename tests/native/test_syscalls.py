import random
import unittest

import os

from manticore.core.smtlib import *
from manticore.native import Manticore
from manticore.platforms import linux


class LinuxTest(unittest.TestCase):
    _multiprocess_can_split_ = True
    BIN_PATH = os.path.join(os.path.dirname(__file__), 'binaries', 'basic_linux_amd64')

    def setUp(self):
        self.linux = linux.Linux(self.BIN_PATH)

    def tearDown(self):
        for f in self.linux.files:
            if isinstance(f, linux.File):
                f.close()

    def test_time(self):
        self.linux.current.memory.mmap(0x1000, 0x1000, 'rw ')

        time_0 = self.linux.sys_time(0)
        self.linux.sys_clock_gettime(1, 0x1100)
        self.linux.sys_gettimeofday(0x1200, 0)
        time_2_0 = self.linux.current.read_int(0x1200)
        time_monotonic_0 = self.linux.current.read_int(0x1100)

        time.sleep(1.1)

        time_final = self.linux.sys_time(0)
        self.linux.sys_clock_gettime(1, 0x1100)
        self.linux.sys_gettimeofday(0x1200, 0)
        time_2_final = self.linux.current.read_int(0x1200)
        time_monotonic_final = self.linux.current.read_int(0x1100)

        self.assertGreater(time_monotonic_final, time_monotonic_0, "Monotonic clock time did not increase!")
        self.assertGreater(time_final, time_0, "Time did not increase!")
        self.assertGreater(time_2_final, time_2_0, "Time did not increase!")

    def test_directories(self):
        dir = f"/tmp/mcore_test_{int(random.getrandbits(32))}"

        self.linux.current.memory.mmap(0x1000, 0x1000, 'rw ')
        self.linux.current.write_string(0x1100, dir)

        self.assertFalse(os.path.exists(dir))
        self.linux.sys_mkdir(0x1100, mode=0o777)
        self.assertTrue(os.path.exists(dir))
        self.linux.sys_rmdir(0x1100)
        self.assertFalse(os.path.exists(dir))

    @unittest.skip
    def test_pipe(self):
        self.linux.current.memory.mmap(0x1000, 0x1000, 'rw ')
        self.linux.sys_pipe(0x1100)

        fd1 = self.linux.current.read_int(0x1100, 8 * 4)
        fd2 = self.linux.current.read_int(0x1100 + 4, 8 * 4)

        buf = b'AAAAAAAAAA'
        self.linux.current.write_bytes(0x1200, buf)

        self.linux.sys_write(fd1, 0x1200, len(buf))
        self.linux.sys_read(fd2, 0x1300, len(buf))

        self.assertEqual(buf, self.linux.current.read_bytes(0x1300, len(buf)), "Pipe Read/Write failed")
