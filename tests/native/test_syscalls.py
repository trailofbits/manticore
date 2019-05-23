import random
import unittest

import os
import errno

from manticore.core.smtlib import *
from manticore.platforms import linux, linux_syscall_stubs
from manticore.platforms.platform import SyscallNotImplemented


def get_random_filename():
    return f"/tmp/mcore_test_{int(random.getrandbits(32))}"


class LinuxTest(unittest.TestCase):
    _multiprocess_can_split_ = True
    BIN_PATH = os.path.join(os.path.dirname(__file__), 'binaries', 'basic_linux_amd64')

    def setUp(self):
        self.linux = linux.SLinux(self.BIN_PATH)

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
        tmpdir = get_random_filename()

        self.linux.current.memory.mmap(0x1000, 0x1000, 'rw ')
        self.linux.current.write_string(0x1100, tmpdir)

        self.assertFalse(os.path.exists(tmpdir))
        self.linux.sys_mkdir(0x1100, mode=0o777)
        self.assertTrue(os.path.exists(tmpdir))
        self.linux.sys_rmdir(0x1100)
        self.assertFalse(os.path.exists(tmpdir))

    def test_pipe(self):
        self.linux.current.memory.mmap(0x1000, 0x1000, 'rw ')
        self.linux.sys_pipe(0x1100)

        fd1 = self.linux.current.read_int(0x1100, 8 * 4)
        fd2 = self.linux.current.read_int(0x1100 + 4, 8 * 4)

        buf = b'0123456789ABCDEF'
        self.linux.current.write_bytes(0x1200, buf)

        self.linux.sys_write(fd1, 0x1200, len(buf))
        self.linux.sys_read(fd2, 0x1300, len(buf))

        self.assertEqual(buf, b''.join(self.linux.current.read_bytes(0x1300, len(buf))), "Pipe Read/Write failed")

    def test_ftruncate(self):
        fname = get_random_filename()
        self.linux.current.memory.mmap(0x1000, 0x1000, 'rw ')
        self.linux.current.write_string(0x1100, fname)

        fd = self.linux.sys_open(0x1100, os.O_RDWR, 0o777)

        buf = b'0123456789ABCDEF'
        self.linux.current.write_bytes(0x1200, buf)

        self.linux.sys_write(fd, 0x1200, len(buf))
        self.linux.sys_close(fd)
        fd = self.linux.sys_open(0x1100, os.O_RDWR, 0o777)
        self.linux.sys_ftruncate(fd, len(buf) // 2)
        self.linux.sys_read(fd, 0x1300, len(buf))

        self.assertEqual(buf[:8] + b'\x00'*8, b''.join(self.linux.current.read_bytes(0x1300, len(buf))))

    def test_link(self):
        fname = get_random_filename()
        newname = get_random_filename()
        self.linux.current.memory.mmap(0x1000, 0x1000, 'rw ')
        self.linux.current.write_string(0x1100, fname)
        self.linux.current.write_string(0x1180, newname)

        fd = self.linux.sys_open(0x1100, os.O_RDWR, 0o777)

        buf = b'0123456789ABCDEF'
        self.linux.current.write_bytes(0x1200, buf)

        self.linux.sys_write(fd, 0x1200, len(buf))
        self.linux.sys_close(fd)

        self.linux.sys_link(0x1100, 0x1180)

        self.assertTrue(os.path.exists(newname))

        fd = self.linux.sys_open(0x1180, os.O_RDWR, 0o777)
        self.linux.sys_read(fd, 0x1300, len(buf))
        self.assertEqual(buf, b''.join(self.linux.current.read_bytes(0x1300, len(buf))))
        self.linux.sys_close(fd)

        self.linux.sys_unlink(0x1180)
        self.assertFalse(os.path.exists(newname))

    def test_chmod(self):
        fname = get_random_filename()
        self.linux.current.memory.mmap(0x1000, 0x1000, 'rw ')
        self.linux.current.write_string(0x1100, fname)

        print("Creating", fname)
        fd = self.linux.sys_open(0x1100, os.O_RDWR, 0o777)

        buf = b'0123456789ABCDEF'
        self.linux.current.write_bytes(0x1200, buf)
        self.linux.sys_close(fd)

        self.linux.sys_chmod(0x1100, 0o444)
        self.assertEqual(-errno.EACCES, self.linux.sys_open(0x1100, os.O_WRONLY, 0o777))

        self.assertEqual(-errno.EPERM, self.linux.sys_chown(0x1100, 0, 0))

    def test_unimplemented(self):
        stubs = linux_syscall_stubs.SyscallStubs(default_to_fail=False)

        if hasattr(stubs, 'sys_bpf'):
            self.assertRaises(SyscallNotImplemented, stubs.sys_bpf, 0, 0, 0)

            self.linux.stubs.default_to_fail = False
            self.linux.current.RAX = 321  # SYS_BPF
            self.assertRaises(SyscallNotImplemented, self.linux.syscall)

            self.linux.stubs.default_to_fail = True
            self.linux.current.RAX = 321
            self.linux.syscall()
            self.assertEqual(0xffffffffffffffff, self.linux.current.RAX)
        else:
            import warnings
            warnings.warn("Couldn't find sys_bpf in the stubs file. " +
                          "If you've implemented it, you need to fix test_syscalls:LinuxTest.test_unimplemented")
