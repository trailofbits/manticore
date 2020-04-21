import random
import struct
import socket
import tempfile
import unittest

import os
import errno
import re

from manticore.core.smtlib import *
from manticore.platforms import linux, linux_syscall_stubs
from manticore.platforms.linux import SymbolicSocket
from manticore.platforms.platform import SyscallNotImplemented, logger as platform_logger


class LinuxTest(unittest.TestCase):
    _multiprocess_can_split_ = True
    BIN_PATH = os.path.join(os.path.dirname(__file__), "binaries", "basic_linux_amd64")

    def setUp(self):
        self.tmp_dir = tempfile.TemporaryDirectory(prefix="mcore_test_")
        self.linux = linux.SLinux(self.BIN_PATH)

    def tearDown(self):
        for f in self.linux.files:
            if isinstance(f, linux.File):
                f.close()
        self.tmp_dir.cleanup()

    def get_path(self, basename: str) -> str:
        "Returns an absolute path with the given basename"
        return f"{self.tmp_dir.name}/{basename}"

    def test_time(self):
        self.linux.current.memory.mmap(0x1000, 0x1000, "rw")

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

        self.assertGreater(
            time_monotonic_final, time_monotonic_0, "Monotonic clock time did not increase!"
        )
        self.assertGreater(time_final, time_0, "Time did not increase!")
        self.assertGreater(time_2_final, time_2_0, "Time did not increase!")

    def test_directories(self):
        dname = self.get_path("test_directories")

        self.linux.current.memory.mmap(0x1000, 0x1000, "rw")
        self.linux.current.write_string(0x1100, dname)

        self.assertFalse(os.path.exists(dname))
        self.linux.sys_mkdir(0x1100, mode=0o777)
        self.assertTrue(os.path.exists(dname))
        self.linux.sys_rmdir(0x1100)
        self.assertFalse(os.path.exists(dname))

    def test_pipe(self):
        self.linux.current.memory.mmap(0x1000, 0x1000, "rw")
        self.linux.sys_pipe(0x1100)

        fd1 = self.linux.current.read_int(0x1100, 8 * 4)
        fd2 = self.linux.current.read_int(0x1100 + 4, 8 * 4)

        buf = b"0123456789ABCDEF"
        self.linux.current.write_bytes(0x1200, buf)

        self.linux.sys_write(fd1, 0x1200, len(buf))
        self.linux.sys_read(fd2, 0x1300, len(buf))

        self.assertEqual(
            buf, b"".join(self.linux.current.read_bytes(0x1300, len(buf))), "Pipe Read/Write failed"
        )

    def test_ftruncate(self):
        fname = self.get_path("test_ftruncate")
        self.linux.current.memory.mmap(0x1000, 0x1000, "rw")
        self.linux.current.write_string(0x1100, fname)

        fd = self.linux.sys_open(0x1100, os.O_RDWR, 0o777)

        buf = b"0123456789ABCDEF"
        self.linux.current.write_bytes(0x1200, buf)

        self.linux.sys_write(fd, 0x1200, len(buf))
        self.linux.sys_close(fd)
        fd = self.linux.sys_open(0x1100, os.O_RDWR, 0o777)
        self.linux.sys_ftruncate(fd, len(buf) // 2)
        self.linux.sys_read(fd, 0x1300, len(buf))

        self.assertEqual(
            buf[:8] + b"\x00" * 8, b"".join(self.linux.current.read_bytes(0x1300, len(buf)))
        )

    def test_link(self):
        fname = self.get_path("test_link_from")
        newname = self.get_path("test_link_to")
        self.linux.current.memory.mmap(0x1000, 0x1000, "rw")
        self.linux.current.write_string(0x1100, fname)
        self.linux.current.write_string(0x1180, newname)

        fd = self.linux.sys_open(0x1100, os.O_RDWR, 0o777)

        buf = b"0123456789ABCDEF"
        self.linux.current.write_bytes(0x1200, buf)

        self.linux.sys_write(fd, 0x1200, len(buf))
        self.linux.sys_close(fd)

        self.linux.sys_link(0x1100, 0x1180)

        self.assertTrue(os.path.exists(newname))

        fd = self.linux.sys_open(0x1180, os.O_RDWR, 0o777)
        self.linux.sys_read(fd, 0x1300, len(buf))
        self.assertEqual(buf, b"".join(self.linux.current.read_bytes(0x1300, len(buf))))
        self.linux.sys_close(fd)

        self.linux.sys_unlink(0x1180)
        self.assertFalse(os.path.exists(newname))

    def test_chmod(self):
        fname = self.get_path("test_chmod")
        self.linux.current.memory.mmap(0x1000, 0x1000, "rw")
        self.linux.current.write_string(0x1100, fname)

        print("Creating", fname)
        fd = self.linux.sys_open(0x1100, os.O_RDWR, 0o777)

        buf = b"0123456789ABCDEF"
        self.linux.current.write_bytes(0x1200, buf)
        self.linux.sys_close(fd)

        self.linux.sys_chmod(0x1100, 0o444)
        self.assertEqual(-errno.EACCES, self.linux.sys_open(0x1100, os.O_WRONLY, 0o777))

        self.assertEqual(-errno.EPERM, self.linux.sys_chown(0x1100, 0, 0))

    def test_read_symb_socket(self):
        self.linux.current.memory.mmap(0x1000, 0x1000, "rw")

        sock_fd = self.linux.sys_socket(socket.AF_INET, socket.SOCK_STREAM, 0)
        self.assertEqual(sock_fd, 3)
        # Unimplemented
        # self.linux.current.write_int(0x1000, 1, size=8 * 4)
        # self.linux.sys_setsockopt(sock_fd, socket.SOL_SOCKET, socket.SO_REUSEPORT, 0x1000, 4)
        self.linux.sys_bind(sock_fd, None, None)
        self.linux.sys_listen(sock_fd, None)
        conn_fd = self.linux.sys_accept(sock_fd, None, 0)
        self.assertEqual(conn_fd, 4)

        sock_obj = self.linux.files[conn_fd]
        # Any socket that comes from an accept should probably be symbolic for now
        assert isinstance(sock_obj, SymbolicSocket)

        # Start with 0 symbolic bytes
        init_len = len(sock_obj.buffer)
        self.assertEqual(init_len, 0)

        # Try to receive 5 symbolic bytes
        BYTES = 5
        wrote = self.linux.sys_read(conn_fd, 0x1100, BYTES)
        self.assertEqual(wrote, BYTES)

        # Try to receive into address 0x0
        wrote = self.linux.sys_read(conn_fd, 0x0, 100)
        self.assertEqual(wrote, -errno.EFAULT)

        # Try to receive all remaining symbolic bytes plus some more
        recvd_bytes = sock_obj.recv_pos
        remaining_bytes = sock_obj.max_recv_symbolic - sock_obj.recv_pos
        BYTES = remaining_bytes + 10
        wrote = self.linux.sys_read(conn_fd, 0x1100, BYTES)
        self.assertNotEqual(wrote, BYTES)
        self.assertEqual(wrote, remaining_bytes)

        # Try to receive 10 more bytes when already at max
        wrote = self.linux.sys_read(conn_fd, 0x1100, 10)
        self.assertEqual(wrote, 0)

        # Close and make sure we can't write more stuff
        self.linux.sys_close(conn_fd)
        wrote = self.linux.sys_read(conn_fd, 0x1100, 10)
        self.assertEqual(wrote, -errno.EBADF)

    def test_recvfrom_symb_socket(self):
        self.linux.current.memory.mmap(0x1000, 0x1000, "rw")

        sock_fd = self.linux.sys_socket(socket.AF_INET, socket.SOCK_STREAM, 0)
        self.assertEqual(sock_fd, 3)
        # Unimplemented
        # self.linux.current.write_int(0x1000, 1, size=8 * 4)
        # self.linux.sys_setsockopt(sock_fd, socket.SOL_SOCKET, socket.SO_REUSEPORT, 0x1000, 4)
        self.linux.sys_bind(sock_fd, None, None)
        self.linux.sys_listen(sock_fd, None)
        conn_fd = self.linux.sys_accept(sock_fd, None, 0)
        self.assertEqual(conn_fd, 4)

        sock_obj = self.linux.files[conn_fd]
        # Any socket that comes from an accept should probably be symbolic for now
        assert isinstance(sock_obj, SymbolicSocket)

        # Start with 0 symbolic bytes
        init_len = len(sock_obj.buffer)
        self.assertEqual(init_len, 0)

        # Try to receive 5 symbolic bytes
        BYTES = 5
        wrote = self.linux.sys_recvfrom(conn_fd, 0x1100, BYTES, 0x0, 0x0, 0x0)
        self.assertEqual(wrote, BYTES)

        # Try to receive into address 0x0
        wrote = self.linux.sys_recvfrom(conn_fd, 0x0, 100, 0x0, 0x0, 0x0)
        self.assertEqual(wrote, -errno.EFAULT)

        # Try to receive all remaining symbolic bytes plus some more
        recvd_bytes = sock_obj.recv_pos
        remaining_bytes = sock_obj.max_recv_symbolic - sock_obj.recv_pos
        BYTES = remaining_bytes + 10
        wrote = self.linux.sys_recvfrom(conn_fd, 0x1100, BYTES, 0x0, 0x0, 0x0)
        self.assertNotEqual(wrote, BYTES)
        self.assertEqual(wrote, remaining_bytes)

        # Try to receive 10 more bytes when already at max
        wrote = self.linux.sys_recvfrom(conn_fd, 0x1100, 10, 0x0, 0x0, 0x0)
        self.assertEqual(wrote, 0)

        # Close and make sure we can't write more stuff
        self.linux.sys_close(conn_fd)
        wrote = self.linux.sys_recvfrom(conn_fd, 0x1100, 10, 0x0, 0x0, 0x0)
        self.assertEqual(wrote, -errno.EBADF)

    def test_multiple_sockets(self):
        sock_fd = self.linux.sys_socket(socket.AF_INET, socket.SOCK_STREAM, 0)
        self.assertEqual(sock_fd, 3)
        self.linux.sys_bind(sock_fd, None, None)
        self.linux.sys_listen(sock_fd, None)
        conn_fd = self.linux.sys_accept(sock_fd, None, 0)
        self.assertEqual(conn_fd, 4)
        self.linux.sys_close(conn_fd)

        conn_fd = -1
        conn_fd = self.linux.sys_accept(sock_fd, None, 0)
        self.assertEqual(conn_fd, 4)

    def test_lseek(self):
        fname = self.get_path("test_lseek")
        assert len(fname) < 0x100
        self.linux.current.memory.mmap(0x1000, 0x1000, "rw")
        self.linux.current.write_string(0x1100, fname)

        fd = self.linux.sys_open(0x1100, os.O_RDWR, 0o777)
        buf = b"1" * 1000
        self.assertEqual(len(buf), 1000)
        self.linux.current.write_bytes(0x1200, buf)
        self.linux.sys_write(fd, 0x1200, len(buf))

        pos = self.linux.sys_lseek(fd, 100, os.SEEK_SET)
        self.assertEqual(100, pos)

        pos = self.linux.sys_lseek(fd, -50, os.SEEK_CUR)
        self.assertEqual(50, pos)

        pos = self.linux.sys_lseek(fd, 50, os.SEEK_CUR)
        self.assertEqual(100, pos)

        pos = self.linux.sys_lseek(fd, 0, os.SEEK_END)
        self.assertEqual(len(buf), pos)

        pos = self.linux.sys_lseek(fd, -50, os.SEEK_END)
        self.assertEqual(len(buf) - 50, pos)

        pos = self.linux.sys_lseek(fd, 50, os.SEEK_END)
        self.assertEqual(len(buf) + 50, pos)

        self.linux.sys_close(fd)
        pos = self.linux.sys_lseek(fd, 0, os.SEEK_SET)
        self.assertEqual(-errno.EBADF, pos)

    @unittest.expectedFailure
    def test_lseek_end_broken(self):
        fname = self.get_path("test_lseek")
        assert len(fname) < 0x100
        self.linux.current.memory.mmap(0x1000, 0x1000, "rw")
        self.linux.current.write_string(0x1100, fname)

        fd = self.linux.sys_open(0x1100, os.O_RDWR, 0o777)
        buf = b"1" * 1000
        self.assertEqual(len(buf), 1000)
        self.linux.current.write_bytes(0x1200, buf)
        self.linux.sys_write(fd, 0x1200, len(buf))

        # FIXME: currently broken -- raises a Python OSError invalid argument exception!
        pos = self.linux.sys_lseek(fd, -2 * len(buf), os.SEEK_END)
        self.assertEqual(-errno.EBADF, pos)

    def test_llseek(self):
        fname = self.get_path("test_llseek")
        assert len(fname) < 0x100
        # map some memory we can play with
        self.linux.current.memory.mmap(0x1000, 0x1000, "rw")
        # open a file descriptor for `fname`
        self.linux.current.write_string(0x1100, fname)
        fd = self.linux.sys_open(0x1100, os.O_RDWR, 0o777)
        # write some bogus data to the file
        buf = b"1" * 1000
        self.assertEqual(len(buf), 1000)
        self.linux.current.write_bytes(0x1200, buf)
        self.linux.sys_write(fd, 0x1200, len(buf))

        # set up a location & some helpers for the result pointer for `sys_llseek`
        result_struct = struct.Struct("q")
        resultp = 0x1900
        result_size = result_struct.size

        def read_resultp():
            "reads the `loff_t` value -- a long long -- from the result pointer"
            data = self.linux.current.read_bytes(resultp, result_struct.size)
            return result_struct.unpack(b"".join(data))[0]

        # now actually test some things about sys_llseek
        res = self.linux.sys_llseek(fd, 0, 100, resultp, os.SEEK_SET)
        self.assertEqual(res, 0)
        self.assertEqual(read_resultp(), 100)

        res = self.linux.sys_llseek(fd, 1, 0, resultp, os.SEEK_CUR)
        self.assertEqual(res, 0)
        self.assertEqual(read_resultp(), 4294967396)

        res = self.linux.sys_llseek(fd, 0, -1000, resultp, os.SEEK_CUR)
        self.assertEqual(res, 0)
        self.assertEqual(read_resultp(), 4294966396)

        res = self.linux.sys_llseek(fd, 0, 0, resultp, os.SEEK_END)
        self.assertEqual(res, 0)
        self.assertEqual(read_resultp(), len(buf))

        res = self.linux.sys_llseek(fd, 0, 50, resultp, os.SEEK_END)
        self.assertEqual(res, 0)
        self.assertEqual(read_resultp(), len(buf) + 50)

        res = self.linux.sys_llseek(fd, 0, -50, resultp, os.SEEK_END)
        self.assertEqual(res, 0)
        self.assertEqual(read_resultp(), len(buf) - 50)

        self.linux.sys_close(fd)
        res = self.linux.sys_llseek(fd, 0, 0, resultp, os.SEEK_SET)
        self.assertEqual(-errno.EBADF, res)

    @unittest.expectedFailure
    def test_llseek_end_broken(self):
        fname = self.get_path("test_llseek_end_broken")
        assert len(fname) < 0x100
        # map some memory we can play with
        self.linux.current.memory.mmap(0x1000, 0x1000, "rw")
        # open a file descriptor for `fname`
        self.linux.current.write_string(0x1100, fname)
        fd = self.linux.sys_open(0x1100, os.O_RDWR, 0o777)
        # write some bogus data to the file
        buf = b"1" * 1000
        self.assertEqual(len(buf), 1000)
        self.linux.current.write_bytes(0x1200, buf)
        self.linux.sys_write(fd, 0x1200, len(buf))

        # FIXME: currently broken -- raises a Python OSError invalid argument exception!
        res = self.linux.sys_llseek(fd, 0, -2 * len(buf), resultp, os.SEEK_END)
        self.assertTrue(res < 0)

    def test_unimplemented_stubs(self) -> None:
        stubs = linux_syscall_stubs.SyscallStubs(default_to_fail=False)

        with self.assertLogs(platform_logger, logging.WARNING) as cm:
            self.assertRaises(SyscallNotImplemented, stubs.sys_bpf, 0, 0, 0)
        # make sure that log message contains expected info
        pat = re.compile(r"Unimplemented system call: .+: .+\(.+\)", re.MULTILINE)
        self.assertRegex("\n".join(cm.output), pat)

        self.linux.stubs.default_to_fail = False
        self.linux.current.RAX = 321  # SYS_BPF
        self.assertRaises(SyscallNotImplemented, self.linux.syscall)

        self.linux.stubs.default_to_fail = True
        self.linux.current.RAX = 321
        self.linux.syscall()
        self.assertEqual(0xFFFFFFFFFFFFFFFF, self.linux.current.RAX)

    def test_unimplemented_linux(self) -> None:
        with self.assertLogs(platform_logger, logging.WARNING) as cm:
            self.linux.sys_futex(0, 0, 0, 0, 0, 0)
        # make sure that log message contains expected info
        pat = re.compile(r"Unimplemented system call: .+: .+\(.+\)", re.MULTILINE)
        self.assertRegex("\n".join(cm.output), pat)
