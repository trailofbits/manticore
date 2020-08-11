import logging
import struct
import socket
import tempfile
import time
import unittest

import os
import errno
import re
from glob import glob

from manticore.core.smtlib import Solver
from manticore.core.state import Concretize
from manticore.native import Manticore
from manticore.native.cpu.abstractcpu import ConcretizeRegister

from manticore.platforms import linux, linux_syscall_stubs
from manticore.platforms.linux import SymbolicSocket, logger as linux_logger
from manticore.platforms.platform import SyscallNotImplemented, logger as platform_logger


def test_symbolic_syscall_arg() -> None:
    BIN_PATH = os.path.join(os.path.dirname(__file__), "binaries", "symbolic_read_count")
    tmp_dir = tempfile.TemporaryDirectory(prefix="mcore_test_")
    m = Manticore(BIN_PATH, argv=["+"], workspace_url=str(tmp_dir.name))

    m.run()
    m.finalize()

    found_win_msg = False
    win_msg = "WIN: Read more than zero data"
    outs_glob = f"{str(m.workspace)}/test_*.stdout"
    # Search all output messages
    for output_p in glob(outs_glob):
        with open(output_p) as f:
            if win_msg in f.read():
                found_win_msg = True
                break

    assert found_win_msg, f'Did not find win message in {outs_glob}: "{win_msg}"'


def test_symbolic_length_recv() -> None:
    BIN_PATH = os.path.join(os.path.dirname(__file__), "binaries", "symbolic_length_recv")
    tmp_dir = tempfile.TemporaryDirectory(prefix="mcore_test_")
    m = Manticore(BIN_PATH, workspace_url=str(tmp_dir.name))

    m.run()
    m.finalize()

    found_msg = False
    less_len_msg = "Received less than BUFFER_SIZE"
    outs_glob = f"{str(m.workspace)}/test_*.stdout"
    # Search all output messages
    for output_p in glob(outs_glob):
        with open(output_p) as f:
            if less_len_msg in f.read():
                found_msg = True
                break

    assert found_msg, f'Did not find our message in {outs_glob}: "{less_len_msg}"'


class LinuxTest(unittest.TestCase):
    _multiprocess_can_split_ = True
    BIN_PATH = os.path.join(os.path.dirname(__file__), "binaries", "basic_linux_amd64")

    def setUp(self):
        self.tmp_dir = tempfile.TemporaryDirectory(prefix="mcore_test_")
        self.linux = linux.SLinux(self.BIN_PATH)

    def tearDown(self):
        for entry in self.linux.fd_table.entries():
            entry.fdlike.close()
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

    def test_dir_stat(self):
        dname = self.get_path("test_dir_stat")
        self.assertFalse(os.path.exists(dname))

        self.linux.current.memory.mmap(0x1000, 0x1000, "rw")
        self.linux.current.write_string(0x1100, dname)

        # Create it as a dir
        self.linux.sys_mkdir(0x1100, mode=0o777)
        fd = self.linux.sys_open(0x1100, flags=os.O_RDONLY | os.O_DIRECTORY, mode=0o777)
        self.assertTrue(os.path.exists(dname))
        self.assertGreater(fd, 0)

        res = self.linux.sys_stat32(0x1100, 0x1200)
        self.assertEqual(res, 0)
        res = self.linux.sys_stat64(0x1100, 0x1200)
        self.assertEqual(res, 0)
        res = self.linux.sys_newfstat(fd, 0x1200)
        self.assertEqual(res, 0)
        res = self.linux.sys_fstat(fd, 0x1200)
        self.assertEqual(res, 0)
        res = self.linux.sys_fstat64(fd, 0x1200)
        self.assertEqual(res, 0)

        # Remove from file system on host but not in Manticore
        os.rmdir(dname)
        self.assertFalse(os.path.exists(dname))
        res = self.linux.sys_stat32(0x1100, 0x1200)
        self.assertLess(res, 0)
        res = self.linux.sys_stat64(0x1100, 0x1200)
        self.assertLess(res, 0)
        # The file descriptor is still valid even though the directory is gone
        res = self.linux.sys_newfstat(fd, 0x1200)
        self.assertEqual(res, 0)
        res = self.linux.sys_fstat(fd, 0x1200)
        self.assertEqual(res, 0)
        res = self.linux.sys_fstat64(fd, 0x1200)
        self.assertEqual(res, 0)

        # Remove the directory using Manticore
        self.linux.sys_rmdir(0x1100)
        res = self.linux.sys_stat32(0x1100, 0x1200)
        self.assertLess(res, 0)
        res = self.linux.sys_stat64(0x1100, 0x1200)
        self.assertLess(res, 0)
        # The file descriptor is still valid even though the directory is gone
        res = self.linux.sys_newfstat(fd, 0x1200)
        self.assertEqual(res, 0)
        res = self.linux.sys_fstat(fd, 0x1200)
        self.assertEqual(res, 0)
        res = self.linux.sys_fstat64(fd, 0x1200)
        self.assertEqual(res, 0)

        # Close the file descriptor to totally remove it
        self.linux.sys_close(fd)
        res = self.linux.sys_stat32(0x1100, 0x1200)
        self.assertLess(res, 0)
        res = self.linux.sys_stat64(0x1100, 0x1200)
        self.assertLess(res, 0)
        res = self.linux.sys_newfstat(fd, 0x1200)
        self.assertLess(res, 0)
        res = self.linux.sys_fstat(fd, 0x1200)
        self.assertLess(res, 0)
        res = self.linux.sys_fstat64(fd, 0x1200)
        self.assertLess(res, 0)

    def test_file_stat(self):
        fname = self.get_path("test_file_stat")
        self.assertFalse(os.path.exists(fname))

        self.linux.current.memory.mmap(0x1000, 0x1000, "rw")
        self.linux.current.write_string(0x1100, fname)

        # Create a file
        fd = self.linux.sys_open(0x1100, os.O_RDWR, 0o777)
        self.assertTrue(os.path.exists(fname))

        res = self.linux.sys_stat32(0x1100, 0x1200)
        self.assertEqual(res, 0)
        res = self.linux.sys_stat64(0x1100, 0x1200)
        self.assertEqual(res, 0)
        res = self.linux.sys_newfstat(fd, 0x1200)
        self.assertEqual(res, 0)
        res = self.linux.sys_fstat(fd, 0x1200)
        self.assertEqual(res, 0)
        res = self.linux.sys_fstat64(fd, 0x1200)
        self.assertEqual(res, 0)

        # Remove from file system on host but not in Manticore
        os.remove(fname)
        self.assertFalse(os.path.exists(fname))
        res = self.linux.sys_stat32(0x1100, 0x1200)
        self.assertLess(res, 0)
        res = self.linux.sys_stat64(0x1100, 0x1200)
        self.assertLess(res, 0)
        res = self.linux.sys_newfstat(fd, 0x1200)
        self.assertEqual(res, 0)
        res = self.linux.sys_fstat(fd, 0x1200)
        self.assertEqual(res, 0)
        res = self.linux.sys_fstat64(fd, 0x1200)
        self.assertEqual(res, 0)

        # Remove the file using Manticore
        self.linux.sys_unlink(0x1100)
        res = self.linux.sys_stat32(0x1100, 0x1200)
        self.assertLess(res, 0)
        res = self.linux.sys_stat64(0x1100, 0x1200)
        self.assertLess(res, 0)
        res = self.linux.sys_newfstat(fd, 0x1200)
        self.assertEqual(res, 0)
        res = self.linux.sys_fstat(fd, 0x1200)
        self.assertEqual(res, 0)
        res = self.linux.sys_fstat64(fd, 0x1200)
        self.assertEqual(res, 0)

        # Close the file descriptor to totally remove it
        self.linux.sys_close(fd)
        res = self.linux.sys_stat32(0x1100, 0x1200)
        self.assertLess(res, 0)
        res = self.linux.sys_stat64(0x1100, 0x1200)
        self.assertLess(res, 0)
        res = self.linux.sys_newfstat(fd, 0x1200)
        self.assertLess(res, 0)
        res = self.linux.sys_fstat(fd, 0x1200)
        self.assertLess(res, 0)
        res = self.linux.sys_fstat64(fd, 0x1200)
        self.assertLess(res, 0)

    def test_socketdesc_stat(self):
        self.linux.current.memory.mmap(0x1000, 0x1000, "rw")

        # Create a socket
        fd = self.linux.sys_socket(socket.AF_INET, socket.SOCK_STREAM, 0)
        res = self.linux.sys_newfstat(fd, 0x1200)
        self.assertEqual(res, 0)
        res = self.linux.sys_fstat(fd, 0x1200)
        self.assertEqual(res, 0)
        res = self.linux.sys_fstat64(fd, 0x1200)
        self.assertEqual(res, 0)

        # Close the socket
        self.linux.sys_close(fd)
        res = self.linux.sys_newfstat(fd, 0x1200)
        self.assertLess(res, 0)
        res = self.linux.sys_fstat(fd, 0x1200)
        self.assertLess(res, 0)
        res = self.linux.sys_fstat64(fd, 0x1200)
        self.assertLess(res, 0)

    def test_socket_stat(self):
        self.linux.current.memory.mmap(0x1000, 0x1000, "rw")

        # Create a socket
        sock_fd = self.linux.sys_socket(socket.AF_INET, socket.SOCK_STREAM, 0)
        self.linux.sys_bind(sock_fd, None, None)
        self.linux.sys_listen(sock_fd, None)
        conn_fd = self.linux.sys_accept(sock_fd, None, 0)

        res = self.linux.sys_newfstat(conn_fd, 0x1200)
        self.assertEqual(res, 0)
        res = self.linux.sys_fstat(conn_fd, 0x1200)
        self.assertEqual(res, 0)
        res = self.linux.sys_fstat64(conn_fd, 0x1200)
        self.assertEqual(res, 0)

        # Close the socket
        self.linux.sys_close(conn_fd)
        res = self.linux.sys_newfstat(conn_fd, 0x1200)
        self.assertLess(res, 0)
        res = self.linux.sys_fstat(conn_fd, 0x1200)
        self.assertLess(res, 0)
        res = self.linux.sys_fstat64(conn_fd, 0x1200)
        self.assertLess(res, 0)

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

        sock_obj = self.linux.fd_table.get_fdlike(conn_fd)
        # Any socket that comes from an accept should probably be symbolic for now
        assert isinstance(sock_obj, SymbolicSocket)

        # Start with 0 symbolic bytes
        init_len = len(sock_obj.buffer)
        self.assertEqual(init_len, 0)

        # Try to receive 5 symbolic bytes
        BYTES = 5
        # Need to set this so we don't fork in our tests
        sock_obj._symb_len = BYTES
        wrote = self.linux.sys_read(conn_fd, 0x1100, BYTES)
        self.assertEqual(wrote, BYTES)

        # Try to receive into address 0x0
        BYTES = 100
        sock_obj._symb_len = BYTES
        wrote = self.linux.sys_read(conn_fd, 0x0, BYTES)
        self.assertEqual(wrote, -errno.EFAULT)

        # Try to receive all remaining symbolic bytes plus some more
        remaining_bytes = sock_obj.max_recv_symbolic - sock_obj.recv_pos
        BYTES = remaining_bytes + 10
        # Needs to be remaining_bytes so that we can simulate overread
        sock_obj._symb_len = remaining_bytes
        wrote = self.linux.sys_read(conn_fd, 0x1100, BYTES)
        self.assertNotEqual(wrote, BYTES)
        self.assertEqual(wrote, remaining_bytes)

        # Try to receive 10 more bytes when already at max
        BYTES = 10
        # Needs to be 0 so that we can simulate overread
        sock_obj._symb_len = 0
        wrote = self.linux.sys_read(conn_fd, 0x1100, BYTES)
        self.assertEqual(wrote, 0)

        # Close and make sure we can't write more stuff
        BYTES = 10
        sock_obj._symb_len = BYTES
        self.linux.sys_close(conn_fd)
        wrote = self.linux.sys_read(conn_fd, 0x1100, BYTES)
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

        sock_obj = self.linux.fd_table.get_fdlike(conn_fd)
        # Any socket that comes from an accept should probably be symbolic for now
        assert isinstance(sock_obj, SymbolicSocket)

        # Start with 0 symbolic bytes
        init_len = len(sock_obj.buffer)
        self.assertEqual(init_len, 0)

        # Try to receive 5 symbolic bytes
        BYTES = 5
        # Need to set this so we don't fork in our tests
        sock_obj._symb_len = BYTES
        wrote = self.linux.sys_recvfrom(conn_fd, 0x1100, BYTES, 0x0, 0x0, 0x0)
        self.assertEqual(wrote, BYTES)

        # Try to receive into address 0x0
        wrote = self.linux.sys_recvfrom(conn_fd, 0x0, 100, 0x0, 0x0, 0x0)
        self.assertEqual(wrote, -errno.EFAULT)

        # Try to receive all remaining symbolic bytes plus some more
        remaining_bytes = sock_obj.max_recv_symbolic - sock_obj.recv_pos
        BYTES = remaining_bytes + 10
        # Needs to be remaining_bytes so that we can simulate overread
        sock_obj._symb_len = remaining_bytes
        wrote = self.linux.sys_recvfrom(conn_fd, 0x1100, BYTES, 0x0, 0x0, 0x0)
        self.assertNotEqual(wrote, BYTES)
        self.assertEqual(wrote, remaining_bytes)

        # Try to receive 10 more bytes when already at max
        BYTES = 10
        # Needs to be 0 so that we can simulate overread
        sock_obj._symb_len = 0
        wrote = self.linux.sys_recvfrom(conn_fd, 0x1100, BYTES, 0x0, 0x0, 0x0)
        self.assertEqual(wrote, 0)

        # Close and make sure we can't write more stuff
        self.linux.sys_close(conn_fd)
        BYTES = 10
        sock_obj._symb_len = 0
        wrote = self.linux.sys_recvfrom(conn_fd, 0x1100, BYTES, 0x0, 0x0, 0x0)
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
        resultp = 0x1900
        res = self.linux.sys_llseek(fd, 0, -2 * len(buf), resultp, os.SEEK_END)
        self.assertTrue(res < 0)

    def test_unimplemented_symbolic_syscall(self) -> None:
        # Load a symbolic argument (address)
        cpu = self.linux.current

        # Store the address argument value in RDI
        cpu.RDI = self.linux.constraints.new_bitvec(cpu.address_bit_size, "addr")
        cpu.RAX = 12  # sys_brk

        # Set logging level to debug so we can match against the message printed
        # when executing our catch-all model for # functions with symbolic
        # arguments
        prev_log_level = linux_logger.getEffectiveLevel()
        linux_logger.setLevel(logging.DEBUG)

        with self.assertLogs(linux_logger, logging.DEBUG) as cm:
            with self.assertRaises(ConcretizeRegister):
                # Call the system call number in RAX
                self.linux.syscall()
        dmsg = "Unimplemented symbolic argument to sys_brk. Concretizing argument 0"
        self.assertIn(dmsg, "\n".join(cm.output))

        linux_logger.setLevel(prev_log_level)

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
