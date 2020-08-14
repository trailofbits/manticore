import binascii
import ctypes
import errno
import fcntl
import logging
import socket
import struct
import time
import resource
import tempfile

from abc import ABC, abstractmethod
from functools import partial

from dataclasses import dataclass
from itertools import chain

import io
import os
import random

from elftools.elf.descriptions import describe_symbol_type

# Remove in favor of binary.py
from elftools.elf.elffile import ELFFile
from elftools.elf.sections import SymbolTableSection

from . import linux_syscalls
from .linux_syscall_stubs import SyscallStubs
from ..core.state import TerminateState, Concretize
from ..core.smtlib import ConstraintSet, Operators, Expression, issymbolic, ArrayProxy
from ..core.smtlib.solver import SelectedSolver
from ..exceptions import SolverError
from ..native.cpu.abstractcpu import Cpu, Syscall, ConcretizeArgument, Interruption
from ..native.cpu.cpufactory import CpuFactory
from ..native.memory import SMemory32, SMemory64, Memory32, Memory64, LazySMemory32, LazySMemory64
from ..native.state import State
from ..platforms.platform import Platform, SyscallNotImplemented, unimplemented

from typing import cast, Any, Deque, Dict, IO, Iterable, List, Optional, Set, Tuple, Union, Callable

logger = logging.getLogger(__name__)


MixedSymbolicBuffer = Union[List[Union[bytes, Expression]], bytes]


def errorcode(code: int) -> str:
    return f"errno.{errno.errorcode[code]}"


class RestartSyscall(Exception):
    pass


class Deadlock(Exception):
    pass


class EnvironmentError(RuntimeError):
    pass


class FdError(Exception):
    def __init__(self, message="", err=errno.EBADF):
        self.err = err
        super().__init__(message)


def perms_from_elf(elf_flags: int) -> str:
    return ["   ", "  x", " w ", " wx", "r  ", "r x", "rw ", "rwx"][elf_flags & 7]


def perms_from_protflags(prot_flags: int) -> str:
    return ["   ", "r  ", " w ", "rw ", "  x", "r x", " wx", "rwx"][prot_flags & 7]


def mode_from_flags(file_flags: int) -> str:
    return {os.O_RDWR: "rb+", os.O_RDONLY: "rb", os.O_WRONLY: "wb"}[file_flags & 7]


def concreteclass(cls):
    """
    This decorator indicates that the given class is intended to have no
    unimplemented abstract methods.  If this is not the case, a TypeError
    exception is raised.

    It only really makes sense to use this in conjunction with classes that
    have ABCMeta as a metaclass, but it should work without issue with other
    classes too.

    Without using this decorator, instead of getting a TypeError just after
    class creation time, you will get an error only if you try to instantiate
    the class.  In short, using this decorator pushes error detection earlier.

    It would be nice if this existed in the Python standard library `abc`
    module, but it doesn't seem to be present.
    """
    methods = getattr(cls, "__abstractmethods__", None)
    if methods:
        methods_str = ", ".join(repr(n) for n in sorted(methods))
        raise TypeError(
            f"Class {cls.__name__} marked as concrete, but has "
            f"unimplemented abstract methods: {methods_str}"
        )
    return cls


@dataclass
class StatResult:
    """
    Data structure corresponding to result received from stat, fstat, lstat for
    information about a file.

    See https://man7.org/linux/man-pages/man2/stat.2.html for more info
    """

    st_mode: int
    st_ino: int
    st_dev: int
    st_nlink: int
    st_uid: int
    st_gid: int
    st_size: int
    st_atime: float
    st_mtime: float
    st_ctime: float
    st_blksize: int
    st_blocks: int
    st_rdev: int


def convert_os_stat(stat: os.stat_result) -> StatResult:
    return StatResult(
        st_mode=stat.st_mode,
        st_ino=stat.st_ino,
        st_dev=stat.st_dev,
        st_nlink=stat.st_nlink,
        st_uid=stat.st_uid,
        st_gid=stat.st_gid,
        st_size=stat.st_size,
        st_atime=stat.st_atime,
        st_mtime=stat.st_mtime,
        st_ctime=stat.st_ctime,
        st_blksize=stat.st_blksize,
        st_blocks=stat.st_blocks,
        st_rdev=stat.st_rdev,
    )


class FdLike(ABC):
    """
    An abstract class for different kinds of file descriptors.
    """

    @abstractmethod
    def read(self, size: int):
        ...

    @abstractmethod
    def write(self, buf) -> int:
        ...

    @abstractmethod
    def sync(self) -> None:
        ...

    @abstractmethod
    def close(self) -> None:
        ...

    @abstractmethod
    def seek(self, offset: int, whence: int) -> int:
        ...

    @abstractmethod
    def is_full(self) -> bool:
        ...

    @abstractmethod
    def ioctl(self, request, argp) -> int:
        ...

    @abstractmethod
    def tell(self) -> int:
        ...

    @abstractmethod
    def stat(self) -> StatResult:
        ...


@dataclass
class FdTableEntry:
    fdlike: FdLike
    rwaiters: Set[int]
    twaiters: Set[int]


class FdTable:
    """
    This represents Linux's file descriptor table.

    Each file descriptor maps to an C{FdLike} object.  Additionally, each file
    descriptor maps to a set of PIDs of processes that are waiting on that
    descriptor.
    """

    __slots__ = ["_mapping"]

    def __init__(self):
        self._mapping: Dict[int, FdTableEntry] = {}

    def max_fd(self) -> Optional[int]:
        """
        Return the maximum file descriptor with an entry in this table.
        """
        return max(self._mapping)

    def _lookup(self, fd: int):
        try:
            return self._mapping[fd]
        except LookupError:
            raise FdError(f"{fd} is not a valid file descriptor", errno.EBADF)

    def _get_available_fd(self) -> int:
        # use the next available closed fd, if any
        m = self._mapping
        num_fds = len(m)
        next_fd = num_fds
        for fd in range(num_fds):
            if fd not in m:
                next_fd = fd
                break
        return next_fd

    def entries(self) -> Iterable[FdTableEntry]:
        return self._mapping.values()

    def has_entry(self, fd: int) -> bool:
        return fd in self._mapping

    def add_entry(self, f: FdLike) -> int:
        """
        Adds an entry for the given C{FdLike} to the file descriptor table,
        returning the file descriptor for it.
        """
        fd = self._get_available_fd()
        self.add_entry_at(f, fd)
        return fd

    def add_entry_at(self, f: FdLike, fd: int) -> None:
        """
        Adds an entry for the given C{FdLike} to the file descriptor table at
        the given file descriptor, which must not already have an entry.
        """
        assert fd not in self._mapping, f"{fd} already has an entry"
        self._mapping[fd] = FdTableEntry(fdlike=f, rwaiters=set(), twaiters=set())

    def remove_entry(self, fd: int) -> None:
        if fd not in self._mapping:
            raise FdError(f"{fd} is not a valid file descriptor", errno.EBADF)
        del self._mapping[fd]

    def get_fdlike(self, fd: int) -> FdLike:
        """
        Returns the C{FdLike} associated with the given file descriptor.
        Raises C{FdError} if the file descriptor is invalid.
        """
        return self._lookup(fd).fdlike

    def get_rwaiters(self, fd: int) -> Set[int]:
        return self._lookup(fd).rwaiters

    def get_twaiters(self, fd: int) -> Set[int]:
        return self._lookup(fd).twaiters


@concreteclass
class File(FdLike):
    def __init__(self, path: str, flags: int):
        # TODO: assert file is seekable; otherwise we should save what was
        # read from/written to the state
        mode = mode_from_flags(flags)
        if mode == "rb+" and not os.path.exists(path):
            mode = "wb+"
        self.file: IO[Any] = open(path, mode)

    def __getstate__(self):
        state = {"name": self.name, "mode": self.mode, "closed": self.closed}
        try:
            state["pos"] = None if self.closed else self.tell()
        except IOError:
            # This is to handle special files like /dev/tty
            state["pos"] = None
        return state

    def __setstate__(self, state):
        name = state["name"]
        mode = state["mode"]
        closed = state["closed"]
        pos = state["pos"]
        try:
            self.file = open(name, mode)
            if closed:
                self.file.close()
        except IOError:
            # If the file can't be opened anymore (should not typically happen)
            self.file = None
        if pos is not None:
            self.seek(pos)

    @property
    def name(self) -> str:
        return self.file.name

    @property
    def mode(self) -> str:
        return self.file.mode

    @property
    def closed(self) -> bool:
        return self.file.closed

    def stat(self) -> StatResult:
        try:
            return convert_os_stat(os.stat(self.fileno()))
        except OSError as e:
            raise FdError(f"Cannot stat: {e.strerror}", e.errno)

    def ioctl(self, request, argp):
        try:
            return fcntl.fcntl(self, request, argp)
        except OSError as e:
            logger.error(f"Invalid Fcntl request: {request}")
            return -e.errno

    def tell(self) -> int:
        return self.file.tell()

    def seek(self, offset: int, whence: int = os.SEEK_SET) -> int:
        return self.file.seek(offset, whence)

    def write(self, buf):
        return self.file.write(buf)

    def read(self, size):
        return self.file.read(size)

    def close(self) -> None:
        self.file.close()

    def fileno(self) -> int:
        return self.file.fileno()

    def is_full(self) -> bool:
        return False

    def sync(self) -> None:
        pass


# TODO - we should consider refactoring File so that we don't have to mute these errors
@concreteclass
class ProcSelfMaps(File):  # lgtm [py/missing-call-to-init]
    def __init__(self, flags: int, linux):
        # WARN: Does not call File.__init__. Should have the File API, but we manually
        # manage the underlying file and mode
        self.file = tempfile.NamedTemporaryFile(mode="w", delete=False)
        self.file.write(linux.current.memory.__proc_self__)
        self.file.close()
        mode = mode_from_flags(flags)
        if mode != "rb":
            raise EnvironmentError("/proc/self/maps is only supported in read only mode")
        self.file = open(self.file.name, mode)


@concreteclass
class Directory(FdLike):
    def __init__(self, path: str, flags: int):
        # WARN: Does not call File.__init__ because we don't want to open the directory,
        # even though we still want it to present the same API as File
        assert os.path.isdir(path)
        self.fd = os.open(path, flags)
        self.path = path
        self.flags = flags

    def __getstate__(self):
        state = {}
        state["path"] = self.path
        state["flags"] = self.flags
        return state

    def __setstate__(self, state):
        self.path = state["path"]
        self.flags = state["flags"]
        self.fd = os.open(self.path, self.flags)

    @property
    def name(self) -> str:
        return self.path

    @property
    def mode(self) -> str:
        return mode_from_flags(self.flags)

    def tell(self) -> int:
        return 0

    def seek(self, offset: int, whence: int = os.SEEK_SET) -> int:
        return 0

    def write(self, buf):
        raise FdError("Is a directory", errno.EBADF)

    def read(self, size):
        raise FdError("Is a directory", errno.EISDIR)

    def close(self):
        try:
            return os.close(self.fd)
        except OSError as e:
            return -e.errno

    def stat(self) -> StatResult:
        try:
            return convert_os_stat(os.stat(self.fileno()))
        except OSError as e:
            raise FdError(f"Cannot stat: {e.strerror}", e.errno)

    def fileno(self):
        return self.fd

    def sync(self) -> None:
        pass

    def is_full(self) -> bool:
        return False

    def ioctl(self, request, argp):
        raise FdError("Invalid ioctl() operation on Directory", errno.ENOTTY)


@concreteclass
class SymbolicFile(File):
    """
    Represents a symbolic file.
    """

    def __init__(
        self,
        constraints,
        path: str = "sfile",
        flags: int = os.O_RDWR,
        max_size: int = 100,
        wildcard: str = "+",
    ):
        """
        Builds a symbolic file

        :param constraints: the SMT constraints
        :param path: the pathname of the symbolic file
        :param mode: the access permissions of the symbolic file
        :param max_size: Maximum amount of bytes of the symbolic file
        :param wildcard: Wildcard to be used in symbolic file
        """
        super().__init__(path, flags)

        # read the concrete data using the parent the read() form the File class
        data = self.file.read()

        self._constraints = constraints
        self.pos = 0
        self.max_size = min(len(data), max_size)

        # build the constraints array
        size = len(data)
        self.array = constraints.new_array(name=self.name, index_max=size)

        symbols_cnt = 0
        for i in range(size):
            if data[i] != wildcard:
                self.array[i] = data[i]
            else:
                symbols_cnt += 1

        if symbols_cnt > max_size:
            logger.warning(
                "Found more wildcards in the file than free symbolic values allowed (%d > %d)",
                symbols_cnt,
                max_size,
            )
        else:
            logger.debug("Found %d free symbolic values on file %s", symbols_cnt, self.name)

    def __getstate__(self):
        state = super().__getstate__()
        state["array"] = self.array
        state["pos"] = self.pos
        state["max_size"] = self.max_size
        return state

    def __setstate__(self, state):
        self.pos = state["pos"]
        self.max_size = state["max_size"]
        self.array = state["array"]
        super().__setstate__(state)

    def tell(self) -> int:
        """
        Returns the read/write file offset
        """
        return self.pos

    def seek(self, offset: int, whence: int = os.SEEK_SET) -> int:
        """
        Repositions the file C{offset} according to C{whence}.
        Returns the resulting offset or -1 in case of error.
        :return: the file offset.
        """
        assert isinstance(offset, int)
        assert whence in (os.SEEK_SET, os.SEEK_CUR, os.SEEK_END)

        new_position = 0
        if whence == os.SEEK_SET:
            new_position = offset
        elif whence == os.SEEK_CUR:
            new_position = self.pos + offset
        elif whence == os.SEEK_END:
            new_position = self.max_size + offset

        if new_position < 0:
            return -1

        self.pos = new_position

        return self.pos

    def read(self, count):
        """
        Reads up to C{count} bytes from the file.
        :rtype: list
        :return: the list of symbolic bytes read
        """
        if self.pos > self.max_size:
            return []
        else:
            size = min(count, self.max_size - self.pos)
            ret = [self.array[i] for i in range(self.pos, self.pos + size)]
            self.pos += size
            return ret

    def write(self, data):
        """
        Writes the symbolic bytes in C{data} onto the file.
        """
        size = min(len(data), self.max_size - self.pos)
        for i in range(self.pos, self.pos + size):
            self.array[i] = data[i - self.pos]


@concreteclass
class SocketDesc(FdLike):
    """
    Represents a socket descriptor that is not yet connected (i.e. a value returned by socket(2))
    """

    def __init__(self, domain=None, socket_type=None, protocol=None):
        self.domain = domain
        self.socket_type = socket_type
        self.protocol = protocol

    def close(self):
        pass

    def seek(self, offset: int, whence: int = os.SEEK_SET):
        raise FdError("Invalid write() operation on SocketDesc", errno.ESPIPE)  # EINVAL?  EBADF?

    def is_full(self):
        raise IsSocketDescErr()

    def read(self, count):
        raise FdError("Invalid write() operation on SocketDesc", errno.EBADF)  # EINVAL?

    def write(self, data):
        raise FdError("Invalid write() operation on SocketDesc", errno.EBADF)  # EPIPE?

    def sync(self):
        raise FdError("Invalid sync() operation on SocketDesc", errno.EINVAL)

    def ioctl(self, request, argp):
        raise FdError("Invalid ioctl() operation on SocketDesc", errno.ENOTTY)

    def tell(self) -> int:
        raise FdError("Invalid tell() operation on SocketDesc", errno.EBADF)

    def stat(self) -> StatResult:
        # Copied from Socket.stat
        return StatResult(
            8592, 11, 9, 1, 1000, 5, 0, 1378673920, 1378673920, 1378653796, 0x400, 0x8808, 0
        )


@concreteclass
class Socket(FdLike):
    def stat(self):
        return StatResult(
            8592, 11, 9, 1, 1000, 5, 0, 1378673920, 1378673920, 1378653796, 0x400, 0x8808, 0
        )

    @staticmethod
    def pair():
        a = Socket()
        b = Socket()
        a.connect(b)
        return a, b

    def __init__(self, net: bool = False):
        """
        Builds a normal socket that does not introduce symbolic bytes.

        :param net: Whether this is a network socket
        """
        from collections import deque

        self.buffer: Deque[
            Union[bytes, Expression]
        ] = deque()  # current bytes received but not read
        self.peer: Optional[Socket] = None
        self.net: bool = net

    def __getstate__(self):
        state = {"buffer": self.buffer, "net": self.net}
        return state

    def __setstate__(self, state):
        self.buffer = state["buffer"]
        self.net = state["net"]

    def __repr__(self):
        return f"SOCKET({hash(self):x}, buffer={self.buffer!r}, net={self.net}, peer={hash(self.peer):x})"

    def is_connected(self) -> bool:
        return self.peer is not None

    def is_empty(self) -> bool:
        return not self.buffer

    def is_full(self) -> bool:
        return len(self.buffer) > 2 * 1024

    def connect(self, peer):
        assert not self.is_connected()
        assert not peer.is_connected()
        self.peer = peer
        if peer.peer is None:
            peer.peer = self

    def read(self, size: int):
        return self.receive(size)

    def receive(self, size: int):
        rx_bytes = min(size, len(self.buffer))
        ret = []
        for i in range(rx_bytes):
            ret.append(self.buffer.popleft())
        return ret

    def write(self, buf):
        if self.net:
            # Just return like we were able to send all data
            # TODO: We should put this data somewhere to let the user know what is being sent.
            #   I don't think stdout is correct. It would be nice to know what is being sent
            #   over each network connection
            return len(buf)
        # If not a network Socket, it should be connected
        assert self.is_connected(), f"Non-network socket is not connected: {self.__repr__()}"
        return self.peer._transmit(buf)

    def _transmit(self, buf) -> int:
        for c in buf:
            self.buffer.append(c)
        return len(buf)

    def sync(self):
        raise FdError("Invalid sync() operation on Socket", errno.EINVAL)

    def seek(self, offset: int, whence: int = os.SEEK_SET) -> int:
        raise FdError("Invalid lseek() operation on Socket", errno.ESPIPE)

    def tell(self) -> int:
        raise FdError("Invalid tell() operation on Socket", errno.EBADF)

    def close(self):
        """
        Doesn't need to do anything; fixes "no attribute 'close'" error.
        """
        pass

    def ioctl(self, request, argp):
        raise FdError("Invalid ioctl() operation on Socket", errno.ENOTTY)


@concreteclass
class SymbolicSocket(Socket):
    """
    Symbolic sockets are generally used for network communications that contain user-controlled input.
    """

    def __init__(
        self,
        constraints: ConstraintSet,
        name: str,
        max_recv_symbolic: int = 80,
        net: bool = True,
        wildcard: str = "+",
    ):
        """
        Builds a symbolic socket.

        :param constraints: the SMT constraints
        :param name: The name of the SymbolicSocket, which is propagated to the symbolic variables introduced
        :param max_recv_symbolic: Maximum number of bytes allowed to be read from this socket. 0 for unlimited
        :param net: Whether this is a network connection socket
        :param wildcard: Wildcard to be used for symbolic bytes in socket. Not supported, yet
        """
        super().__init__(net=net)
        self._constraints = constraints
        self.symb_name = name
        self.max_recv_symbolic = max_recv_symbolic  # 0 for unlimited. Unlimited is not tested
        # Keep track of the symbolic inputs we create
        self.inputs_recvd: List[ArrayProxy] = []
        self.recv_pos = 0
        # This is a meta-variable, of sorts, and it is responsible for
        # determining the symbolic length of the array during recv/read.
        # Initially, it is None, to indicate we haven't forked yet. After
        # fork, each state will be assigned their respective _actual_,
        # concretized, receive length
        self._symb_len: Optional[int] = None
        # Set after adding this socket to the file descriptor list
        self.fd: Optional[int] = None

    def __getstate__(self):
        state = super().__getstate__()
        state["inputs_recvd"] = self.inputs_recvd
        state["symb_name"] = self.symb_name
        state["recv_pos"] = self.recv_pos
        state["max_recv_symbolic"] = self.max_recv_symbolic
        state["_symb_len"] = self._symb_len
        state["fd"] = self.fd
        return state

    def __setstate__(self, state):
        super().__setstate__(state)
        self.inputs_recvd = state["inputs_recvd"]
        self.symb_name = state["symb_name"]
        self.recv_pos = state["recv_pos"]
        self.max_recv_symbolic = state["max_recv_symbolic"]
        self._symb_len = state["_symb_len"]
        self.fd = state["fd"]

    def __repr__(self):
        return f"SymbolicSocket({hash(self):x}, fd={self.fd}, inputs_recvd={self.inputs_recvd}, buffer={self.buffer}, net={self.net}"

    def _next_symb_name(self) -> str:
        """
        Return the next name for a symbolic array, based on previous number of other receives
        """
        return f"{self.symb_name}-{len(self.inputs_recvd)}"

    def receive(self, size: int) -> Union[ArrayProxy, List[bytes]]:
        """
        Return a symbolic array of either `size` or rest of remaining symbolic bytes
        :param size: Size of receive
        :return: Symbolic array or list of concrete bytes
        """
        # First, get our max valid rx_bytes size
        rx_bytes = (
            size
            if self.max_recv_symbolic == 0
            else min(size, self.max_recv_symbolic - self.recv_pos)
        )
        if rx_bytes == 0:
            # If no symbolic bytes left, return empty list
            return []
        # Then do some forking with self._symb_len
        if self._symb_len is None:
            self._symb_len = self._constraints.new_bitvec(
                8, "_socket_symb_len", avoid_collisions=True
            )
            self._constraints.add(Operators.AND(self._symb_len >= 1, self._symb_len <= rx_bytes))

            def setstate(state: State, value):
                state.platform.fd_table.get_fdlike(self.fd)._symb_len = value

            logger.debug("Raising concretize in SymbolicSocket receive")
            raise Concretize(
                "Returning symbolic amount of data to SymbolicSocket",
                self._symb_len,
                setstate=setstate,
                policy="MINMAX",
            )
        ret = self._constraints.new_array(
            name=self._next_symb_name(), index_max=self._symb_len, avoid_collisions=True
        )
        logger.info(f"Setting recv symbolic length to {self._symb_len}")
        self.recv_pos += self._symb_len
        self.inputs_recvd.append(ret)
        # Reset _symb_len for next recv
        self._symb_len = None
        return ret


class Linux(Platform):
    """
    A simple Linux Operating System Platform.
    This class emulates the most common Linux system calls
    """

    # from /usr/include/asm-generic/resource.h
    FCNTL_FDCWD = -100  # /* Special value used to indicate openat should use the cwd */

    # Hard-coded base load address for dynamic elf binaries (ET_DYN in pyelftools)
    BASE_DYN_ADDR_32 = 0x56555000
    BASE_DYN_ADDR = 0x555555554000

    def __init__(
        self,
        program: Optional[str],
        argv: List[str] = [],
        envp: List[str] = [],
        disasm: str = "capstone",
        **kwargs,
    ):
        """
        Builds a Linux OS platform
        :param string program: The path to ELF binary
        :param string disasm: Disassembler to be used
        :param list argv: The argv array; not including binary.
        :param list envp: The ENV variables.
        """
        super().__init__(path=program, **kwargs)

        self.program = program
        self.clocks: int = 0
        self.fd_table: FdTable = FdTable()
        # A cache for keeping state when reading directories { fd: dent_iter }
        self._getdents_c: Dict[int, Any] = {}
        self._closed_files: List[FdLike] = []
        self.syscall_trace: List[Tuple[str, int, bytes]] = []
        # Many programs to support SLinux
        self.programs = program
        self.disasm = disasm
        self.envp = envp
        self.argv = argv
        self.stubs = SyscallStubs(parent=self)

        # dict of [int -> (int, int)] where tuple is (soft, hard) limits
        self._rlimits = {
            resource.RLIMIT_NOFILE: (256, 1024),
            resource.RLIMIT_STACK: (8192 * 1024, 0),
        }

        if program is not None:
            self.elf = ELFFile(open(program, "rb"))
            # FIXME (theo) self.arch is actually mode as initialized in the CPUs,
            # make things consistent and perhaps utilize a global mapping for this
            self.arch = {"x86": "i386", "x64": "amd64", "ARM": "armv7", "AArch64": "aarch64"}[
                self.elf.get_machine_arch()
            ]

            self._init_cpu(self.arch)
            self._init_std_fds()
            self._execve(program, argv, envp)

    def __del__(self):
        elf = getattr(self, "elf", None)
        if elf is not None:
            try:
                # Prevents a ResourceWarning
                elf.stream.close()
            except IOError as e:
                logger.error(str(e))

    @property
    def PC(self):
        return (self._current, self.procs[self._current].PC)

    def __deepcopy__(self, memo):
        return self

    @classmethod
    def empty_platform(cls, arch):
        """
        Create a platform without an ELF loaded.

        :param str arch: The architecture of the new platform
        :rtype: Linux
        """
        platform = cls(None)
        platform._init_cpu(arch)
        platform._init_std_fds()
        return platform

    def _init_std_fds(self) -> None:
        # open standard files stdin, stdout, stderr
        logger.debug("Opening file descriptors (0,1,2) (STDIN, STDOUT, STDERR)")
        self.input = Socket()
        self.output = Socket()
        self.stderr = Socket()

        stdin = Socket()
        stdout = Socket()
        stderr = Socket()
        # A transmit to stdin,stdout or stderr will be directed to out
        stdin.peer = self.output
        stdout.peer = self.output
        stderr.peer = self.stderr
        # A receive from stdin will get data from input
        self.input.peer = stdin
        # A receive on stdout or stderr will return no data (rx_bytes: 0)

        in_fd = self._open(stdin)
        out_fd = self._open(stdout)
        err_fd = self._open(stderr)

        assert (in_fd, out_fd, err_fd) == (0, 1, 2)

    def _init_cpu(self, arch: str) -> None:
        # create memory and CPU
        cpu = self._mk_proc(arch)
        self.procs: List[Cpu] = [cpu]
        self._current: Optional[int] = 0
        self._function_abi = CpuFactory.get_function_abi(cpu, "linux", arch)
        self._syscall_abi = CpuFactory.get_syscall_abi(cpu, "linux", arch)

    def _find_symbol(self, name: str):
        symbol_tables = (s for s in self.elf.iter_sections() if isinstance(s, SymbolTableSection))

        for section in symbol_tables:
            if section["sh_entsize"] == 0:
                continue

            for symbol in section.iter_symbols():
                if describe_symbol_type(symbol["st_info"]["type"]) == "FUNC":
                    if symbol.name == name:
                        return symbol["st_value"]

        return None

    def _execve(self, program: str, argv: List[str], envp: List[str]) -> None:
        """
        Load `program` and establish program state, such as stack and arguments.

        :param program str: The ELF binary to load
        :param argv list: argv array
        :param envp list: envp array
        """
        logger.debug(f"Loading {program} as a {self.arch} elf")

        self.load(program, envp)
        self._arch_specific_init()

        self._stack_top = self.current.STACK
        self.setup_stack([program] + argv, envp)

        nprocs = len(self.procs)
        assert nprocs > 0
        self.running = list(range(nprocs))

        # Each process can wait for one timeout
        self.timers: List[Optional[int]] = [None] * nprocs

        # Install event forwarders
        for proc in self.procs:
            self.forward_events_from(proc)

    def _mk_proc(self, arch: str) -> Cpu:
        mem = Memory32() if arch in {"i386", "armv7"} else Memory64()
        cpu = CpuFactory.get_cpu(mem, arch)
        return cpu

    @property
    def current(self) -> Cpu:
        assert self._current is not None
        return self.procs[self._current]

    def __getstate__(self):
        state = super().__getstate__()
        state["clocks"] = self.clocks
        state["input"] = self.input.buffer
        state["output"] = self.output.buffer

        state["fd_table"] = self.fd_table
        state["_getdents_c"] = self._getdents_c
        state["_closed_files"] = self._closed_files
        state["_rlimits"] = self._rlimits

        state["procs"] = self.procs
        state["_current"] = self._current
        state["running"] = self.running
        state["timers"] = self.timers
        state["syscall_trace"] = self.syscall_trace
        state["argv"] = self.argv
        state["envp"] = self.envp
        state["base"] = self.base
        state["elf_bss"] = self.elf_bss
        state["end_code"] = self.end_code
        state["end_data"] = self.end_data
        state["elf_brk"] = self.elf_brk
        state["brk"] = self.brk
        state["auxv"] = self.auxv
        state["program"] = self.program
        state["_function_abi"] = self._function_abi
        state["_syscall_abi"] = self._syscall_abi
        state["_uname_machine"] = self._uname_machine

        _arm_tls_memory = getattr(self, "_arm_tls_memory", None)
        if _arm_tls_memory is not None:
            state["_arm_tls_memory"] = _arm_tls_memory

        return state

    def __setstate__(self, state: Dict) -> None:
        """
        :todo: some asserts
        """
        super().__setstate__(state)

        self.input = Socket()
        self.input.buffer = state["input"]
        self.output = Socket()
        self.output.buffer = state["output"]

        # fetch each file descriptor (Socket or File())
        self.fd_table = state["fd_table"]

        # If file descriptors for stdin/stdout/stderr aren't closed, connect them
        try:
            stdin = self.fd_table.get_fdlike(0)
            if isinstance(stdin, Socket):
                stdin.peer = self.output
                self.input.peer = stdin
        except FdError:
            pass

        for fd in [1, 2]:
            try:
                f = self.fd_table.get_fdlike(fd)
                if isinstance(f, Socket):
                    f.peer = self.output
            except FdError:
                pass

        self._getdents_c = state["_getdents_c"]
        self._closed_files = state["_closed_files"]
        self._rlimits = state["_rlimits"]

        self.procs = state["procs"]
        self._current = state["_current"]
        self.running = state["running"]
        self.timers = state["timers"]
        self.clocks = state["clocks"]

        self.syscall_trace = state["syscall_trace"]
        self.argv = state["argv"]
        self.envp = state["envp"]
        self.base = state["base"]
        self.elf_bss = state["elf_bss"]
        self.end_code = state["end_code"]
        self.end_data = state["end_data"]
        self.elf_brk = state["elf_brk"]
        self.brk = state["brk"]
        self.auxv = state["auxv"]
        self.program = state["program"]
        self._function_abi = state["_function_abi"]
        self._syscall_abi = state["_syscall_abi"]
        self._uname_machine = state["_uname_machine"]
        self.stubs = SyscallStubs(parent=self)
        if "_arm_tls_memory" in state:
            self._arm_tls_memory = state["_arm_tls_memory"]

        # Install event forwarders
        for proc in self.procs:
            self.forward_events_from(proc)

    def _init_arm_kernel_helpers(self) -> None:
        """
        ARM kernel helpers

        https://www.kernel.org/doc/Documentation/arm/kernel_user_helpers.txt
        """

        page_data = bytearray(b"\xf1\xde\xfd\xe7" * 1024)

        # Extracted from a RPi2
        preamble = binascii.unhexlify(
            "ff0300ea"
            + "650400ea"
            + "f0ff9fe5"
            + "430400ea"
            + "220400ea"
            + "810400ea"
            + "000400ea"
            + "870400ea"
        )

        # XXX(yan): The following implementations of cmpxchg and cmpxchg64 were
        # handwritten to not use any exclusive instructions (e.g. ldrexd) or
        # locking. For actual implementations, refer to
        # arch/arm64/kernel/kuser32.S in the Linux source code.
        __kuser_cmpxchg64 = binascii.unhexlify(
            "30002de9"
            + "08c09de5"  # push    {r4, r5}
            + "30009ce8"  # ldr     ip, [sp, #8]
            + "010055e1"  # ldm     ip, {r4, r5}
            + "00005401"  # cmp     r5, r1
            + "0100a013"  # cmpeq   r4, r0
            + "0000a003"  # movne   r0, #1
            + "0c008c08"  # moveq   r0, #0
            + "3000bde8"  # stmeq   ip, {r2, r3}
            + "1eff2fe1"  # pop     {r4, r5}  # bx      lr
        )

        __kuser_dmb = binascii.unhexlify("5bf07ff5" + "1eff2fe1")  # dmb ish  # bx lr

        __kuser_cmpxchg = binascii.unhexlify(
            "003092e5"
            + "000053e1"  # ldr     r3, [r2]
            + "0000a003"  # cmp     r3, r0
            + "00108205"  # moveq   r0, #0
            + "0100a013"  # streq   r1, [r2]
            + "1eff2fe1"  # movne   r0, #1  # bx      lr
        )

        # Map a TLS segment
        self._arm_tls_memory = self.current.memory.mmap(None, 4, "rw ")

        __kuser_get_tls = binascii.unhexlify(
            "04009FE5" + "010090e8" + "1eff2fe1"  # ldr r0, [pc, #4]  # ldm r0, {r0}  # bx lr
        ) + struct.pack("<I", self._arm_tls_memory)

        tls_area = b"\x00" * 12

        version = struct.pack("<I", 5)

        def update(address, code):
            page_data[address : address + len(code)] = code

        # Offsets from Documentation/arm/kernel_user_helpers.txt in Linux
        update(0x000, preamble)
        update(0xF60, __kuser_cmpxchg64)
        update(0xFA0, __kuser_dmb)
        update(0xFC0, __kuser_cmpxchg)
        update(0xFE0, __kuser_get_tls)
        update(0xFF0, tls_area)
        update(0xFFC, version)

        self.current.memory.mmap(0xFFFF0000, len(page_data), "r x", page_data)

    def setup_stack(self, argv: List, envp: List) -> None:
        """
        :param Cpu cpu: The cpu instance
        :param argv: list of parameters for the program to execute.
        :param envp: list of environment variables for the program to execute.

        http://www.phrack.org/issues.html?issue=58&id=5#article
         position            content                     size (bytes) + comment
         ----------------------------------------------------------------------
         stack pointer ->  [ argc = number of args ]     4
                         [ argv[0] (pointer) ]         4   (program name)
                         [ argv[1] (pointer) ]         4
                         [ argv[..] (pointer) ]        4 * x
                         [ argv[n - 1] (pointer) ]     4
                         [ argv[n] (pointer) ]         4   (= NULL)

                         [ envp[0] (pointer) ]         4
                         [ envp[1] (pointer) ]         4
                         [ envp[..] (pointer) ]        4
                         [ envp[term] (pointer) ]      4   (= NULL)

                         [ auxv[0] (Elf32_auxv_t) ]    8
                         [ auxv[1] (Elf32_auxv_t) ]    8
                         [ auxv[..] (Elf32_auxv_t) ]   8
                         [ auxv[term] (Elf32_auxv_t) ] 8   (= AT_NULL vector)

                         [ padding ]                   0 - 16

                         [ argument ASCIIZ strings ]   >= 0
                         [ environment ASCIIZ str. ]   >= 0

         (0xbffffffc)      [ end marker ]                4   (= NULL)

         (0xc0000000)      < top of stack >              0   (virtual)
         ----------------------------------------------------------------------
        """
        cpu = self.current

        # In case setup_stack() is called again, we make sure we're growing the
        # stack from the original top
        cpu.STACK = self._stack_top

        auxv = self.auxv
        logger.debug("Setting argv, envp and auxv.")
        logger.debug(f"\tArguments: {argv!r}")
        if envp:
            logger.debug("\tEnvironment:")
            for e in envp:
                logger.debug(f"\t\t{e!r}")

        logger.debug("\tAuxv:")
        for name, val in auxv.items():
            logger.debug(f"\t\t{name}: 0x{val:x}")

        # We save the argument and environment pointers
        argvlst = []
        envplst = []

        # end envp marker empty string
        for evar in envp:
            cpu.push_bytes("\x00")
            envplst.append(cpu.push_bytes(evar))

        for arg in argv:
            cpu.push_bytes("\x00")
            argvlst.append(cpu.push_bytes(arg))

        # Put all auxv strings into the string stack area.
        # And replace the value be its pointer

        for name, value in auxv.items():
            if hasattr(value, "__len__"):
                cpu.push_bytes(value)
                auxv[name] = cpu.STACK

        # The "secure execution" mode of secure_getenv() is controlled by the
        # AT_SECURE flag contained in the auxiliary vector passed from the
        # kernel to user space.
        auxvnames = {
            "AT_IGNORE": 1,  # Entry should be ignored
            "AT_EXECFD": 2,  # File descriptor of program
            "AT_PHDR": 3,  # Program headers for program
            "AT_PHENT": 4,  # Size of program header entry
            "AT_PHNUM": 5,  # Number of program headers
            "AT_PAGESZ": 6,  # System page size
            "AT_BASE": 7,  # Base address of interpreter
            "AT_FLAGS": 8,  # Flags
            "AT_ENTRY": 9,  # Entry point of program
            "AT_NOTELF": 10,  # Program is not ELF
            "AT_UID": 11,  # Real uid
            "AT_EUID": 12,  # Effective uid
            "AT_GID": 13,  # Real gid
            "AT_EGID": 14,  # Effective gid
            "AT_CLKTCK": 17,  # Frequency of times()
            "AT_PLATFORM": 15,  # String identifying platform.
            "AT_HWCAP": 16,  # Machine-dependent hints about processor capabilities.
            "AT_FPUCW": 18,  # Used FPU control word.
            "AT_SECURE": 23,  # Boolean, was exec setuid-like?
            "AT_BASE_PLATFORM": 24,  # String identifying real platforms.
            "AT_RANDOM": 25,  # Address of 16 random bytes.
            "AT_EXECFN": 31,  # Filename of executable.
            "AT_SYSINFO": 32,  # Pointer to the global system page used for system calls and other nice things.
            "AT_SYSINFO_EHDR": 33,  # Pointer to the global system page used for system calls and other nice things.
        }
        # AT_NULL
        cpu.push_int(0)
        cpu.push_int(0)
        for name, val in auxv.items():
            cpu.push_int(val)
            cpu.push_int(auxvnames[name])

        # NULL ENVP
        cpu.push_int(0)
        for var in reversed(envplst):  # ENVP n
            cpu.push_int(var)
        envp = cpu.STACK

        # NULL ARGV
        cpu.push_int(0)
        for arg in reversed(argvlst):  # Argv n
            cpu.push_int(arg)
        argv = cpu.STACK

        # ARGC
        cpu.push_int(len(argvlst))

    def set_entry(self, entryPC):
        elf_entry = entryPC
        if self.elf.header.e_type == "ET_DYN":
            elf_entry += self.load_addr
        self.current.PC = elf_entry
        logger.debug(f"Entry point updated: {elf_entry:016x}")

    def load(self, filename: str, env_list: List) -> None:
        """
        Loads and an ELF program in memory and prepares the initial CPU state.
        Creates the stack and loads the environment variables and the arguments in it.

        :param filename: pathname of the file to be executed. (used for auxv)
        :param env_list: A list of env variables. (used for extracting vars that control ld behavior)
        :raises error:
            - 'Not matching cpu': if the program is compiled for a different architecture
            - 'Not matching memory': if the program is compiled for a different address size
        :todo: define va_randomize and read_implies_exec personality
        """
        # load elf See binfmt_elf.c
        # read the ELF object file
        cpu = self.current
        elf = self.elf
        arch = self.arch
        env = dict(var.split("=", 1) for var in env_list if "=" in var)
        addressbitsize = {"x86": 32, "x64": 64, "ARM": 32, "AArch64": 64}[elf.get_machine_arch()]
        logger.debug("Loading %s as a %s elf", filename, arch)

        assert elf.header.e_type in ["ET_DYN", "ET_EXEC", "ET_CORE"]

        # Get interpreter elf
        interpreter = None

        # Need to clean up when we are done
        def _clean_interp_stream() -> None:
            if interpreter is not None:
                try:
                    interpreter.stream.close()
                except IOError as e:
                    logger.error(str(e))

        for elf_segment in elf.iter_segments():
            if elf_segment.header.p_type != "PT_INTERP":
                continue
            interpreter_filename = elf_segment.data()[:-1]
            logger.info(f"Interpreter filename: {interpreter_filename}")
            if os.path.exists(interpreter_filename.decode("utf-8")):
                _clean_interp_stream()
                interpreter = ELFFile(open(interpreter_filename, "rb"))
            elif "LD_LIBRARY_PATH" in env:
                for mpath in env["LD_LIBRARY_PATH"].split(":"):
                    interpreter_path_filename = os.path.join(
                        mpath, os.path.basename(interpreter_filename)
                    )
                    logger.info(f"looking for interpreter {interpreter_path_filename}")
                    if os.path.exists(interpreter_path_filename):
                        _clean_interp_stream()
                        interpreter = ELFFile(open(interpreter_path_filename, "rb"))
                        break
            break

        if interpreter is not None:
            assert interpreter.get_machine_arch() == elf.get_machine_arch()
            assert interpreter.header.e_type in ["ET_DYN", "ET_EXEC"]

        # Stack Executability
        executable_stack = False
        for elf_segment in elf.iter_segments():
            if elf_segment.header.p_type != "PT_GNU_STACK":
                continue
            if elf_segment.header.p_flags & 0x01:
                executable_stack = True
            else:
                executable_stack = False
            break

        base = 0
        elf_bss = 0
        end_code = 0
        end_data = 0
        elf_brk = 0
        self.load_addr = 0

        for elf_segment in elf.iter_segments():
            if elf_segment.header.p_type != "PT_LOAD":
                continue

            align = 0x1000  # elf_segment.header.p_align

            ELF_PAGEOFFSET = elf_segment.header.p_vaddr & (align - 1)

            flags = elf_segment.header.p_flags
            memsz = elf_segment.header.p_memsz + ELF_PAGEOFFSET
            offset = elf_segment.header.p_offset - ELF_PAGEOFFSET
            filesz = elf_segment.header.p_filesz + ELF_PAGEOFFSET
            vaddr = elf_segment.header.p_vaddr - ELF_PAGEOFFSET
            memsz = cpu.memory._ceil(memsz)
            if base == 0 and elf.header.e_type == "ET_DYN":
                assert vaddr == 0
                if addressbitsize == 32:
                    base = self.BASE_DYN_ADDR_32
                else:
                    base = self.BASE_DYN_ADDR

            perms = perms_from_elf(flags)
            hint = base + vaddr
            if hint == 0:
                hint = None

            logger.debug(
                f"Loading elf offset: {offset:08x} addr:{base + vaddr:08x} {base + vaddr + memsz:08x} {perms}"
            )
            base = cpu.memory.mmapFile(hint, memsz, perms, elf_segment.stream.name, offset) - vaddr

            if self.load_addr == 0:
                self.load_addr = base + vaddr

            k = base + vaddr + filesz
            if k > elf_bss:
                elf_bss = k
            if (flags & 4) and end_code < k:  # PF_X
                end_code = k
            if end_data < k:
                end_data = k
            k = base + vaddr + memsz
            if k > elf_brk:
                elf_brk = k

        elf_entry = elf.header.e_entry
        if elf.header.e_type == "ET_DYN":
            elf_entry += self.load_addr
        entry = elf_entry
        real_elf_brk = elf_brk

        # We need to explicitly clear bss, as fractional pages will have data from the file
        bytes_to_clear = elf_brk - elf_bss
        if bytes_to_clear > 0:
            logger.debug(
                f"Zeroing main elf fractional pages. From bss({elf_bss:x}) to brk({elf_brk:x}), {bytes_to_clear} bytes."
            )
            cpu.write_bytes(elf_bss, "\x00" * bytes_to_clear, force=True)

        stack_size = 0x21000

        if addressbitsize == 32:
            stack_top = 0xC0000000
        else:
            stack_top = 0x800000000000
        stack_base = stack_top - stack_size
        stack = cpu.memory.mmap(stack_base, stack_size, "rwx", name="stack") + stack_size
        assert stack_top == stack

        reserved = cpu.memory.mmap(base + vaddr + memsz, 0x1000000, "   ")
        interpreter_base = 0
        if interpreter is not None:
            base = 0
            elf_bss = 0
            end_code = 0
            end_data = 0
            elf_brk = 0
            entry = interpreter.header.e_entry
            for elf_segment in interpreter.iter_segments():
                if elf_segment.header.p_type != "PT_LOAD":
                    continue
                align = 0x1000  # elf_segment.header.p_align
                vaddr = elf_segment.header.p_vaddr
                filesz = elf_segment.header.p_filesz
                flags = elf_segment.header.p_flags
                offset = elf_segment.header.p_offset
                memsz = elf_segment.header.p_memsz

                ELF_PAGEOFFSET = vaddr & (align - 1)
                memsz = memsz + ELF_PAGEOFFSET
                offset = offset - ELF_PAGEOFFSET
                filesz = filesz + ELF_PAGEOFFSET
                vaddr = vaddr - ELF_PAGEOFFSET
                memsz = cpu.memory._ceil(memsz)

                if base == 0 and interpreter.header.e_type == "ET_DYN":
                    assert vaddr == 0
                    total_size = self._interp_total_size(interpreter)
                    base = stack_base - total_size

                if base == 0:
                    assert vaddr == 0
                perms = perms_from_elf(flags)
                hint = base + vaddr
                if hint == 0:
                    hint = None

                base = cpu.memory.mmapFile(
                    hint, memsz, perms, elf_segment.stream.name.decode("utf-8"), offset
                )
                base -= vaddr
                logger.debug(
                    f"Loading interpreter offset: {offset:08x} "
                    f"addr:{base + vaddr:08x} "
                    f"{base + vaddr + memsz:08x} "
                    f"{(flags & 1 and 'r' or ' ')}"
                    f"{(flags & 2 and 'w' or ' ')}"
                    f"{(flags & 4 and 'x' or ' ')}"
                )

                k = base + vaddr + filesz
                if k > elf_bss:
                    elf_bss = k
                if (flags & 4) and end_code < k:  # PF_X
                    end_code = k
                if end_data < k:
                    end_data = k
                k = base + vaddr + memsz
                if k > elf_brk:
                    elf_brk = k

            if interpreter.header.e_type == "ET_DYN":
                entry += base
            interpreter_base = base

            bytes_to_clear = elf_brk - elf_bss
            if bytes_to_clear > 0:
                logger.debug(
                    f"Zeroing interpreter elf fractional pages. From bss({elf_bss:x}) to brk({elf_brk:x}), {bytes_to_clear} bytes."
                )
                cpu.write_bytes(elf_bss, "\x00" * bytes_to_clear, force=True)

        # free reserved brk space
        cpu.memory.munmap(reserved, 0x1000000)

        cpu.STACK = stack
        cpu.PC = entry

        logger.debug(f"Entry point: {entry:016x}")
        logger.debug(f"Stack start: {stack:016x}")
        logger.debug(f"Brk: {real_elf_brk:016x}")
        logger.debug(f"Mappings:")
        for m in str(cpu.memory).split("\n"):
            logger.debug(f"  {m}")
        self.base = base
        self.elf_bss = elf_bss
        self.end_code = end_code
        self.end_data = end_data
        self.elf_brk = real_elf_brk
        self.brk = real_elf_brk

        at_random = cpu.push_bytes("A" * 16)
        at_execfn = cpu.push_bytes(f"{filename}\x00")

        self.auxv = {
            "AT_PHDR": self.load_addr + elf.header.e_phoff,  # Program headers for program
            "AT_PHENT": elf.header.e_phentsize,  # Size of program header entry
            "AT_PHNUM": elf.header.e_phnum,  # Number of program headers
            "AT_PAGESZ": cpu.memory.page_size,  # System page size
            "AT_BASE": interpreter_base,  # Base address of interpreter
            "AT_FLAGS": elf.header.e_flags,  # Flags
            "AT_ENTRY": elf_entry,  # Entry point of program
            "AT_UID": 1000,  # Real uid
            "AT_EUID": 1000,  # Effective uid
            "AT_GID": 1000,  # Real gid
            "AT_EGID": 1000,  # Effective gid
            "AT_CLKTCK": 100,  # Frequency of times()
            "AT_HWCAP": 0,  # Machine-dependent hints about processor capabilities.
            "AT_RANDOM": at_random,  # Address of 16 random bytes.
            "AT_EXECFN": at_execfn,  # Filename of executable.
        }

        # Clean up interpreter ELFFile
        _clean_interp_stream()

    def _to_signed_dword(self, dword: int):
        arch_width = self.current.address_bit_size
        if arch_width == 32:
            sdword = ctypes.c_int32(dword).value
        elif arch_width == 64:
            sdword = ctypes.c_int64(dword).value
        else:
            raise EnvironmentError(f"Corrupted internal CPU state (arch width is {arch_width})")
        return sdword

    def _open(self, f: FdLike) -> int:
        """
        Adds a file descriptor to the current file descriptor list

        :param f: the file descriptor to add.
        :return: the index of the file descriptor in the file descr. list
        """
        return self.fd_table.add_entry(f)

    def _close(self, fd: int) -> None:
        """
        Removes a file descriptor from the file descriptor list
        :param fd: the file descriptor to close.
        """
        f = self.fd_table.get_fdlike(fd)
        f.close()
        self.fd_table.remove_entry(fd)
        self._closed_files.append(f)  # Keep track for SymbolicFile testcase generation

    def _is_fd_open(self, fd: int) -> bool:
        """
        Determines if the fd is within range and in the file descr. list
        :param fd: the file descriptor to check.
        """
        return self.fd_table.has_entry(fd)

    def _get_fdlike(self, fd: int) -> FdLike:
        """
        Returns the File or Socket corresponding to the given file descriptor.
        """
        return self.fd_table.get_fdlike(fd)

    def _transform_write_data(self, data) -> bytes:
        """
        Implement in subclass to transform data written by write(2)/writev(2)
        Nop by default.
        """
        return data

    def _exit(self, message) -> None:
        procid = self.procs.index(self.current)
        self.sched()
        self.running.remove(procid)
        if len(self.running) == 0:
            raise TerminateState(message, testcase=True)

    def sys_umask(self, mask: int) -> int:
        """
        umask - Set file creation mode mask
        :param int mask: New mask
        """
        logger.debug(f"umask({mask:o})")
        try:
            return os.umask(mask)
        except OSError as e:
            return -e.errno

    def sys_chdir(self, path) -> int:
        """
        chdir - Change current working directory
        :param int path: Pointer to path
        """
        path_str = self.current.read_string(path)
        logger.debug(f"chdir({path_str})")
        try:
            os.chdir(path_str)
            return 0
        except OSError as e:
            return -e.errno

    def sys_getcwd(self, buf, size) -> int:
        """
        getcwd - Get the current working directory
        :param int buf: Pointer to dest array
        :param size: size in bytes of the array pointed to by the buf
        :return: buf (Success), or 0
        """

        try:
            current_dir = os.getcwd()
            length = len(current_dir) + 1

            if size > 0 and size < length:
                logger.info(
                    "GETCWD: size is greater than 0, but is smaller than the length "
                    "of the path + 1. Returning -errno.ERANGE"
                )
                return -errno.ERANGE

            if not self.current.memory.access_ok(slice(buf, buf + length), "w"):
                logger.info("GETCWD: buf within invalid memory. Returning -errno.EFAULT")
                return -errno.EFAULT

            self.current.write_string(buf, current_dir)
            logger.debug(f"getcwd(0x{buf:08x}, {size}) -> <{current_dir}> (Size {length})")
            return length

        except OSError as e:
            return -e.errno

    def sys_lseek(self, fd: int, offset: int, whence: int) -> int:
        """
        lseek - reposition read/write file offset

        The lseek() function repositions the file offset of the open file description associated
        with the file descriptor fd to the argument offset according to the directive whence


        :param fd: a valid file descriptor
        :param offset: the offset in bytes
        :param whence: os.SEEK_SET: The file offset is set to offset bytes.
                       os.SEEK_CUR: The file offset is set to its current location plus offset bytes.
                       os.SEEK_END: The file offset is set to the size of the file plus offset bytes.

        :return: offset from file beginning, or EBADF (fd is not a valid file descriptor or is not open)
        """
        signed_offset = self._to_signed_dword(offset)
        try:
            return self._get_fdlike(fd).seek(signed_offset, whence)
        except FdError as e:
            logger.info(
                f"sys_lseek: Not valid file descriptor on lseek. Fd not seekable. Returning -{errorcode(e.err)}"
            )
            return -e.err

    def sys_llseek(
        self, fd: int, offset_high: int, offset_low: int, resultp: int, whence: int
    ) -> int:
        """
        _llseek - reposition read/write file offset

        The  _llseek()  system  call  repositions  the  offset  of  the open
        file description associated with the file descriptor fd to
        (offset_high<<32) | offset_low bytes relative to the beginning of the
        file, the current  file offset,  or the end of the file, depending on
        whether whence is os.SEEK_SET, os.SEEK_CUR, or os.SEEK_END,
        respectively.  It returns the resulting file position in the argument
        result.

        This system call exists on various 32-bit platforms to support seeking
        to large file offsets.

        :param fd: a valid file descriptor
        :param offset_high: the high 32 bits of the byte offset
        :param offset_low: the low 32 bits of the byte offset
        :param resultp: a pointer to write the position into on success
        :param whence: os.SEEK_SET: The file offset is set to offset bytes.
                       os.SEEK_CUR: The file offset is set to its current location plus offset bytes.
                       os.SEEK_END: The file offset is set to the size of the file plus offset bytes.

        :return: 0 on success, negative on error
        """
        signed_offset_high = self._to_signed_dword(offset_high)
        signed_offset_low = self._to_signed_dword(offset_low)
        signed_offset = (signed_offset_high << 32) | signed_offset_low
        try:
            pos = self._get_fdlike(fd).seek(signed_offset, whence)
            posbuf = struct.pack("q", pos)  # `loff_t * resultp` in linux, which is `long long`
            self.current.write_bytes(resultp, posbuf)
            return 0
        except FdError as e:
            logger.info(
                f"sys_llseek: Not valid file descriptor on llseek. Fd not seekable. Returning -{errorcode(e.err)}"
            )
            return -e.err

    def sys_read(self, fd: int, buf: int, count: int) -> int:
        data: bytes = bytes()
        if count != 0:
            # TODO check count bytes from buf
            if buf not in self.current.memory:  # or not  self.current.memory.isValid(buf+count):
                logger.info("sys_read: buf points to invalid address. Returning -errno.EFAULT")
                return -errno.EFAULT

            try:
                # Read the data and put it in memory
                data = self._get_fdlike(fd).read(count)
            except FdError as e:
                logger.info(
                    f"sys_read: Not valid file descriptor ({fd}). Returning -{errorcode(e.err)}"
                )
                return -e.err
            self.syscall_trace.append(("_read", fd, data))
            self.current.write_bytes(buf, data)

        return len(data)

    def sys_write(self, fd: int, buf, count) -> int:
        """ write - send bytes through a file descriptor
          The write system call writes up to count bytes from the buffer pointed
          to by buf to the file descriptor fd. If count is zero, write returns 0
          and optionally sets *tx_bytes to zero.

          :param fd            a valid file descriptor
          :param buf           a memory buffer
          :param count         number of bytes to send
          :return: 0          Success
                    EBADF      fd is not a valid file descriptor or is not open.
                    EFAULT     buf or tx_bytes points to an invalid address.
        """
        data: bytes = bytes()
        cpu = self.current
        if count != 0:
            try:
                write_fd = self._get_fdlike(fd)
            except FdError as e:
                logger.error(
                    f"sys_write: Not valid file descriptor ({fd}). Returning -{errorcode(e.err)}"
                )
                return -e.err

            # TODO check count bytes from buf
            if buf not in cpu.memory or buf + count not in cpu.memory:
                logger.debug("sys_write: buf points to invalid address. Returning -errno.EFAULT")
                return -errno.EFAULT

            if fd > 2 and write_fd.is_full():
                cpu.PC -= cpu.instruction.size
                self.wait([], [fd], None)
                raise RestartSyscall()

            data_sym: MixedSymbolicBuffer = cpu.read_bytes(buf, count)
            data = self._transform_write_data(data_sym)
            write_fd.write(data)

            for line in data.split(b"\n"):
                line_str = line.decode(
                    "latin-1"
                )  # latin-1 encoding will happily decode any byte (0x00-0xff)
                logger.debug(f"sys_write({fd}, 0x{buf:08x}, {count}) -> <{repr(line_str):48s}>")
            self.syscall_trace.append(("_write", fd, data))
            self.signal_transmit(fd)

        return len(data)

    def sys_fork(self) -> int:
        """
        We don't support forking, but do return a valid error code to client binary.
        """
        return -errno.ENOSYS

    def sys_access(self, buf: int, mode: int) -> int:
        """
        Checks real user's permissions for a file

        :param buf: a buffer containing the pathname to the file to check its permissions.
        :param mode: the access permissions to check.
        :return:
            -  C{0} if the calling process can access the file in the desired mode.
            - C{-1} if the calling process can not access the file in the desired mode.
        """
        filename = b""
        for i in range(0, 255):
            c = Operators.CHR(self.current.read_int(buf + i, 8))
            if c == b"\x00":
                break
            filename += c

        if os.access(filename, mode):
            return 0
        else:
            if not os.path.exists(filename):
                return -errno.ENOENT
            return -1

    def sys_newuname(self, old_utsname):
        """
        Writes system information in the variable C{old_utsname}.
        :rtype: int
        :param old_utsname: the buffer to write the system info.
        :return: C{0} on success
        """
        from datetime import datetime

        def pad(s):
            return s + "\x00" * (65 - len(s))

        now = datetime(2017, 8, 0o1).strftime("%a %b %d %H:%M:%S ART %Y")
        info = (
            ("sysname", "Linux"),
            ("nodename", "ubuntu"),
            ("release", "4.4.0-77-generic"),
            ("version", "#98 SMP " + now),
            ("machine", self._uname_machine),
            ("domainname", ""),
        )

        uname_buf = "".join(pad(pair[1]) for pair in info)
        self.current.write_bytes(old_utsname, uname_buf)
        return 0

    def sys_brk(self, brk):
        """
        Changes data segment size (moves the C{brk} to the new address)
        :rtype: int
        :param brk: the new address for C{brk}.
        :return: the value of the new C{brk}.
        :raises error:
                    - "Error in brk!" if there is any error allocating the memory
        """
        if brk != 0 and brk > self.elf_brk:
            mem = self.current.memory
            size = brk - self.brk
            if brk > mem._ceil(self.brk):
                perms = mem.perms(self.brk - 1)
                addr = mem.mmap(mem._ceil(self.brk), size, perms)
                if not mem._ceil(self.brk) == addr:
                    logger.error(
                        f"Error in brk: ceil: {hex(mem._ceil(self.brk))} brk: {hex(brk)} self.brk: {hex(self.brk)} addr: {hex(addr)}"
                    )
                    return self.brk
            self.brk += size
        return self.brk

    def sys_arch_prctl(self, code, addr):
        """
        Sets architecture-specific thread state
        :rtype: int

        :param code: must be C{ARCH_SET_FS}.
        :param addr: the base address of the FS segment.
        :return: C{0} on success
        :raises error:
            - if C{code} is different to C{ARCH_SET_FS}
        """
        ARCH_SET_GS = 0x1001
        ARCH_SET_FS = 0x1002
        ARCH_GET_FS = 0x1003
        ARCH_GET_GS = 0x1004
        if code not in {ARCH_SET_GS, ARCH_SET_FS, ARCH_GET_FS, ARCH_GET_GS}:
            logger.debug("code not in expected options ARCH_GET/SET_FS/GS")
            return -errno.EINVAL
        if code != ARCH_SET_FS:
            raise NotImplementedError(
                "Manticore supports only arch_prctl with code=ARCH_SET_FS (0x1002) for now"
            )
        self.current.FS = 0x63
        self.current.set_descriptor(self.current.FS, addr, 0x4000, "rw")
        return 0

    def sys_ioctl(self, fd, request, argp) -> int:
        if fd > 2:
            try:
                return self.fd_table.get_fdlike(fd).ioctl(request, argp)
            except FdError as e:
                return -e.err
        else:
            return -errno.EINVAL

    def _sys_open_get_file(self, filename: str, flags: int) -> FdLike:
        # TODO(yan): Remove this special case
        if os.path.abspath(filename).startswith("/proc/self"):
            if filename == "/proc/self/exe":
                assert self.program is not None
                filename = os.path.abspath(self.program)
            elif filename == "/proc/self/maps":
                return ProcSelfMaps(flags, self)
            else:
                raise EnvironmentError(
                    f"Trying to read from {filename}.\nThe /proc/self filesystem is largely unsupported."
                )

        if os.path.isdir(filename):
            return Directory(filename, flags)
        else:
            return File(filename, flags)

    def sys_open(self, buf: int, flags: int, mode: Optional[int]) -> int:
        """
        :param buf: address of zero-terminated pathname
        :param flags: file access bits
        :param mode: file permission mode (ignored)
        """
        filename = self.current.read_string(buf)
        try:
            f = self._sys_open_get_file(filename, flags)
            logger.debug(f"sys_open: Opening file {filename} for real file {f!r}")
        except IOError as e:
            logger.warning(f"sys_open: Could not open file {filename}. Reason: {e!s}")
            return -e.errno if e.errno is not None else -errno.EINVAL

        return self._open(f)

    def sys_openat(self, dirfd: int, buf: int, flags: int, mode) -> int:
        """
        Openat SystemCall - Similar to open system call except dirfd argument
        when path contained in buf is relative, dirfd is referred to set the relative path
        Special value AT_FDCWD set for dirfd to set path relative to current directory

        :param dirfd: directory file descriptor to refer in case of relative path at buf
        :param buf: address of zero-terminated pathname
        :param flags: file access bits
        :param mode: file permission mode
        """

        filename = self.current.read_string(buf)
        dirfd = ctypes.c_int32(dirfd).value

        if os.path.isabs(filename) or dirfd == self.FCNTL_FDCWD:
            return self.sys_open(buf, flags, mode)

        try:
            dir_entry = self._get_fdlike(dirfd)
        except FdError as e:
            logger.info(f"sys_openat: Not valid file descriptor. Returning -{errorcode(e.err)}")
            return -e.err

        if not isinstance(dir_entry, Directory):
            logger.info("sys_openat: Not directory descriptor. Returning -errno.ENOTDIR")
            return -errno.ENOTDIR

        dir_path = dir_entry.name

        filename = os.path.join(dir_path, filename)
        try:
            f = self._sys_open_get_file(filename, flags)
            logger.debug(f"sys_openat: Opening file {filename} for real file {f!r}")
        except IOError as e:
            logger.info(f"sys_openat: Could not open file {filename}. Reason: {e!s}")
            return -e.errno if e.errno is not None else -errno.EINVAL

        return self._open(f)

    def sys_rename(self, oldnamep: int, newnamep: int) -> int:
        """
        Rename filename `oldnamep` to `newnamep`.

        :param int oldnamep: pointer to oldname
        :param int newnamep: pointer to newname
        """
        oldname = self.current.read_string(oldnamep)
        newname = self.current.read_string(newnamep)

        try:
            os.rename(oldname, newname)
        except OSError as e:
            return -e.errno
        return 0

    def sys_fsync(self, fd: int) -> int:
        """
        Synchronize a file's in-core state with that on disk.
        """

        try:
            self._get_fdlike(fd).sync()
            return 0
        except FdError as e:
            return -e.err

    def sys_getpid(self):
        logger.debug("GETPID, warning pid modeled as concrete 1000")
        return 1000

    def sys_gettid(self):
        logger.debug("GETTID, warning tid modeled as concrete 1000")
        return 1000

    def sys_ARM_NR_set_tls(self, val):
        if hasattr(self, "_arm_tls_memory"):
            self.current.write_int(self._arm_tls_memory, val)
            self.current.set_arm_tls(val)
        return 0

    # Signals..
    def sys_kill(self, pid, sig):
        logger.warning(f"KILL, Ignoring Sending signal {sig} to pid {pid}")
        return 0

    def sys_rt_sigaction(self, signum, act, oldact, _sigsetsize):
        """Wrapper for sys_sigaction"""
        return self.sys_sigaction(signum, act, oldact)

    def sys_sigaction(self, signum, act, oldact):
        logger.warning(f"SIGACTION, Ignoring changing signal handler for signal {signum}")
        return 0

    def sys_rt_sigprocmask(self, cpu, how, newset, oldset):
        """Wrapper for sys_sigprocmask"""
        return self.sys_sigprocmask(cpu, how, newset, oldset)

    def sys_sigprocmask(self, cpu, how, newset, oldset):
        logger.warning(f"SIGACTION, Ignoring changing signal mask set cmd:%s", how)
        return 0

    def sys_dup(self, fd: int) -> int:
        """
        Duplicates an open file descriptor
        :rtype: int
        :param fd: the open file descriptor to duplicate.
        :return: the new file descriptor.
        """

        try:
            f = self._get_fdlike(fd)
        except FdError as e:
            logger.info(f"sys_dup: fd ({fd}) is not open. Returning -{errorcode(e.err)}")
            return -e.err
        return self._open(f)

    def sys_dup2(self, fd: int, newfd: int) -> int:
        """
        Duplicates an open fd to newfd. If newfd is open, it is first closed
        :param fd: the open file descriptor to duplicate.
        :param newfd: the file descriptor to alias the file described by fd.
        :return: newfd.
        """
        try:
            f = self._get_fdlike(fd)
        except FdError as e:
            logger.info("sys_dup2: fd ({fd}) is not open. Returning -{errorcode(e.err)}")
            return -e.err

        soft_max, hard_max = self._rlimits[resource.RLIMIT_NOFILE]
        if newfd >= soft_max:
            logger.info(
                f"sys_dup2: newfd ({newfd}) is above max descriptor table size ({soft_max})"
            )
            return -errno.EBADF

        if self._is_fd_open(newfd):
            self._close(newfd)

        self.fd_table.add_entry_at(f, fd)

        logger.debug("sys_dup2(%d,%d) -> %d", fd, newfd, newfd)
        return newfd

    def sys_chroot(self, path):
        """
        An implementation of chroot that does perform some basic error checking,
        but does not actually chroot.

        :param path: Path to chroot
        """
        if path not in self.current.memory:
            return -errno.EFAULT

        path_s = self.current.read_string(path)
        if not os.path.exists(path_s):
            return -errno.ENOENT

        if not os.path.isdir(path_s):
            return -errno.ENOTDIR

        return -errno.EPERM

    def sys_close(self, fd: int) -> int:
        """
        Closes a file descriptor
        :rtype: int
        :param fd: the file descriptor to close.
        :return: C{0} on success.
        """
        if not self._is_fd_open(fd):
            return -errno.EBADF
        self._close(fd)
        logger.debug(f"sys_close({fd})")
        return 0

    def sys_readlink(self, path, buf, bufsize):
        """
        Read the value of a symbolic link.
        :rtype: int

        :param path: symbolic link.
        :param buf: destination buffer.
        :param bufsize: size to read.
        :return: number of bytes placed in buffer on success, -errno on error.

        :todo: return -errno on error.
        """
        if bufsize <= 0:
            return -errno.EINVAL
        filename = self.current.read_string(path)
        if filename == "/proc/self/exe":
            data = os.path.abspath(self.program)
        else:
            data = os.readlink(filename)[:bufsize]
        self.current.write_bytes(buf, data)
        # XXX: Return an appropriate value on error.
        return len(data)

    def sys_readlinkat(self, dir_fd, path, buf, bufsize):
        """
        Read the value of a symbolic link relative to a directory file descriptor.
        :rtype: int

        :param dir_fd: directory file descriptor.
        :param path: symbolic link.
        :param buf: destination buffer.
        :param bufsize: size to read.
        :return: number of bytes placed in buffer on success, -errno on error.

        :todo: return -errno on error, full 'dir_fd' support.
        """
        _path = self.current.read_string(path)
        _dir_fd = ctypes.c_int32(dir_fd).value

        if not (os.path.isabs(_path) or _dir_fd == self.FCNTL_FDCWD):
            raise NotImplementedError("Only absolute paths or paths relative to CWD are supported")

        # XXX: Use 'dir_fd'.
        # XXX: Return an appropriate value on error.
        return self.sys_readlink(path, buf, bufsize)

    def sys_mmap_pgoff(self, address, size, prot, flags, fd, offset):
        """Wrapper for mmap2"""
        return self.sys_mmap2(address, size, prot, flags, fd, offset)

    def sys_mmap2(self, address, size, prot, flags, fd, offset):
        """
        Creates a new mapping in the virtual address space of the calling process.
        :rtype: int
        :param address: the starting address for the new mapping. This address is used as hint unless the
                        flag contains C{MAP_FIXED}.
        :param size: the length of the mapping.
        :param prot: the desired memory protection of the mapping.
        :param flags: determines whether updates to the mapping are visible to other
                      processes mapping the same region, and whether updates are carried
                      through to the underlying file.
        :param fd: the contents of a file mapping are initialized using C{size} bytes starting at
                   offset C{offset} in the file referred to by the file descriptor C{fd}.
        :param offset: the contents of a file mapping are initialized using C{size} bytes starting at
                       offset C{offset}*0x1000 in the file referred to by the file descriptor C{fd}.
        :return:
            - C{-1} In case you use C{MAP_FIXED} in the flags and the mapping can not be place at the desired address.
            - the address of the new mapping.
        """
        return self.sys_mmap(address, size, prot, flags, fd, offset * 0x1000)

    def sys_mmap(self, address, size, prot, flags, fd, offset):
        """
        Creates a new mapping in the virtual address space of the calling process.
        :rtype: int

        :param address: the starting address for the new mapping. This address is used as hint unless the
                        flag contains C{MAP_FIXED}.
        :param size: the length of the mapping.
        :param prot: the desired memory protection of the mapping.
        :param flags: determines whether updates to the mapping are visible to other
                      processes mapping the same region, and whether updates are carried
                      through to the underlying file.
        :param fd: the contents of a file mapping are initialized using C{size} bytes starting at
                   offset C{offset} in the file referred to by the file descriptor C{fd}.
        :param offset: the contents of a file mapping are initialized using C{size} bytes starting at
                       offset C{offset} in the file referred to by the file descriptor C{fd}.
        :return:
                - C{-1} in case you use C{MAP_FIXED} in the flags and the mapping can not be place at the desired address.
                - the address of the new mapping (that must be the same as address in case you included C{MAP_FIXED} in flags).
        :todo: handle exception.
        """

        if address == 0:
            address = None

        cpu = self.current
        if flags & 0x10:
            cpu.memory.munmap(address, size)

        perms = perms_from_protflags(prot)

        if flags & 0x20:
            result = cpu.memory.mmap(address, size, perms)
        elif fd == 0:
            assert offset == 0
            result = cpu.memory.mmap(address, size, perms)
            try:
                data = self.fd_table.get_fdlike(fd).read(size)
            except FdError as e:
                return -1
            cpu.write_bytes(result, data)
        else:
            # FIXME Check if file should be symbolic input and do as with fd0
            f = self.fd_table.get_fdlike(fd)
            result = cpu.memory.mmapFile(address, size, perms, f.name, offset)

        actually_mapped = f"0x{result:016x}"
        if address is None or result != address:
            address = address or 0
            actually_mapped += f" [requested: 0x{address:016x}]"

        if flags & 0x10 != 0 and result != address:
            cpu.memory.munmap(result, size)
            result = -1

        return result

    def sys_mprotect(self, start, size, prot):
        """
        Sets protection on a region of memory. Changes protection for the calling process's
        memory page(s) containing any part of the address range in the interval [C{start}, C{start}+C{size}-1].
        :rtype: int

        :param start: the starting address to change the permissions.
        :param size: the size of the portion of memory to change the permissions.
        :param prot: the new access permission for the memory.
        :return: C{0} on success.
        """
        perms = perms_from_protflags(prot)
        ret = self.current.memory.mprotect(start, size, perms)
        return 0

    def sys_munmap(self, addr, size):
        """
        Unmaps a file from memory. It deletes the mappings for the specified address range
        :rtype: int

        :param addr: the starting address to unmap.
        :param size: the size of the portion to unmap.
        :return: C{0} on success.
        """
        if issymbolic(addr):
            raise ConcretizeArgument(self, 0)
        if issymbolic(size):
            raise ConcretizeArgument(self, 1)
        self.current.memory.munmap(addr, size)
        return 0

    def sys_getuid(self):
        """
        Gets user identity.
        :rtype: int

        :return: this call returns C{1000} for all the users.
        """
        return 1000

    def sys_getgid(self):
        """
        Gets group identity.
        :rtype: int

        :return: this call returns C{1000} for all the groups.
        """
        return 1000

    def sys_geteuid(self):
        """
        Gets user identity.
        :rtype: int

        :return: This call returns C{1000} for all the users.
        """
        return 1000

    def sys_getegid(self):
        """
        Gets group identity.
        :rtype: int

        :return: this call returns C{1000} for all the groups.
        """
        return 1000

    def sys_readv(self, fd, iov, count) -> int:
        """
        Works just like C{sys_read} except that data is read into multiple buffers.
        :rtype: int

        :param fd: the file descriptor of the file to read.
        :param iov: the buffer where the the bytes to read are stored.
        :param count: amount of C{iov} buffers to read from the file.
        :return: the amount of bytes read in total.
        """
        cpu = self.current
        ptrsize = cpu.address_bit_size
        sizeof_iovec = 2 * (ptrsize // 8)
        total = 0
        for i in range(0, count):
            buf = cpu.read_int(iov + i * sizeof_iovec, ptrsize)
            size = cpu.read_int(iov + i * sizeof_iovec + (sizeof_iovec // 2), ptrsize)

            try:
                data = self.fd_table.get_fdlike(fd).read(size)
            except FdError as e:
                return -e.err
            total += len(data)
            cpu.write_bytes(buf, data)
            self.syscall_trace.append(("_read", fd, data))
        return total

    def sys_writev(self, fd, iov, count):
        """
        Works just like C{sys_write} except that multiple buffers are written out.
        :rtype: int

        :param fd: the file descriptor of the file to write.
        :param iov: the buffer where the the bytes to write are taken.
        :param count: amount of C{iov} buffers to write into the file.
        :return: the amount of bytes written in total.
        """
        cpu = self.current
        ptrsize = cpu.address_bit_size
        sizeof_iovec = 2 * (ptrsize // 8)
        total = 0
        try:
            write_fd = self._get_fdlike(fd)
        except FdError as e:
            logger.error(f"writev: Not a valid file descriptor ({fd})")
            return -e.err

        for i in range(0, count):
            buf = cpu.read_int(iov + i * sizeof_iovec, ptrsize)
            size = cpu.read_int(iov + i * sizeof_iovec + (sizeof_iovec // 2), ptrsize)

            if issymbolic(size):
                size = SelectedSolver.instance().get_value(self.constraints, size)

            data = [Operators.CHR(cpu.read_int(buf + i, 8)) for i in range(size)]
            data = self._transform_write_data(data)
            write_fd.write(data)
            self.syscall_trace.append(("_write", fd, data))
            total += size
        return total

    def sys_set_thread_area(self, user_info):
        """
        Sets a thread local storage (TLS) area. Sets the base address of the GS segment.
        :rtype: int

        :param user_info: the TLS array entry set corresponds to the value of C{u_info->entry_number}.
        :return: C{0} on success.
        """
        n = self.current.read_int(user_info, 32)
        pointer = self.current.read_int(user_info + 4, 32)
        m = self.current.read_int(user_info + 8, 32)
        flags = self.current.read_int(user_info + 12, 32)
        assert n == 0xFFFFFFFF
        assert flags == 0x51  # TODO: fix
        self.current.GS = 0x63
        self.current.set_descriptor(self.current.GS, pointer, 0x4000, "rw")
        self.current.write_int(user_info, (0x63 - 3) // 8, 32)
        return 0

    def sys_getpriority(self, which, who):
        """
        System call ignored.
        :rtype: int

        :return: C{0}
        """
        logger.warning("Unimplemented system call: sys_get_priority")
        return 0

    def sys_setpriority(self, which, who, prio):
        """
        System call ignored.
        :rtype: int

        :return: C{0}
        """
        logger.warning("Unimplemented system call: sys_setpriority")
        return 0

    def sys_tgkill(self, tgid, pid, sig):
        logger.warning("Unimplemented system call: sys_tgkill")
        return 0

    def sys_acct(self, path):
        """
        System call not implemented.
        :rtype: int

        :return: C{-1}
        """
        logger.debug("BSD account not implemented!")
        return -1

    def sys_exit(self, error_code):
        """Wrapper for sys_exit_group"""
        return self.sys_exit_group(error_code)

    def sys_exit_group(self, error_code):
        """
        Exits all threads in a process
        :raises Exception: 'Finished'
        """
        return self._exit(f"Program finished with exit status: {ctypes.c_int32(error_code).value}")

    def sys_set_tid_address(self, tidptr):
        return 1000  # tha pid

    def sys_getrlimit(self, resource, rlim):
        ret = -1
        if resource in self._rlimits:
            rlimit_tup = self._rlimits[resource]
            # 32 bit values on both 32 and 64 bit platforms. For more info,
            # see the BUGS section in getrlimit(2) man page.
            self.current.write_bytes(rlim, struct.pack("<LL", *rlimit_tup))
            ret = 0
        return ret

    def sys_prlimit64(self, pid, resource, new_lim, old_lim):
        ret = -1
        if pid == 0:
            if old_lim:
                ret = self.sys_getrlimit(resource, old_lim)
            elif new_lim:
                ret = self.sys_setrlimit(resource, new_lim)
        else:
            logger.warning("Cowardly refusing to set resource limits for process %d", pid)
        return ret

    def sys_madvise(self, infop):
        logger.info("Ignoring sys_madvise")
        return 0

    def sys_fadvise64(self, fd: int, offset: int, length: int, advice: int) -> int:
        logger.info("Ignoring sys_fadvise64")
        return 0

    def sys_arm_fadvise64_64(self, fd: int, offset: int, length: int, advice: int) -> int:
        logger.info("Ignoring sys_arm_fadvise64_64")
        return 0

    def sys_socket(self, domain, socket_type, protocol):
        if domain != socket.AF_INET:
            return -errno.EINVAL

        if socket_type != socket.SOCK_STREAM:
            return -errno.EINVAL

        if protocol != 0:
            return -errno.EINVAL

        f = SocketDesc(domain, socket_type, protocol)
        fd = self._open(f)
        return fd

    def _is_sockfd(self, sockfd: int) -> int:
        try:
            fd = self._get_fdlike(sockfd)
            if not isinstance(fd, SocketDesc):
                return -errno.ENOTSOCK
            return 0
        except IndexError:
            return -errno.EBADF

    def sys_bind(self, sockfd: int, address, address_len) -> int:
        return self._is_sockfd(sockfd)

    def sys_listen(self, sockfd: int, backlog) -> int:
        return self._is_sockfd(sockfd)

    def sys_accept(self, sockfd: int, addr, addrlen) -> int:
        """
        https://github.com/torvalds/linux/blob/63bdf4284c38a48af21745ceb148a087b190cd21/net/socket.c#L1649-L1653
        """
        return self.sys_accept4(sockfd, addr, addrlen, 0)

    def sys_accept4(self, sockfd: int, addr, addrlen, flags) -> int:
        # TODO: ehennenfent - Only handles the flags=0 (sys_accept) case
        ret = self._is_sockfd(sockfd)
        if ret != 0:
            return ret

        sock = Socket(net=True)
        fd = self._open(sock)
        return fd

    def sys_recv(self, sockfd: int, buf: int, count: int, flags: int, trace_str="_recv") -> int:
        # act like sys_recvfrom
        return self.sys_recvfrom(sockfd, buf, count, flags, 0, 0, trace_str=trace_str)

    def sys_recvfrom(
        self,
        sockfd: int,
        buf: int,
        count: int,
        flags: int,
        src_addr: int,
        addrlen: int,
        trace_str="_recvfrom",
    ) -> int:
        if src_addr != 0:
            logger.warning("sys_recvfrom: Unimplemented non-NULL src_addr")

        if addrlen != 0:
            logger.warning("sys_recvfrom: Unimplemented non-NULL addrlen")

        if not self.current.memory.access_ok(slice(buf, buf + count), "w"):
            logger.info("RECV: buf within invalid memory. Returning -errno.EFAULT")
            return -errno.EFAULT

        try:
            sock = self._get_fdlike(sockfd)
        except FdError:
            return -errno.EBADF

        if not isinstance(sock, Socket):
            return -errno.ENOTSOCK

        data = sock.read(count)
        if len(data) == 0:
            return 0
        self.syscall_trace.append((trace_str, sockfd, data))
        self.current.write_bytes(buf, data)

        return len(data)

    def sys_send(self, sockfd, buf, count, flags) -> int:
        try:
            sock = self.fd_table.get_fdlike(sockfd)
        except FdError as e:
            return -e.err

        if not isinstance(sock, Socket):
            return -errno.ENOTSOCK

        data = self.current.read_bytes(buf, count)
        # XXX(yan): send(2) is currently a nop; we don't communicate yet
        self.syscall_trace.append(("_send", sockfd, data))

        return count

    def sys_sendfile(self, out_fd, in_fd, offset_p, count) -> int:
        if offset_p != 0:
            offset = self.current.read_int(offset_p, self.current.address_bit_size)
        else:
            offset = 0

        try:
            out_sock = self.fd_table.get_fdlike(out_fd)
            in_sock = self.fd_table.get_fdlike(in_fd)
        except FdError as e:
            return -e.err

        # XXX(yan): sendfile(2) is currently a nop; we don't communicate yet

        return count

    def sys_getrandom(self, buf, size, flags):
        """
        The getrandom system call fills the buffer with random bytes of buflen.
        The source of random (/dev/random or /dev/urandom) is decided based on
        the flags value.

        Manticore's implementation simply fills a buffer with zeroes -- choosing
        determinism over true randomness.

        :param buf: address of buffer to be filled with random bytes
        :param size: number of random bytes
        :param flags: source of random (/dev/random or /dev/urandom)
        :return: number of bytes copied to buf
        """

        GRND_NONBLOCK = 0x0001
        GRND_RANDOM = 0x0002

        if size == 0:
            return 0

        if buf not in self.current.memory:
            logger.info("getrandom: Provided an invalid address. Returning -errno.EFAULT")
            return -errno.EFAULT

        if flags & ~(GRND_NONBLOCK | GRND_RANDOM):
            return -errno.EINVAL

        self.current.write_bytes(buf, "\x00" * size)

        return size

    @unimplemented
    def sys_futex(self, uaddr, op, val, utime, uaddr2, val3) -> int:
        """
        Fast user-space locking
        success: Depends on the operation, but often 0
        error: Returns -1
        """
        return 0

    @unimplemented
    def sys_clone_ptregs(self, flags, child_stack, ptid, ctid, regs):
        """
        Create a child process
        :param flags:
        :param child_stack:
        :param ptid:
        :param ctid:
        :param regs:
        :return: The PID of the child process
        """
        return self.sys_getpid()

    # Dispatchers...
    def syscall(self):
        """
        Syscall dispatcher.
        """

        index: int = self._syscall_abi.syscall_number()
        name: Optional[str] = None

        try:
            table = getattr(linux_syscalls, self.current.machine)
            name = table.get(index, None)
            if hasattr(self, name):
                implementation = getattr(self, name)
                # If this instance does not have an implementation for the system
                # call, but the parent class does, use a partial function to do
                # some processing of the unimplemented syscall before using the
                # parent's implementation
                # '.' is class separator
                owner_class = implementation.__qualname__.rsplit(".", 1)[0]
                if owner_class != self.__class__.__name__:
                    implementation = partial(self._handle_unimplemented_syscall, implementation)
            else:
                implementation = getattr(self.stubs, name)
        except (AttributeError, KeyError):
            if name is not None:
                raise SyscallNotImplemented(index, name)
            else:
                raise EnvironmentError(f"Bad syscall index, {index}")

        return self._syscall_abi.invoke(implementation)

    def _handle_unimplemented_syscall(self, impl: Callable, *args):
        """
        Handle an unimplemented system call (for this class) in a generic way
        before calling the implementation passed to this function.

        :param impl: The real implementation
        :param args: The arguments to the implementation
        """
        return impl(*args)

    def sys_clock_gettime(self, clock_id, timespec):
        logger.warning("sys_clock_time not really implemented")
        if clock_id == 1:
            t = int(time.monotonic() * 1000000000)  # switch to monotonic_ns in py3.7
            self.current.write_bytes(
                timespec, struct.pack("L", t // 1000000000) + struct.pack("L", t)
            )
        return 0

    def sys_time(self, tloc):
        import time

        t = time.time()
        if tloc != 0:
            self.current.write_int(tloc, int(t), self.current.address_bit_size)
        return int(t)

    def sys_gettimeofday(self, tv, tz) -> int:
        """
        Get time
        success: Returns 0
        error: Returns -1
        """
        if tv != 0:
            microseconds = int(time.time() * 10 ** 6)
            self.current.write_bytes(
                tv, struct.pack("L", microseconds // (10 ** 6)) + struct.pack("L", microseconds)
            )
        if tz != 0:
            logger.warning("No support for time zones in sys_gettimeofday")
        return 0

    def sched(self) -> None:
        """ Yield CPU.
            This will choose another process from the running list and change
            current running process. May give the same cpu if only one running
            process.
        """
        if len(self.procs) > 1:
            logger.debug("SCHED:")
            logger.debug(f"\tProcess: {self.procs!r}")
            logger.debug(f"\tRunning: {self.running!r}")
            logger.debug(f"\tTimers: {self.timers!r}")
            logger.debug(f"\tCurrent clock: {self.clocks}")
            logger.debug(f"\tCurrent cpu: {self._current}")

        if len(self.running) == 0:
            logger.debug("None running checking if there is some process waiting for a timeout")
            if all([x is None for x in self.timers]):
                raise Deadlock()
            self.clocks = min(x for x in self.timers if x is not None) + 1
            self.check_timers()
            assert len(self.running) != 0, "DEADLOCK!"
            self._current = self.running[0]
            return
        assert self._current is not None
        next_index = (self.running.index(self._current) + 1) % len(self.running)
        next_running_idx = self.running[next_index]
        if len(self.procs) > 1:
            logger.debug(f"\tTransfer control from process {self._current} to {next_running_idx}")
        self._current = next_running_idx

    def wait(self, readfds, writefds, timeout) -> None:
        """ Wait for file descriptors or timeout.
            Adds the current process in the correspondent waiting list and
            yield the cpu to another running process.
        """
        logger.debug("WAIT:")
        logger.debug(
            f"\tProcess {self._current} is going to wait for [ {readfds!r} {writefds!r} {timeout!r} ]"
        )
        logger.debug(f"\tProcess: {self.procs!r}")
        logger.debug(f"\tRunning: {self.running!r}")
        logger.debug(f"\tTimers: {self.timers!r}")

        assert self._current is not None

        for fd in readfds:
            self.fd_table.get_rwaiters(fd).add(self._current)
        for fd in writefds:
            self.fd_table.get_twaiters(fd).add(self._current)
        if timeout is not None:
            self.timers[self._current] = self.clocks + timeout
        procid = self._current
        # self.sched()
        next_index = (self.running.index(procid) + 1) % len(self.running)
        self._current = self.running[next_index]
        logger.debug(f"\tTransfer control from process {procid} to {self._current}")
        logger.debug(f"\tREMOVING {procid!r} from {self.running!r}. Current: {self._current!r}")
        self.running.remove(procid)
        if self._current not in self.running:
            logger.debug("\tCurrent not running. Checking for timers...")
            self._current = None
            self.check_timers()

    def awake(self, procid) -> None:
        """ Remove procid from waitlists and reestablish it in the running list """
        logger.debug(
            f"Remove procid:{procid} from waitlists and reestablish it in the running list"
        )
        for entry in self.fd_table.entries():
            entry.rwaiters.discard(procid)
            entry.twaiters.discard(procid)
        self.timers[procid] = None
        self.running.append(procid)
        if self._current is None:
            self._current = procid

    def connections(self, fd: int) -> Optional[int]:
        """ File descriptors are connected to each other like pipes, except
        for 0, 1, and 2. If you write to FD(N) for N >=3, then that comes
        out from FD(N+1) and vice-versa
        """
        if fd in [0, 1, 2]:
            return None
        if fd % 2:
            return fd + 1
        else:
            return fd - 1

    def signal_receive(self, fd: int) -> None:
        """ Awake one process waiting to receive data on fd """
        connections = self.connections
        connection = connections(fd)
        if connection:
            procs = self.fd_table.get_twaiters(connection)
            if procs:
                procid = random.sample(procs, 1)[0]
                self.awake(procid)

    def signal_transmit(self, fd: int) -> None:
        """ Awake one process waiting to transmit data on fd """
        connection = self.connections(fd)
        if connection is None or not self.fd_table.has_entry(connection):
            return

        procs = self.fd_table.get_rwaiters(connection)
        if procs:
            procid = random.sample(procs, 1)[0]
            self.awake(procid)

    def check_timers(self) -> None:
        """ Awake process if timer has expired """
        if self._current is None:
            # Advance the clocks. Go to future!!
            advance = min([self.clocks] + [x for x in self.timers if x is not None]) + 1
            logger.debug(f"Advancing the clock from {self.clocks} to {advance}")
            self.clocks = advance
        for procid, timer in enumerate(self.timers):
            if timer is not None:
                if self.clocks > timer:
                    self.procs[procid].PC += self.procs[procid].instruction.size
                    self.awake(procid)

    def execute(self):
        """
        Execute one cpu instruction in the current thread (only one supported).
        :rtype: bool
        :return: C{True}

        :todo: This is where we could implement a simple schedule.
        """
        try:
            self.current.execute()
            self.clocks += 1
            if self.clocks % 10000 == 0:
                self.check_timers()
                self.sched()
        except (Interruption, Syscall) as e:
            try:
                self.syscall()
                if hasattr(e, "on_handled"):
                    e.on_handled()
            except RestartSyscall:
                pass

        return True

    # 64bit syscalls

    def sys_newfstat(self, fd, buf):
        """
        Determines information about a file based on its file descriptor.
        :rtype: int
        :param fd: the file descriptor of the file that is being inquired.
        :param buf: a buffer where data about the file will be stored.
        :return: C{0} on success, EBADF when called with bad fd
        """

        try:
            stat = self._get_fdlike(fd).stat()
        except FdError as e:
            logger.info(f"sys_newfstat: invalid fd ({fd}), returning -{errorcode(e.err)}")
            return -e.err

        def add(width, val):
            fformat = {2: "H", 4: "L", 8: "Q"}[width]
            return struct.pack("<" + fformat, val)

        def to_timespec(width, ts):
            "Note: this is a platform-dependent timespec (8 or 16 bytes)"
            return add(width, int(ts)) + add(width, int(ts % 1 * 1e9))

        # From linux/arch/x86/include/uapi/asm/stat.h
        # Numerous fields are native width-wide
        nw = self.current.address_bit_size // 8

        bufstat = add(nw, stat.st_dev)  # long st_dev
        bufstat += add(nw, stat.st_ino)  # long st_ino
        bufstat += add(nw, stat.st_nlink)  # long st_nlink
        bufstat += add(4, stat.st_mode)  # 32 mode
        bufstat += add(4, stat.st_uid)  # 32 uid
        bufstat += add(4, stat.st_gid)  # 32 gid
        bufstat += add(4, 0)  # 32 _pad
        bufstat += add(nw, stat.st_rdev)  # long st_rdev
        bufstat += add(nw, stat.st_size)  # long st_size
        bufstat += add(nw, stat.st_blksize)  # long st_blksize
        bufstat += add(nw, stat.st_blocks)  # long st_blocks
        bufstat += to_timespec(nw, stat.st_atime)  # long   st_atime, nsec;
        bufstat += to_timespec(nw, stat.st_mtime)  # long   st_mtime, nsec;
        bufstat += to_timespec(nw, stat.st_ctime)  # long   st_ctime, nsec;

        self.current.write_bytes(buf, bufstat)
        return 0

    def sys_fstat(self, fd, buf):
        """
        Determines information about a file based on its file descriptor.
        :rtype: int
        :param fd: the file descriptor of the file that is being inquired.
        :param buf: a buffer where data about the file will be stored.
        :return: C{0} on success, EBADF when called with bad fd
        """

        try:
            stat = self._get_fdlike(fd).stat()
        except FdError as e:
            logger.info(f"sys_fstat: invalid fd ({fd}), returning -{errorcode(e.err)}")
            return -e.err

        def add(width, val):
            fformat = {2: "H", 4: "L", 8: "Q"}[width]
            return struct.pack("<" + fformat, val)

        def to_timespec(ts):
            return struct.pack("<LL", int(ts), int(ts % 1 * 1e9))

        bufstat = add(8, stat.st_dev)  # dev_t st_dev;
        bufstat += add(4, 0)  # __pad1
        bufstat += add(4, stat.st_ino)  # unsigned long  st_ino;
        bufstat += add(4, stat.st_mode)  # unsigned short st_mode;
        bufstat += add(4, stat.st_nlink)  # unsigned short st_nlink;
        bufstat += add(4, stat.st_uid)  # unsigned short st_uid;
        bufstat += add(4, stat.st_gid)  # unsigned short st_gid;
        bufstat += add(4, stat.st_rdev)  # unsigned long  st_rdev;
        bufstat += add(4, stat.st_size)  # unsigned long  st_size;
        bufstat += add(4, stat.st_blksize)  # unsigned long  st_blksize;
        bufstat += add(4, stat.st_blocks)  # unsigned long  st_blocks;
        bufstat += to_timespec(stat.st_atime)  # unsigned long  st_atime;
        bufstat += to_timespec(stat.st_mtime)  # unsigned long  st_mtime;
        bufstat += to_timespec(stat.st_ctime)  # unsigned long  st_ctime;
        bufstat += add(4, 0)  # unsigned long  __unused4;
        bufstat += add(4, 0)  # unsigned long  __unused5;

        self.current.write_bytes(buf, bufstat)
        return 0

    def sys_fstat64(self, fd, buf):
        """
        Determines information about a file based on its file descriptor (for Linux 64 bits).
        :rtype: int
        :param fd: the file descriptor of the file that is being inquired.
        :param buf: a buffer where data about the file will be stored.
        :return: C{0} on success, EBADF when called with bad fd
        :todo: Fix device number.
        """

        try:
            stat = self._get_fdlike(fd).stat()
        except FdError as e:
            logger.info(f"sys_fstat64: invalid fd ({fd}), returning -{errorcode(e.err)}")
            return -e.err

        def add(width, val):
            fformat = {2: "H", 4: "L", 8: "Q"}[width]
            return struct.pack("<" + fformat, val)

        def to_timespec(ts):
            return struct.pack("<LL", int(ts), int(ts % 1 * 1e9))

        bufstat = add(8, stat.st_dev)  # unsigned long long      st_dev;
        bufstat += add(8, stat.st_ino)  # unsigned long long   __st_ino;
        bufstat += add(4, stat.st_mode)  # unsigned int    st_mode;
        bufstat += add(4, stat.st_nlink)  # unsigned int    st_nlink;
        bufstat += add(4, stat.st_uid)  # unsigned long   st_uid;
        bufstat += add(4, stat.st_gid)  # unsigned long   st_gid;
        bufstat += add(8, stat.st_rdev)  # unsigned long long st_rdev;
        bufstat += add(4, 0)  # unsigned long long __pad1;
        bufstat += add(8, stat.st_size)  # long long       st_size;
        bufstat += add(4, stat.st_blksize)  # int   st_blksize;
        # bufstat += add(4, 0)  # int   __pad2;
        bufstat += add(8, stat.st_blocks)  # unsigned long long st_blocks;
        bufstat += to_timespec(stat.st_atime)  # unsigned long   st_atime;
        bufstat += to_timespec(stat.st_mtime)  # unsigned long   st_mtime;
        bufstat += to_timespec(stat.st_ctime)  # unsigned long   st_ctime;
        bufstat += add(4, 0)  # unsigned int __unused4;
        bufstat += add(4, 0)  # unsigned int __unused5;

        self.current.write_bytes(buf, bufstat)
        return 0

    def sys_newstat(self, fd, buf):
        """
        Wrapper for stat64()
        """
        return self.sys_stat64(fd, buf)

    def sys_stat64(self, path, buf):
        """
        Determines information about a file based on its filename (for Linux 64 bits).
        :rtype: int
        :param path: the pathname of the file that is being inquired.
        :param buf: a buffer where data about the file will be stored.
        :return: C{0} on success.
        """
        return self._stat(path, buf, True)

    def sys_stat32(self, path, buf):
        return self._stat(path, buf, False)

    def _stat(self, path, buf, is64bit):
        fd = self.sys_open(path, 0, "r")
        if is64bit:
            ret = self.sys_fstat64(fd, buf)
        else:
            ret = self.sys_fstat(fd, buf)
        self.sys_close(fd)
        return ret

    def sys_mkdir(self, pathname, mode) -> int:
        """
        Creates a directory
        :return 0 on success
        """
        name = self.current.read_string(pathname)
        try:
            os.mkdir(name, mode=mode)
        except OSError as e:
            return -e.errno

        return 0

    def sys_rmdir(self, pathname) -> int:
        """
        Deletes a directory
        :return 0 on success
        """
        name = self.current.read_string(pathname)
        try:
            os.rmdir(name)
        except OSError as e:
            return -e.errno

        return -1

    def sys_pipe(self, filedes) -> int:
        """
        Wrapper for pipe2(filedes, 0)
        """
        return self.sys_pipe2(filedes, 0)

    def sys_pipe2(self, filedes, flags) -> int:
        """
        # TODO (ehennenfent) create a native pipe type instead of cheating with sockets
        Create pipe
        :return 0 on success
        """
        if flags == 0:
            l, r = Socket.pair()
            self.current.write_int(filedes, self._open(l))
            self.current.write_int(filedes + 4, self._open(r))
            return 0
        else:
            logger.warning("sys_pipe2 doesn't handle flags")
            return -1

    def sys_ftruncate(self, fd, length) -> int:
        """
        Truncate a file to <length>
        :return 0 on success
        """
        try:
            f = self._get_fdlike(fd)
        except FdError as e:
            return -e.err
        except OSError as e:
            return -e.errno
        if isinstance(f, Directory):
            return -errno.EISDIR
        if not isinstance(f, File):
            return -errno.EINVAL
        f.file.truncate(length)
        return 0

    def sys_link(self, oldname, newname) -> int:
        """
        Create a symlink from oldname to newname.
        :return 0 on success
        """
        oldname = self.current.read_string(oldname)
        newname = self.current.read_string(newname)
        try:
            os.link(oldname, newname)
        except OSError as e:
            return -e.errno
        return 0

    def sys_unlink(self, pathname) -> int:
        """
        Delete a symlink.
        :return 0 on success
        """
        pathname = self.current.read_string(pathname)
        try:
            os.unlink(pathname)
        except OSError as e:
            return -e.errno
        return 0

    def sys_getdents(self, fd, dirent, count) -> int:
        """
        Fill memory with directory entry structs
        return: The number of bytes read or 0 at the end of the directory
        """
        buf = b""
        try:
            file = self._get_fdlike(fd)
        except FdError as e:
            return -e.err
        if not isinstance(file, Directory):
            logger.info("Can't get directory entries for a file")
            return -1

        if fd not in self._getdents_c:
            # First call on this file descriptor
            self._getdents_c[fd] = os.scandir(file.path)

        dent_iter = self._getdents_c[fd]

        item = next(dent_iter, None)
        while item is not None:
            fmt = f"LLH{len(item.name) + 1}sB"
            size = struct.calcsize(fmt)
            if len(buf) + size > count:
                # Don't overflow buffer
                break

            try:
                stat = item.stat()
            except FdError as e:
                return -e.err

            # https://elixir.bootlin.com/linux/v5.1.15/source/include/linux/fs_types.h#L27
            d_type = (stat.st_mode >> 12) & 15

            packed = struct.pack(
                fmt, item.inode(), size, size, bytes(item.name, "utf-8") + b"\x00", d_type
            )
            buf += packed
            item = next(dent_iter, None)

        if item:
            # Prepend the last valid item that didn't fit to the list for next time
            self._getdents_c[fd] = chain([item], dent_iter)
        else:
            # If everything fit, then save just the dent_iter
            self._getdents_c[fd] = dent_iter

        if len(buf) > 0:
            # Write out to buffer if we have something to write
            self.current.write_bytes(dirent, buf)
        else:  # len(buf) == 0
            # When the buffer is 0, that means we've read all directory entries
            # Delete the state and don't write a zero buffer back to dirent
            del self._getdents_c[fd]

        return len(buf)

    def sys_nanosleep(self, rqtp, rmtp) -> int:
        """
        Ignored
        """
        logger.info("Ignoring call to sys_nanosleep")
        return 0

    def sys_chmod(self, filename, mode) -> int:
        """
        Modify file permissions
        :return 0 on success
        """
        filename = self.current.read_string(filename)
        try:
            os.chmod(filename, mode)
        except OSError as e:
            return -e.errno

        return 0

    def sys_chown(self, filename, user, group) -> int:
        """
        Modify file ownership
        :return 0 on success
        """
        filename = self.current.read_string(filename)
        try:
            os.chown(filename, user, group)
        except OSError as e:
            return -e.errno

        return 0

    def _arch_specific_init(self):
        assert self.arch in {"i386", "amd64", "armv7", "aarch64"}

        if self.arch == "i386":
            self._uname_machine = "i386"
        elif self.arch == "amd64":
            self._uname_machine = "x86_64"
        elif self.arch == "armv7":
            self._uname_machine = "armv71"
            self._init_arm_kernel_helpers()
            self.current._set_mode_by_val(self.current.PC)
            self.current.PC &= ~1
        elif self.arch == "aarch64":
            # XXX: Possible values: 'aarch64_be', 'aarch64', 'armv8b', 'armv8l'.
            # See 'UTS_MACHINE' and 'COMPAT_UTS_MACHINE' in the Linux kernel source.
            # https://stackoverflow.com/a/45125525
            self._uname_machine = "aarch64"

        # Establish segment registers for x86 architectures
        if self.arch in {"i386", "amd64"}:
            x86_defaults = {"CS": 0x23, "SS": 0x2B, "DS": 0x2B, "ES": 0x2B}
            for reg, val in x86_defaults.items():
                self.current.regfile.write(reg, val)

    @staticmethod
    def _interp_total_size(interp):
        """
        Compute total load size of interpreter.

        :param ELFFile interp: interpreter ELF .so
        :return: total load size of interpreter, not aligned
        :rtype: int
        """
        load_segs = [x for x in interp.iter_segments() if x.header.p_type == "PT_LOAD"]
        last = load_segs[-1]
        return last.header.p_vaddr + last.header.p_memsz


############################################################################
# Symbolic versions follows


class SLinux(Linux):
    """
    Builds a symbolic extension of a Linux OS

    :param str programs: path to ELF binary
    :param str disasm: disassembler to be used
    :param list argv: argv not including binary
    :param list envp: environment variables
    :param tuple[str] symbolic_files: files to consider symbolic
    """

    def __init__(
        self,
        programs,
        argv=None,
        envp=None,
        symbolic_files=None,
        disasm="capstone",
        pure_symbolic=False,
    ):
        argv = [] if argv is None else argv
        envp = [] if envp is None else envp
        symbolic_files = [] if symbolic_files is None else symbolic_files

        self._constraints = ConstraintSet()
        self._pure_symbolic = pure_symbolic
        self.random = 0
        self.symbolic_files = symbolic_files
        # Keep track of number of accepted symbolic sockets
        self.net_accepts = 0
        super().__init__(programs, argv=argv, envp=envp, disasm=disasm)

    def _mk_proc(self, arch):
        if arch in {"i386", "armv7"}:
            if self._pure_symbolic:
                mem = LazySMemory32(self.constraints)
            else:
                mem = SMemory32(self.constraints)
        else:
            if self._pure_symbolic:
                mem = LazySMemory64(self.constraints)
            else:
                mem = SMemory64(self.constraints)

        cpu = CpuFactory.get_cpu(mem, arch)
        return cpu

    def add_symbolic_file(self, symbolic_file):
        """
        Add a symbolic file. Each '+' in the file will be considered
        as symbolic; other chars are concretized.
        Symbolic files must have been defined before the call to `run()`.

        :param str symbolic_file: the name of the symbolic file
        """
        self.symbolic_files.append(symbolic_file)

    @property
    def constraints(self):
        return self._constraints

    @constraints.setter
    def constraints(self, constraints):
        self._constraints = constraints
        for proc in self.procs:
            proc.memory.constraints = constraints

    # marshaling/pickle
    def __getstate__(self):
        state = super().__getstate__()
        state["constraints"] = self.constraints
        state["random"] = self.random
        state["symbolic_files"] = self.symbolic_files
        state["net_accepts"] = self.net_accepts
        return state

    def __setstate__(self, state):
        self._constraints = state["constraints"]
        self.random = state["random"]
        self.symbolic_files = state["symbolic_files"]
        self.net_accepts = state["net_accepts"]
        super().__setstate__(state)
        # Add constraints to symbolic sockets
        for fd_entry in self.fd_table.entries():
            symb_socket_entry = fd_entry.fdlike
            if isinstance(symb_socket_entry, SymbolicSocket):
                symb_socket_entry._constraints = self.constraints

    def _sys_open_get_file(self, filename: str, flags: int) -> FdLike:
        if filename in self.symbolic_files:
            logger.debug(f"{filename} file is considered symbolic")
            return SymbolicFile(self.constraints, filename, flags)
        else:
            return super()._sys_open_get_file(filename, flags)

    def _transform_write_data(self, data: MixedSymbolicBuffer) -> bytes:
        bytes_concretized: int = 0
        concrete_data: bytes = bytes()
        for c in data:
            if issymbolic(c):
                bytes_concretized += 1
                c = bytes([SelectedSolver.instance().get_value(self.constraints, c)])
            concrete_data += cast(bytes, c)

        if bytes_concretized > 0:
            logger.debug(f"Concretized {bytes_concretized} written bytes.")

        return super()._transform_write_data(concrete_data)

    # Dispatchers...

    def _handle_unimplemented_syscall(self, impl: Callable, *args):
        """
        Handle all unimplemented syscalls that could have symbolic arguments.

        If a system call has symbolic argument values and there is no
        specially implemented function to handle them, then just concretize
        all symbolic arguments and call impl with args.

        :param name: Name of the system call
        :param args: Arguments for the system call
        """
        for i, arg in enumerate(args):
            if issymbolic(arg):
                logger.debug(
                    f"Unimplemented symbolic argument to {impl.__name__}. Concretizing argument {i}"
                )
                raise ConcretizeArgument(self, i)

        # Call the concrete Linux implementation
        return impl(*args)

    def sys_exit_group(self, error_code):
        if issymbolic(error_code):
            error_code = SelectedSolver.instance().get_value(self.constraints, error_code)
            return self._exit(
                f"Program finished with exit status: {ctypes.c_int32(error_code).value} (*)"
            )
        else:
            return super().sys_exit_group(error_code)

    def sys_read(self, fd, buf, count):
        if issymbolic(fd):
            logger.debug("Ask to read from a symbolic file descriptor!!")
            raise ConcretizeArgument(self, 0)

        if issymbolic(buf):
            logger.debug("Ask to read to a symbolic buffer")
            raise ConcretizeArgument(self, 1)

        if issymbolic(count):
            logger.debug("Ask to read a symbolic number of bytes ")
            raise ConcretizeArgument(self, 2)

        assert not issymbolic(fd)
        assert not issymbolic(buf)
        assert not issymbolic(count)
        return super().sys_read(fd, buf, count)

    def sys_write(self, fd, buf, count):
        if issymbolic(fd):
            logger.debug("Ask to write to a symbolic file descriptor!!")
            raise ConcretizeArgument(self, 0)

        if issymbolic(buf):
            logger.debug("Ask to write to a symbolic buffer")
            raise ConcretizeArgument(self, 1)

        if issymbolic(count):
            logger.debug("Ask to write a symbolic number of bytes ")
            raise ConcretizeArgument(self, 2)

        return super().sys_write(fd, buf, count)

    def sys_recv(self, sockfd, buf, count, flags, trace_str="_recv"):
        if issymbolic(sockfd):
            logger.debug("Ask to read from a symbolic file descriptor!!")
            raise ConcretizeArgument(self, 0)

        if issymbolic(buf):
            logger.debug("Ask to read to a symbolic buffer")
            raise ConcretizeArgument(self, 1)

        if issymbolic(count):
            logger.debug("Ask to read a symbolic number of bytes ")
            raise ConcretizeArgument(self, 2)

        if issymbolic(flags):
            logger.debug("Submitted a symbolic flags")
            raise ConcretizeArgument(self, 3)

        return self.sys_recvfrom(sockfd, buf, count, flags, 0, 0, trace_str)

    def sys_recvfrom(
        self,
        sockfd: Union[int, Expression],
        buf: Union[int, Expression],
        count: Union[int, Expression],
        flags: Union[int, Expression],
        src_addr: Union[int, Expression],
        addrlen: Union[int, Expression],
        trace_str: str = "_recvfrom",
    ):
        if issymbolic(sockfd):
            logger.debug("Ask to recvfrom a symbolic file descriptor!!")
            raise ConcretizeArgument(self, 0)

        if issymbolic(buf):
            logger.debug("Ask to recvfrom to a symbolic buffer")
            raise ConcretizeArgument(self, 1)

        if issymbolic(count):
            logger.debug("Ask to recvfrom a symbolic number of bytes ")
            raise ConcretizeArgument(self, 2)

        if issymbolic(flags):
            logger.debug("Ask to recvfrom with symbolic flags")
            raise ConcretizeArgument(self, 3)

        if issymbolic(src_addr):
            logger.debug("Ask to recvfrom with symbolic source address")
            raise ConcretizeArgument(self, 4)

        if issymbolic(addrlen):
            logger.debug("Ask to recvfrom with symbolic address length")
            raise ConcretizeArgument(self, 5)

        # mypy doesn't know issymbolic works like `isinstance`
        assert isinstance(sockfd, int)
        assert isinstance(buf, int)
        assert isinstance(count, int)
        assert isinstance(flags, int)
        assert isinstance(src_addr, int)
        assert isinstance(addrlen, int)

        return super().sys_recvfrom(sockfd, buf, count, flags, src_addr, addrlen, trace_str)

    def sys_accept(self, sockfd, addr, addrlen):
        if issymbolic(sockfd):
            logger.debug("Symbolic sockfd")
            raise ConcretizeArgument(self, 0)

        if issymbolic(addr):
            logger.debug("Symbolic address")
            raise ConcretizeArgument(self, 1)

        if issymbolic(addrlen):
            logger.debug("Symbolic address length")
            raise ConcretizeArgument(self, 2)

        ret = self._is_sockfd(sockfd)
        if ret != 0:
            return ret

        # TODO: maybe combine name with addr?
        sock = SymbolicSocket(self.constraints, f"SymbSocket_{self.net_accepts}", net=True)
        self.net_accepts += 1
        fd = self._open(sock)
        sock.fd = fd
        return fd
        # TODO: Make a concrete connection actually an option
        # return super().sys_accept(sockfd, addr, addrlen)

    def sys_open(self, buf: int, flags: int, mode: Optional[int]) -> int:
        """
        A version of open(2) that includes a special case for a symbolic path.
        When given a symbolic path, it will create a temporary file with
        64 bytes of symbolic bytes as contents and return that instead.

        :param buf: address of zero-terminated pathname
        :param flags: file access bits
        :param mode: file permission mode
        """
        offset = 0
        symbolic_path = issymbolic(self.current.read_int(buf, 8))
        if symbolic_path:
            fd, path = tempfile.mkstemp()
            with open(path, "wb+") as f:
                f.write(b"+" * 64)
            self.symbolic_files.append(path)
            buf = self.current.memory.mmap(None, 1024, "rw ", data_init=path)

        rv = super().sys_open(buf, flags, mode)

        if symbolic_path:
            self.current.memory.munmap(buf, 1024)

        return rv

    def sys_openat(self, dirfd, buf, flags: int, mode: int) -> int:
        """
        A version of openat that includes a symbolic path and symbolic directory file descriptor

        :param dirfd: directory file descriptor
        :param buf: address of zero-terminated pathname
        :param flags: file access bits
        :param mode: file permission mode
        """

        if issymbolic(dirfd):
            logger.debug("Ask to read from a symbolic directory file descriptor!!")
            # Constrain to a valid fd and one past the end of fds
            self.constraints.add(dirfd >= 0)
            self.constraints.add(dirfd <= (self.fd_table.max_fd() or 0) + 1)
            raise ConcretizeArgument(self, 0)

        if issymbolic(buf):
            logger.debug("Ask to read to a symbolic buffer")
            raise ConcretizeArgument(self, 1)

        return super().sys_openat(dirfd, buf, flags, mode)

    def sys_getrandom(self, buf, size, flags):
        """
        The getrandom system call fills the buffer with random bytes of buflen.
        The source of random (/dev/random or /dev/urandom) is decided based on the flags value.

        :param buf: address of buffer to be filled with random bytes
        :param size: number of random bytes
        :param flags: source of random (/dev/random or /dev/urandom)
        :return: number of bytes copied to buf
        """

        if issymbolic(buf):
            logger.debug("sys_getrandom: Asked to generate random to a symbolic buffer address")
            raise ConcretizeArgument(self, 0)

        if issymbolic(size):
            logger.debug("sys_getrandom: Asked to generate random of symbolic number of bytes")
            raise ConcretizeArgument(self, 1)

        if issymbolic(flags):
            logger.debug("sys_getrandom: Passed symbolic flags")
            raise ConcretizeArgument(self, 2)

        return super().sys_getrandom(buf, size, flags)

    def generate_workspace_files(self) -> Dict[str, Any]:
        def solve_to_fd(data, fd):
            def make_chr(c):
                if isinstance(c, int):
                    return bytes([c])
                elif isinstance(c, str):
                    return c.encode()
                return c

            try:
                for c in data:
                    if issymbolic(c):
                        c = SelectedSolver.instance().get_value(self.constraints, c)
                    fd.write(make_chr(c))
            except SolverError:
                fd.write("{SolverError}")

        out = io.BytesIO()
        inn = io.BytesIO()
        err = io.BytesIO()
        net = io.BytesIO()
        argIO = io.BytesIO()
        envIO = io.BytesIO()

        for name, fd, data in self.syscall_trace:
            if name in ("_transmit", "_write"):
                if fd == 1:
                    solve_to_fd(data, out)
                elif fd == 2:
                    solve_to_fd(data, err)
            if name in ("_recv", "_recvfrom"):
                solve_to_fd(data, net)
            if name in ("_receive", "_read") and fd == 0:
                solve_to_fd(data, inn)

        for a in self.argv:
            solve_to_fd(a, argIO)
            argIO.write(b"\n")

        for e in self.envp:
            solve_to_fd(e, envIO)
            envIO.write(b"\n")

        ret = {
            "syscalls": repr(self.syscall_trace),
            "argv": argIO.getvalue(),
            "env": envIO.getvalue(),
            "stdout": out.getvalue(),
            "stdin": inn.getvalue(),
            "stderr": err.getvalue(),
            "net": net.getvalue(),
        }
        for f in chain((e.fdlike for e in self.fd_table.entries()), self._closed_files):
            if not isinstance(f, SymbolicFile):
                continue
            fdata = io.BytesIO()
            solve_to_fd(f.array, fdata)
            ret[f.name] = fdata.getvalue()

        return ret
