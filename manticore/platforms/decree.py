from . import cgcrandom

# TODO use cpu factory
from ..native.cpu.x86 import I386Cpu
from ..native.cpu.abstractcpu import Interruption, ConcretizeRegister, ConcretizeArgument
from ..native.memory import SMemory32, Memory32
from ..core.smtlib import *
from ..core.state import TerminateState
from ..binary import CGCElf
from ..platforms.platform import Platform
import logging
import random

logger = logging.getLogger(__name__)


class RestartSyscall(Exception):
    pass


class Deadlock(Exception):
    pass


class SymbolicSyscallArgument(ConcretizeRegister):
    def __init__(self, cpu, number, message="Concretizing syscall argument", policy="SAMPLED"):
        reg_name = ["EBX", "ECX", "EDX", "ESI", "EDI", "EBP"][number]
        super().__init__(cpu, reg_name, message, policy)


class Socket:
    @staticmethod
    def pair():
        a = Socket()
        b = Socket()
        a.connect(b)
        return a, b

    def __init__(self):
        self.buffer = []  # queue os bytes
        self.peer = None

    def __repr__(self):
        return "SOCKET(%x, %r, %x)" % (hash(self), self.buffer, hash(self.peer))

    def is_connected(self):
        return self.peer is not None

    def is_empty(self):
        return len(self.buffer) == 0

    def is_full(self):
        return len(self.buffer) > 2 * 1024

    def connect(self, peer):
        assert not self.is_connected()
        assert not peer.is_connected()
        self.peer = peer
        if peer.peer is None:
            peer.peer = self

    def receive(self, size):
        rx_bytes = min(size, len(self.buffer))
        ret = []
        for i in range(rx_bytes):
            ret.append(self.buffer.pop())
        return ret

    def transmit(self, buf):
        assert self.is_connected()
        return self.peer._transmit(buf)

    def _transmit(self, buf):
        for c in buf:
            self.buffer.insert(0, c)
        return len(buf)


class Decree(Platform):
    """
    A simple Decree Operating System.
    This class emulates the most common Decree system calls
    """

    CGC_EBADF = 1
    CGC_EFAULT = 2
    CGC_EINVAL = 3
    CGC_ENOMEM = 4
    CGC_ENOSYS = 5
    CGC_EPIPE = 6
    CGC_SSIZE_MAX = 2147483647
    CGC_SIZE_MAX = 4294967295
    CGC_FD_SETSIZE = 32

    def __init__(self, programs, **kwargs):
        """
        Builds a Decree OS
        :param cpus: CPU for this platform
        :param mem: memory for this platform
        :todo: generalize for more CPUs
        :todo: fix deps?
        """
        programs = programs.split(",")
        super().__init__(path=programs[0], **kwargs)

        self.program = programs[0]
        self.clocks = 0
        self.files = []
        self.syscall_trace = []

        self.files = []
        # open standard files stdin, stdout, stderr
        logger.info("Opening file descriptors (0,1,2)")
        self.input = Socket()
        self.output = Socket()

        stdin = Socket()
        stdout = Socket()
        stderr = Socket()
        # A transmit to stdin,stdout or stderr will be directed to out
        stdin.peer = self.output
        stdout.peer = self.output
        stderr.peer = self.output
        # A receive from stdin will get data from inp
        self.input.peer = stdin
        # A receive on stdout or stderr will return no data (rx_bytes: 0)

        assert self._open(stdin) == 0
        assert self._open(stdout) == 1
        assert self._open(stderr) == 2

        # Load process and setup socketpairs
        self.procs = []
        for program in programs:
            self.procs += self.load(program)
            socka, sockb = Socket.pair()
            self._open(socka)
            self._open(sockb)

        nprocs = len(self.procs)
        nfiles = len(self.files)
        assert nprocs > 0
        self.running = list(range(nprocs))
        self._current = 0

        # Each process can wait for one timeout
        self.timers = [None] * nprocs
        # each fd has a waitlist
        self.rwait = [set() for _ in range(nfiles)]
        self.twait = [set() for _ in range(nfiles)]

        # Install event forwarders
        for proc in self.procs:
            self.forward_events_from(proc)

    @property
    def PC(self):
        return self._current, self.procs[self._current].PC

    def __deepcopy__(self, memo):
        return self

    def _mk_proc(self):
        return I386Cpu(Memory32())

    @property
    def current(self):
        return self.procs[self._current]

    def __getstate__(self):
        state = super().__getstate__()
        state["clocks"] = self.clocks
        state["input"] = self.input.buffer
        state["output"] = self.output.buffer
        state["files"] = [x.buffer for x in self.files]
        state["procs"] = self.procs
        state["current"] = self._current
        state["running"] = self.running
        state["rwait"] = self.rwait
        state["twait"] = self.twait
        state["timers"] = self.timers
        state["syscall_trace"] = self.syscall_trace
        return state

    def __setstate__(self, state):
        """
        :todo: some asserts
        :todo: fix deps? (last line)
        """
        super().__setstate__(state)
        self.input = Socket()
        self.input.buffer = state["input"]
        self.output = Socket()
        self.output.buffer = state["output"]

        self.files = []
        for buf in state["files"]:
            f = Socket()
            f.buffer = buf
            self.files.append(f)
        for fd in range(len(self.files)):
            if self.connections(fd) is not None:
                self.files[fd].peer = self.files[self.connections(fd)]

        self.files[0].peer = self.output
        self.files[1].peer = self.output
        self.files[2].peer = self.output
        self.input.peer = self.files[0]

        self.procs = state["procs"]
        self._current = state["current"]
        self.running = state["running"]
        self.rwait = state["rwait"]
        self.twait = state["twait"]
        self.timers = state["timers"]
        self.clocks = state["clocks"]

        self.syscall_trace = state["syscall_trace"]

        # Install event forwarders
        for proc in self.procs:
            self.forward_events_from(proc)

    def _read_string(self, cpu, buf):
        """
        Reads a null terminated concrete buffer form memory
        :todo: FIX. move to cpu or memory
        """
        filename = ""
        for i in range(0, 1024):
            c = Operators.CHR(cpu.read_int(buf + i, 8))
            if c == "\x00":
                break
            filename += c
        return filename

    def load(self, filename):
        """
        Loads a CGC-ELF program in memory and prepares the initial CPU state
        and the stack.

        :param filename: pathname of the file to be executed.
        """
        CGC_MIN_PAGE_SIZE = 4096
        CGC_MIN_ALIGN = CGC_MIN_PAGE_SIZE
        TASK_SIZE = 0x80000000

        def CGC_PAGESTART(_v):
            return (_v) & ~(CGC_MIN_ALIGN - 1)

        def CGC_PAGEOFFSET(_v):
            return (_v) & (CGC_MIN_ALIGN - 1)

        def CGC_PAGEALIGN(_v):
            return ((_v) + CGC_MIN_ALIGN - 1) & ~(CGC_MIN_ALIGN - 1)

        def BAD_ADDR(x):
            return (x) >= TASK_SIZE

        # load elf See https://github.com/CyberdyneNYC/linux-source-3.13.2-cgc/blob/master/fs/binfmt_cgc.c
        # read the ELF object file
        cgc = CGCElf(filename)
        logger.info("Loading %s as a %s elf" % (filename, cgc.arch))
        # make cpu and memory (Only 1 thread in Decree)
        cpu = self._mk_proc()

        bss = brk = 0
        start_code = 0xFFFFFFFF
        end_code = start_data = end_data = 0

        for (vaddr, memsz, perms, name, offset, filesz) in cgc.maps():
            if vaddr < start_code:
                start_code = vaddr
            if start_data < vaddr:
                start_data = vaddr

            if (
                vaddr > TASK_SIZE
                or filesz > memsz
                or memsz > TASK_SIZE
                or TASK_SIZE - memsz < vaddr
            ):
                raise Exception("Set_brk can never work. avoid overflows")

            # CGCMAP--
            addr = None
            if filesz > 0:
                hint = CGC_PAGESTART(vaddr)
                size = CGC_PAGEALIGN(filesz + CGC_PAGEOFFSET(vaddr))
                offset = CGC_PAGESTART(offset)
                addr = cpu.memory.mmapFile(hint, size, perms, name, offset)
                assert not BAD_ADDR(addr)

                lo = CGC_PAGEALIGN(vaddr + filesz)
                hi = CGC_PAGEALIGN(vaddr + memsz)
            else:
                # for 0 filesz, we have to include the first page as bss.
                lo = CGC_PAGESTART(vaddr + filesz)
                hi = CGC_PAGEALIGN(vaddr + memsz)

            # map anon pages for the rest (no prefault)
            if hi - lo > 0:
                zaddr = cpu.memory.mmap(lo, hi - lo, perms)
                assert not BAD_ADDR(zaddr)

            lo = vaddr + filesz
            hi = CGC_PAGEALIGN(vaddr + memsz)
            if hi - lo > 0:
                old_perms = cpu.memory.perms(lo)
                cpu.memory.mprotect(lo, hi - lo, "rw")
                try:
                    cpu.memory[lo:hi] = "\x00" * (hi - lo)
                except Exception as e:
                    logger.debug("Exception zeroing main elf fractional pages: %s" % str(e))
                cpu.memory.mprotect(lo, hi, old_perms)

            if addr is None:
                addr = zaddr
            assert addr is not None

            k = vaddr + filesz
            if k > bss:
                bss = k
            if "x" in perms and end_code < k:
                end_code = k
            if end_data < k:
                end_data = k

            k = vaddr + memsz
            if k > brk:
                brk = k

        bss = brk
        stack_base = 0xBAAAAFFC
        stack_size = 0x800000
        stack = cpu.memory.mmap(0xBAAAB000 - stack_size, stack_size, "rwx") + stack_size - 4
        assert (stack_base) in cpu.memory and (stack_base - stack_size + 4) in cpu.memory

        # Only one thread in Decree
        status, thread = next(cgc.threads())
        assert status == "Running"

        logger.info("Setting initial cpu state")
        cpu.write_register("EAX", 0x0)
        cpu.write_register(
            "ECX",
            cpu.memory.mmap(
                CGC_PAGESTART(0x4347C000), CGC_PAGEALIGN(4096 + CGC_PAGEOFFSET(0x4347C000)), "rwx"
            ),
        )
        cpu.write_register("EDX", 0x0)
        cpu.write_register("EBX", 0x0)
        cpu.write_register("ESP", stack)
        cpu.write_register("EBP", 0x0)
        cpu.write_register("ESI", 0x0)
        cpu.write_register("EDI", 0x0)
        cpu.write_register("EIP", thread["EIP"])
        cpu.write_register("RFLAGS", 0x202)
        cpu.write_register("CS", 0x0)
        cpu.write_register("SS", 0x0)
        cpu.write_register("DS", 0x0)
        cpu.write_register("ES", 0x0)
        cpu.write_register("FS", 0x0)
        cpu.write_register("GS", 0x0)

        cpu.memory.mmap(0x4347C000, 0x1000, "r")
        # cpu.memory[0x4347c000:0x4347d000] = 'A' 0x1000

        logger.info("Entry point: %016x", cpu.EIP)
        logger.info("Stack start: %016x", cpu.ESP)
        logger.info("Brk: %016x", brk)
        logger.info("Mappings:")
        for m in str(cpu.memory).split("\n"):
            logger.info("  %s", m)
        return [cpu]

    def _open(self, f):
        if None in self.files:
            fd = self.files.index(None)
            self.files[fd] = f
        else:
            fd = len(self.files)
            self.files.append(f)
        return fd

    def _close(self, fd):
        """
        Closes a file descriptor
        :rtype: int
        :param fd: the file descriptor to close.
        :return: C{0} on success.
        """
        self.files[fd] = None

    def _dup(self, fd):
        """
        Duplicates a file descriptor
        :rtype: int
        :param fd: the file descriptor to close.
        :return: C{0} on success.
        """
        return self._open(self.files[fd])

    def _is_open(self, fd):
        return fd >= 0 and fd < len(self.files) and self.files[fd] is not None

    def sys_allocate(self, cpu, length, isX, addr):
        """allocate - allocate virtual memory

        The  allocate  system call creates a new allocation in the virtual address
        space of the calling process.  The length argument specifies the length of
        the allocation in bytes which will be rounded up to the hardware page size.

        The kernel chooses the address at which to create the allocation; the
        address of the new allocation is returned in *addr as the result of the call.

        All newly allocated memory is readable and writeable. In addition, the
        is_X argument is a boolean that allows newly allocated memory to be marked
        as executable (non-zero) or non-executable (zero).

        The allocate function is invoked through system call number 5.

        :param cpu: current CPU
        :param length: the length of the allocation in bytes
        :param isX: boolean that allows newly allocated memory to be marked as executable
        :param addr: the address of the new allocation is returned in *addr

        :return: On success, allocate returns zero and a pointer to the allocated area
                            is returned in *addr.  Otherwise, an error code is returned
                            and *addr is undefined.
                EINVAL   length is zero.
                EINVAL   length is too large.
                EFAULT   addr points to an invalid address.
                ENOMEM   No memory is available or the process' maximum number of allocations
                         would have been exceeded.
        """
        # TODO: check 4 bytes from addr
        if addr not in cpu.memory:
            logger.info("ALLOCATE: addr points to invalid address. Returning EFAULT")
            return Decree.CGC_EFAULT

        perms = ["rw ", "rwx"][bool(isX)]
        try:
            result = cpu.memory.mmap(None, length, perms)
        except Exception as e:
            logger.info("ALLOCATE exception %s. Returning ENOMEM %r", str(e), length)
            return Decree.CGC_ENOMEM
        cpu.write_int(addr, result, 32)
        logger.info("ALLOCATE(%d, %s, 0x%08x) -> 0x%08x" % (length, perms, addr, result))
        self.syscall_trace.append(("_allocate", -1, length))
        return 0

    def sys_random(self, cpu, buf, count, rnd_bytes):
        """random - fill a buffer with random data

        The  random  system call populates the buffer referenced by buf with up to
        count bytes of random data. If count is zero, random returns 0 and optionally
        sets *rx_bytes to zero. If count is greater than SSIZE_MAX, the result is unspecified.

        :param cpu: current CPU
        :param buf: a memory buffer
        :param count: max number of bytes to receive
        :param rnd_bytes: if valid, points to the actual number of random bytes

        :return:  0        On success
                  EINVAL   count is invalid.
                  EFAULT   buf or rnd_bytes points to an invalid address.
        """

        ret = 0
        if count != 0:
            if count > Decree.CGC_SSIZE_MAX or count < 0:
                ret = Decree.CGC_EINVAL
            else:
                # TODO check count bytes from buf
                if buf not in cpu.memory or (buf + count) not in cpu.memory:
                    logger.info("RANDOM: buf points to invalid address. Returning EFAULT")
                    return Decree.CGC_EFAULT

                with open("/dev/urandom", "rb") as f:
                    data = f.read(count)

                self.syscall_trace.append(("_random", -1, data))
                cpu.write_bytes(buf, data)

        # TODO check 4 bytes from rx_bytes
        if rnd_bytes:
            if rnd_bytes not in cpu.memory:
                logger.info("RANDOM: Not valid rnd_bytes. Returning EFAULT")
                return Decree.CGC_EFAULT
            cpu.write_int(rnd_bytes, len(data), 32)

        logger.info(
            "RANDOM(0x%08x, %d, 0x%08x) -> <%s>)" % (buf, count, rnd_bytes, repr(data[:10]))
        )
        return ret

    def sys_receive(self, cpu, fd, buf, count, rx_bytes):
        """receive - receive bytes from a file descriptor

        The receive system call reads up to count bytes from file descriptor fd to the
        buffer pointed to by buf. If count is zero, receive returns 0 and optionally
        sets *rx_bytes to zero.

        :param cpu: current CPU.
        :param fd: a valid file descriptor
        :param buf: a memory buffer
        :param count: max number of bytes to receive
        :param rx_bytes: if valid, points to the actual number of bytes received
        :return: 0            Success
                 EBADF        fd is not a valid file descriptor or is not open
                 EFAULT       buf or rx_bytes points to an invalid address.
        """
        data = ""
        if count != 0:
            if not self._is_open(fd):
                logger.info("RECEIVE: Not valid file descriptor on receive. Returning EBADF")
                return Decree.CGC_EBADF

            # TODO check count bytes from buf
            if buf not in cpu.memory:  # or not  buf+count in cpu.memory:
                logger.info("RECEIVE: buf points to invalid address. Returning EFAULT")
                return Decree.CGC_EFAULT

            # import random
            # count = random.randint(1,count)
            if fd > 2 and self.files[fd].is_empty():
                cpu.PC -= cpu.instruction.size
                self.wait([fd], [], None)
                raise RestartSyscall()

            # get some potential delay
            # if random.randint(5) == 0 and count > 1:
            #    count = count/2

            # Read the data and put it in memory
            data = self.files[fd].receive(count)
            self.syscall_trace.append(("_receive", fd, data))
            cpu.write_bytes(buf, data)

            self.signal_receive(fd)

        # TODO check 4 bytes from rx_bytes
        if rx_bytes:
            if rx_bytes not in cpu.memory:
                logger.info("RECEIVE: Not valid file descriptor on receive. Returning EFAULT")
                return Decree.CGC_EFAULT
            cpu.write_int(rx_bytes, len(data), 32)

        logger.info(
            "RECEIVE(%d, 0x%08x, %d, 0x%08x) -> <%s> (size:%d)"
            % (fd, buf, count, rx_bytes, repr(data)[: min(count, 10)], len(data))
        )
        return 0

    def sys_transmit(self, cpu, fd, buf, count, tx_bytes):
        """transmit - send bytes through a file descriptor
        The  transmit system call writes up to count bytes from the buffer pointed
        to by buf to the file descriptor fd. If count is zero, transmit returns 0
        and optionally sets *tx_bytes to zero.

        :param cpu           current CPU
        :param fd            a valid file descriptor
        :param buf           a memory buffer
        :param count         number of bytes to send
        :param tx_bytes      if valid, points to the actual number of bytes transmitted
        :return: 0            Success
                 EBADF        fd is not a valid file descriptor or is not open.
                 EFAULT       buf or tx_bytes points to an invalid address.
        """
        data = []
        if count != 0:

            if not self._is_open(fd):
                logger.error("TRANSMIT: Not valid file descriptor. Returning EBADFD %d", fd)
                return Decree.CGC_EBADF

            # TODO check count bytes from buf
            if buf not in cpu.memory or (buf + count) not in cpu.memory:
                logger.debug("TRANSMIT: buf points to invalid address. Rerurning EFAULT")
                return Decree.CGC_EFAULT

            if fd > 2 and self.files[fd].is_full():
                cpu.PC -= cpu.instruction.size
                self.wait([], [fd], None)
                raise RestartSyscall()

            for i in range(0, count):
                value = Operators.CHR(cpu.read_int(buf + i, 8))
                if not isinstance(value, str):
                    logger.debug("TRANSMIT: Writing symbolic values to file %d", fd)
                    # value = str(value)
                data.append(value)
            self.files[fd].transmit(data)

            logger.info(
                "TRANSMIT(%d, 0x%08x, %d, 0x%08x) -> <%.24r>"
                % (fd, buf, count, tx_bytes, "".join([str(x) for x in data]))
            )
            self.syscall_trace.append(("_transmit", fd, data))
            self.signal_transmit(fd)

        # TODO check 4 bytes from tx_bytes
        if tx_bytes:
            if tx_bytes not in cpu.memory:
                logger.debug("TRANSMIT: Not valid tx_bytes pointer on transmit. Returning EFAULT")
                return Decree.CGC_EFAULT
            cpu.write_int(tx_bytes, len(data), 32)

        return 0

    def sys_terminate(self, cpu, error_code):
        """
        Exits all threads in a process
        :param cpu: current CPU.
        :raises Exception: 'Finished'
        """
        procid = self.procs.index(cpu)
        self.sched()
        self.running.remove(procid)
        # self.procs[procid] = None #let it there so we can report?
        if issymbolic(error_code):
            logger.info(
                "TERMINATE PROC_%02d with symbolic exit code [%d,%d]",
                procid,
                solver.minmax(self.constraints, error_code),
            )
        else:
            logger.info("TERMINATE PROC_%02d %x", procid, error_code)
        if len(self.running) == 0:
            raise TerminateState(f"Process exited correctly. Code: {error_code}")
        return error_code

    def sys_deallocate(self, cpu, addr, size):
        """deallocate - remove allocations
        The  deallocate  system call deletes the allocations for the specified
        address range, and causes further references to the addresses within the
        range to generate invalid memory accesses. The region is also
        automatically deallocated when the process is terminated.

        The address addr must be a multiple of the page size.  The length parameter
        specifies the size of the region to be deallocated in bytes.  All pages
        containing a part of the indicated range are deallocated, and subsequent
        references will terminate the process.  It is not an error if the indicated
        range does not contain any allocated pages.

        The deallocate function is invoked through system call number 6.

        :param cpu: current CPU
        :param addr: the starting address to unmap.
        :param size: the size of the portion to unmap.
        :return 0        On success
                EINVAL   addr is not page aligned.
                EINVAL   length is zero.
                EINVAL   any  part  of  the  region  being  deallocated  is outside the valid
                         address range of the process.

        :param cpu: current CPU.
        :return: C{0} on success.
        """
        logger.info("DEALLOCATE(0x%08x, %d)" % (addr, size))

        if addr & 0xFFF != 0:
            logger.info("DEALLOCATE: addr is not page aligned")
            return Decree.CGC_EINVAL
        if size == 0:
            logger.info("DEALLOCATE:length is zero")
            return Decree.CGC_EINVAL
        # unlikely AND WRONG!!!
        # if addr > Decree.CGC_SSIZE_MAX or addr+size > Decree.CGC_SSIZE_MAX:
        #    logger.info("DEALLOCATE: part of the region being deallocated is outside the valid address range of the process")
        #    return Decree.CGC_EINVAL

        cpu.memory.munmap(addr, size)
        self.syscall_trace.append(("_deallocate", -1, size))
        return 0

    def sys_fdwait(self, cpu, nfds, readfds, writefds, timeout, readyfds):
        """fdwait - wait for file descriptors to become ready"""
        logger.debug(
            "FDWAIT(%d, 0x%08x, 0x%08x, 0x%08x, 0x%08x)"
            % (nfds, readfds, writefds, timeout, readyfds)
        )

        if timeout:
            if timeout not in cpu.memory:  # todo: size
                logger.info("FDWAIT: timeout is pointing to invalid memory. Returning EFAULT")
                return Decree.CGC_EFAULT

        if readyfds:
            if readyfds not in cpu.memory:
                logger.info("FDWAIT: readyfds pointing to invalid memory. Returning EFAULT")
                return Decree.CGC_EFAULT

        writefds_wait = set()
        writefds_ready = set()

        fds_bitsize = (nfds + 7) & ~7
        if writefds:
            if writefds not in cpu.memory:
                logger.info("FDWAIT: writefds pointing to invalid memory. Returning EFAULT")
                return Decree.CGC_EFAULT
            bits = cpu.read_int(writefds, fds_bitsize)

            for fd in range(nfds):
                if bits & 1 << fd:
                    if self.files[fd].is_full():
                        writefds_wait.add(fd)
                    else:
                        writefds_ready.add(fd)

        readfds_wait = set()
        readfds_ready = set()
        if readfds:
            if readfds not in cpu.memory:
                logger.info("FDWAIT: readfds pointing to invalid memory. Returning EFAULT")
                return Decree.CGC_EFAULT
            bits = cpu.read_int(readfds, fds_bitsize)
            for fd in range(nfds):
                if bits & 1 << fd:
                    if self.files[fd].is_empty():
                        readfds_wait.add(fd)
                    else:
                        readfds_ready.add(fd)
        n = len(readfds_ready) + len(writefds_ready)
        if n == 0:
            # TODO FIX timeout symbolic
            if timeout != 0:
                seconds = cpu.read_int(timeout, 32)
                microseconds = cpu.read_int(timeout + 4, 32)
                logger.info(
                    "FDWAIT: waiting for read on fds: {%s} and write to: {%s} timeout: %d",
                    repr(list(readfds_wait)),
                    repr(list(writefds_wait)),
                    microseconds + 1000 * seconds,
                )
                to = microseconds + 1000 * seconds
                # no ready file, wait
            else:
                to = None
                logger.info(
                    "FDWAIT: waiting for read on fds: {%s} and write to: {%s} timeout: INDIFENITELY",
                    repr(list(readfds_wait)),
                    repr(list(writefds_wait)),
                )

            cpu.PC -= cpu.instruction.size
            self.wait(readfds_wait, writefds_wait, to)
            raise RestartSyscall()  # When coming back from a timeout remember
            # not to backtrack instruction and set EAX to 0! :( ugliness alert!

        if readfds:
            bits = 0
            for fd in readfds_ready:
                bits |= 1 << fd
            for byte in range(0, nfds, 8):
                cpu.write_int(readfds, (bits >> byte) & 0xFF, 8)
        if writefds:
            bits = 0
            for fd in writefds_ready:
                bits |= 1 << fd
            for byte in range(0, nfds, 8):
                cpu.write_int(writefds, (bits >> byte) & 0xFF, 8)

        logger.info("FDWAIT: continuing. Some file is ready Readyfds: %08x", readyfds)
        if readyfds:
            cpu.write_int(readyfds, n, 32)

        self.syscall_trace.append(("_fdwait", -1, None))
        return 0

    def int80(self, cpu):
        """
        32 bit dispatcher.
        :param cpu: current CPU.
        _terminate, transmit, receive, fdwait, allocate, deallocate and random
        """
        syscalls = {
            0x00000001: self.sys_terminate,
            0x00000002: self.sys_transmit,
            0x00000003: self.sys_receive,
            0x00000004: self.sys_fdwait,
            0x00000005: self.sys_allocate,
            0x00000006: self.sys_deallocate,
            0x00000007: self.sys_random,
        }
        if cpu.EAX not in syscalls.keys():
            raise TerminateState(f"32 bit DECREE system call number {cpu.EAX} Not Implemented")
        func = syscalls[cpu.EAX]
        logger.debug("SYSCALL32: %s (nargs: %d)", func.__name__, func.__code__.co_argcount)
        nargs = func.__code__.co_argcount
        args = [cpu, cpu.EBX, cpu.ECX, cpu.EDX, cpu.ESI, cpu.EDI, cpu.EBP]
        cpu.EAX = func(*args[: nargs - 1])

    def sched(self):
        """Yield CPU.
        This will choose another process from the RUNNNIG list and change
        current running process. May give the same cpu if only one running
        process.
        """
        if len(self.procs) > 1:
            logger.info("SCHED:")
            logger.info("\tProcess: %r", self.procs)
            logger.info("\tRunning: %r", self.running)
            logger.info("\tRWait: %r", self.rwait)
            logger.info("\tTWait: %r", self.twait)
            logger.info("\tTimers: %r", self.timers)
            logger.info("\tCurrent clock: %d", self.clocks)
            logger.info("\tCurrent cpu: %d", self._current)

        if len(self.running) == 0:
            logger.info("None running checking if there is some process waiting for a timeout")
            if all([x is None for x in self.timers]):
                raise Deadlock()
            self.clocks = min([x for x in self.timers if x is not None]) + 1
            self.check_timers()
            assert len(self.running) != 0, "DEADLOCK!"
            self._current = self.running[0]
            return
        next_index = (self.running.index(self._current) + 1) % len(self.running)
        next = self.running[next_index]
        if len(self.procs) > 1:
            logger.info("\tTransfer control from process %d to %d", self._current, next)
        self._current = next

    def wait(self, readfds, writefds, timeout):
        """Wait for filedescriptors or timeout.
        Adds the current process to the corresponding waiting list and
        yields the cpu to another running process.
        """
        logger.info("WAIT:")
        logger.info(
            "\tProcess %d is going to wait for [ %r %r %r ]",
            self._current,
            readfds,
            writefds,
            timeout,
        )
        logger.info("\tProcess: %r", self.procs)
        logger.info("\tRunning: %r", self.running)
        logger.info("\tRWait: %r", self.rwait)
        logger.info("\tTWait: %r", self.twait)
        logger.info("\tTimers: %r", self.timers)

        for fd in readfds:
            self.rwait[fd].add(self._current)
        for fd in writefds:
            self.twait[fd].add(self._current)
        if timeout is not None:
            self.timers[self._current] = self.clocks + timeout
        else:
            self.timers[self._current] = None
        procid = self._current
        # self.sched()
        next_index = (self.running.index(procid) + 1) % len(self.running)
        self._current = self.running[next_index]
        logger.info("\tTransfer control from process %d to %d", procid, self._current)
        logger.info("\tREMOVING %r from %r. Current: %r", procid, self.running, self._current)
        self.running.remove(procid)
        if self._current not in self.running:
            logger.info("\tCurrent not running. Checking for timers...")
            self._current = None
            if all([x is None for x in self.timers]):
                raise Deadlock()
            self.check_timers()

    def awake(self, procid):
        """ Remove procid from waitlists and reestablish it in the running list """
        logger.info(
            "Remove procid:%d from waitlists and reestablish it in the running list", procid
        )
        for wait_list in self.rwait:
            if procid in wait_list:
                wait_list.remove(procid)
        for wait_list in self.twait:
            if procid in wait_list:
                wait_list.remove(procid)
        self.timers[procid] = None
        self.running.append(procid)
        if self._current is None:
            self._current = procid

    def connections(self, fd):
        if fd in [0, 1, 2]:
            return None
        if fd % 2:
            return fd + 1
        else:
            return fd - 1

    def signal_receive(self, fd):
        """ Awake one process waiting to receive data on fd """
        connections = self.connections
        if connections(fd) and self.twait[connections(fd)]:
            procid = random.sample(self.twait[connections(fd)], 1)[0]
            self.awake(procid)

    def signal_transmit(self, fd):
        """ Awake one process waiting to transmit data on fd """
        connections = self.connections
        if connections(fd) and self.rwait[connections(fd)]:
            procid = random.sample(self.rwait[connections(fd)], 1)[0]
            self.awake(procid)

    def check_timers(self):
        """ Awake process if timer has expired """
        if self._current is None:
            # Advance the clocks. Go to future!!
            advance = min([x for x in self.timers if x is not None]) + 1
            logger.info("Advancing the clock from %d to %d", self.clocks, advance)
            self.clocks = advance
        for procid in range(len(self.timers)):
            if self.timers[procid] is not None:
                if self.clocks > self.timers[procid]:
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
        except Interruption as e:
            if e.N != 0x80:
                raise
            try:
                self.int80(self.current)
            except RestartSyscall:
                pass

        return True


############################################################################
# Symbolic versions follows


class SDecree(Decree):
    """
    A symbolic extension of a Decree Operating System .
    """

    def __init__(self, constraints, programs, symbolic_random=None):
        """
        Builds a symbolic extension of a Decree OS
        :param constraints: a constraint set
        :param cpus: CPU for this platform
        :param mem: memory for this platform
        """
        self.random = 0
        self._constraints = constraints
        super().__init__(programs)

    def _mk_proc(self):
        return I386Cpu(SMemory32(self.constraints))

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
        return state

    def __setstate__(self, state):
        self._constraints = state["constraints"]
        self.random = state["random"]
        super().__setstate__(state)

    def sys_receive(self, cpu, fd, buf, count, rx_bytes):
        """
        Symbolic version of Decree.sys_receive
        """
        if issymbolic(fd):
            logger.info("Ask to read from a symbolic file descriptor!!")
            cpu.PC = cpu.PC - cpu.instruction.size
            raise SymbolicSyscallArgument(cpu, 0)

        if issymbolic(buf):
            logger.info("Ask to read to a symbolic buffer")
            cpu.PC = cpu.PC - cpu.instruction.size
            raise SymbolicSyscallArgument(cpu, 1)

        if issymbolic(count):
            logger.info("Ask to read a symbolic number of bytes ")
            cpu.PC = cpu.PC - cpu.instruction.size
            raise SymbolicSyscallArgument(cpu, 2)

        if issymbolic(rx_bytes):
            logger.info("Ask to return size to a symbolic address ")
            cpu.PC = cpu.PC - cpu.instruction.size
            raise SymbolicSyscallArgument(cpu, 3)

        return super().sys_receive(cpu, fd, buf, count, rx_bytes)

    def sys_transmit(self, cpu, fd, buf, count, tx_bytes):
        """
        Symbolic version of Decree.sys_transmit
        """
        if issymbolic(fd):
            logger.info("Ask to write to a symbolic file descriptor!!")
            cpu.PC = cpu.PC - cpu.instruction.size
            raise SymbolicSyscallArgument(cpu, 0)

        if issymbolic(buf):
            logger.info("Ask to write to a symbolic buffer")
            cpu.PC = cpu.PC - cpu.instruction.size
            raise SymbolicSyscallArgument(cpu, 1)

        if issymbolic(count):
            logger.info("Ask to write a symbolic number of bytes ")
            cpu.PC = cpu.PC - cpu.instruction.size
            raise SymbolicSyscallArgument(cpu, 2)

        if issymbolic(tx_bytes):
            logger.info("Ask to return size to a symbolic address ")
            cpu.PC = cpu.PC - cpu.instruction.size
            raise SymbolicSyscallArgument(cpu, 3)

        return super().sys_transmit(cpu, fd, buf, count, tx_bytes)

    def sys_allocate(self, cpu, length, isX, address_p):
        if issymbolic(length):
            logger.info("Ask to ALLOCATE a symbolic number of bytes ")
            cpu.PC = cpu.PC - cpu.instruction.size
            raise SymbolicSyscallArgument(cpu, 0)
        if issymbolic(isX):
            logger.info("Ask to ALLOCATE potentially executable or not executable memory")
            cpu.PC = cpu.PC - cpu.instruction.size
            raise SymbolicSyscallArgument(cpu, 1)
        if issymbolic(address_p):
            logger.info("Ask to return ALLOCATE result to a symbolic reference ")
            cpu.PC = cpu.PC - cpu.instruction.size
            raise SymbolicSyscallArgument(cpu, 2)
        return super().sys_allocate(cpu, length, isX, address_p)

    def sys_deallocate(self, cpu, addr, size):
        if issymbolic(addr):
            logger.info("Ask to DEALLOCATE a symbolic pointer?!")
            cpu.PC = cpu.PC - cpu.instruction.size
            raise SymbolicSyscallArgument(cpu, 0)
        if issymbolic(size):
            logger.info("Ask to DEALLOCATE a symbolic size?!")
            cpu.PC = cpu.PC - cpu.instruction.size
            raise SymbolicSyscallArgument(cpu, 1)
        return super().sys_deallocate(cpu, addr, size)

    def sys_random(self, cpu, buf, count, rnd_bytes):
        if issymbolic(buf):
            logger.info("Ask to write random bytes to a symbolic buffer")
            cpu.PC = cpu.PC - cpu.instruction.size
            raise SymbolicSyscallArgument(cpu, 0)

        if issymbolic(count):
            logger.info("Ask to read a symbolic number of random bytes ")
            cpu.PC = cpu.PC - cpu.instruction.size
            raise SymbolicSyscallArgument(cpu, 1)

        if issymbolic(rnd_bytes):
            logger.info("Ask to return rnd size to a symbolic address ")
            cpu.PC = cpu.PC - cpu.instruction.size
            raise SymbolicSyscallArgument(cpu, 2)

        data = []
        for i in range(count):
            # TODO - should value be symbolic?
            value = cgcrandom.stream[self.random]
            data.append(value)
            self.random += 1

        cpu.write_bytes(buf, data)
        if rnd_bytes:
            cpu.write_int(rnd_bytes, len(data), 32)
        logger.info("RANDOM(0x%08x, %d, 0x%08x) -> %d", buf, count, rnd_bytes, len(data))
        return 0


class DecreeEmu:

    RANDOM = 0

    @staticmethod
    def cgc_initialize_secret_page(platform):
        logger.info("Skipping: cgc_initialize_secret_page()")
        return 0

    @staticmethod
    def cgc_random(platform, buf, count, rnd_bytes):
        from . import cgcrandom

        if issymbolic(buf):
            logger.info("Ask to write random bytes to a symbolic buffer")
            raise ConcretizeArgument(platform.current, 0)

        if issymbolic(count):
            logger.info("Ask to read a symbolic number of random bytes ")
            raise ConcretizeArgument(platform.current, 1)

        if issymbolic(rnd_bytes):
            logger.info("Ask to return rnd size to a symbolic address ")
            raise ConcretizeArgument(platform.current, 2)

        data = []
        for i in range(count):
            value = cgcrandom.stream[DecreeEmu.RANDOM]
            data.append(value)
            DecreeEmu.random += 1

        cpu = platform.current
        cpu.write(buf, data)
        if rnd_bytes:
            cpu.store(rnd_bytes, len(data), 32)
        logger.info("RANDOM(0x%08x, %d, 0x%08x) -> %d", buf, count, rnd_bytes, len(data))
        return 0
