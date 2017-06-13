import errno
import fcntl
import logging
import os
import random
import struct

from elftools.elf.elffile import ELFFile

from ..utils.helpers import issymbolic
from ..core.cpu.abstractcpu import Interruption, Syscall, ConcretizeArgument
from ..core.cpu.cpufactory import CpuFactory
from ..core.memory import SMemory32, SMemory64, Memory32, Memory64
from ..core.smtlib import Operators, ConstraintSet
from ..platforms.platform import Platform
from ..core.cpu.arm import *
from ..core.executor import SyscallNotImplemented, ProcessExit
from . import linux_syscalls

logger = logging.getLogger("PLATFORM")


class RestartSyscall(Exception):
    pass

class Deadlock(Exception):
    pass

def perms_from_elf(elf_flags):
    return ['   ', '  x', ' w ', ' wx', 'r  ', 'r x', 'rw ', 'rwx'][elf_flags&7]

def perms_from_protflags(prot_flags):
    return ['   ', 'r  ', ' w ', 'rw ', '  x', 'r x', ' wx', 'rwx'][prot_flags&7]

class File(object):
    def __init__(self, *args, **kwargs):
        # TODO: assert file is seekable otherwise we should save what was
        # read/write to the state
        self.file = file(*args,**kwargs)

    def __getstate__(self):
        state = {}
        state['name'] = self.name
        state['mode'] = self.mode
        state['pos'] = self.tell()
        return state

    def __setstate__(self, state):
        name = state['name']
        mode = state['mode']
        pos = state['pos']
        self.file = file(name, mode)
        self.seek(pos)

    @property
    def name(self):
        return self.file.name

    @property
    def mode(self):
        return self.file.mode

    def stat(self):
        return os.fstat(self.fileno())

    def ioctl(self, request, argp):
        #argp ignored..
        return fcntl.fcntl(self, request)

    def tell(self, *args):
        return self.file.tell(*args)

    def seek(self, *args):
        return self.file.seek(*args)

    def write(self, buf):
        for c in buf:
            self.file.write(c)

    def read(self, *args):
        return self.file.read(*args)

    def close(self, *args):
        return self.file.close(*args)

    def fileno(self, *args):
        return self.file.fileno(*args)

    def is_full(self):
        return False

    def sync(self):
        '''
        Flush buffered data. Currently not implemented.
        '''
        return

class SymbolicFile(File):
    '''
    Represents a symbolic file.
    '''
    def __init__(self, constraints, path="sfile", mode='rw', max_size=100,
                 wildcard='+'):
        '''
        Builds a symbolic file

        :param constraints: the SMT constraints
        :param str path: the pathname of the symbolic file
        :param str mode: the access permissions of the symbolic file
        :param max_size: Maximun amount of bytes of the symbolic file
        :param str wildcard: Wildcard to be used in symbolic file
        '''
        super(SymbolicFile, self).__init__(path, mode)

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
            logger.warning(("Found more wilcards in the file than free ",
                            "symbolic values allowed (%d > %d)"),
                           symbols_cnt,
                           max_size)
        else:
            logger.debug("Found %d free symbolic values on file %s",
                         symbols_cnt,
                         self.name)

    def __getstate__(self):
        state = {}
        state['array'] = self.array
        state['pos'] = self.pos
        state['max_size'] = self.max_size
        return state

    def __setstate__(self, state):
        self.pos = state['pos']
        self.max_size = state['max_size']
        self.array = state['array']

    @property
    def constraints(self):
        return self._constraints

    def tell(self):
        '''
        Returns the read/write file offset
        :rtype: int
        :return: the read/write file offset.
        '''
        return self.pos

    def seek(self, pos):
        '''
        Returns the read/write file offset
        :rtype: int
        :return: the read/write file offset.
        '''
        assert isinstance(pos, (int, long))
        self.pos = pos

    def read(self, count):
        '''
        Reads up to C{count} bytes from the file.
        :rtype: list
        :return: the list of symbolic bytes read
        '''
        if self.pos > self.max_size:
            return []
        else:
            size = min(count, self.max_size - self.pos)
            ret = [self.array[i] for i in xrange(self.pos, self.pos + size)]
            self.pos += size
            return ret

    def write(self, data):
        '''
        Writes the symbolic bytes in C{data} onto the file.
        '''
        size = min(len(data), self.max_size - self.pos)
        for i in xrange(self.pos, self.pos + size):
            self.array[i] = data[i - self.pos]

class Socket(object):
    def stat(self):
        from collections import namedtuple
        stat_result = namedtuple('stat_result', ['st_mode','st_ino','st_dev','st_nlink','st_uid','st_gid','st_size','st_atime','st_mtime','st_ctime', 'st_blksize','st_blocks','st_rdev'])
        return stat_result(8592,11,9,1,1000,5,0,1378673920,1378673920,1378653796,0x400,0x8808,0)

    @staticmethod
    def pair():
        a = Socket()
        b = Socket()
        a.connect(b)
        return a,b

    def __init__(self):
        self.buffer = [] #queue os bytes
        self.peer = None

    def __repr__(self):
        return "SOCKET(%x, %r, %x)"%(hash(self), self.buffer, hash(self.peer))

    def is_connected(self):
        return self.peer is not None

    def is_empty(self):
        return not self.buffer

    def is_full(self):
        return len(self.buffer) > 2 * 1024

    def connect(self, peer):
        assert not self.is_connected()
        assert not peer.is_connected()
        self.peer = peer
        if peer.peer is None:
            peer.peer = self

    def read(self, size):
        return self.receive(size)

    def receive(self, size):
        rx_bytes = min(size, len(self.buffer))
        ret = []
        for i in xrange(rx_bytes):
            ret.append(self.buffer.pop())
        return ret

    def write(self, buf):
        assert self.is_connected()
        return self.peer._transmit(buf)

    def _transmit(self, buf):
        for c in buf:
            self.buffer.insert(0,c)
        return len(buf)


class Linux(Platform):
    '''
    A simple Linux Operating System Platform.
    This class emulates the most common Linux system calls
    '''

    def __init__(self, program, argv=None, envp=None):
        '''
        Builds a Linux OS platform
        :param string program: The path to ELF binary
        :param list argv: The argv array; not including binary.
        :param list envp: The ENV variables.
        '''
        super(Linux, self).__init__(program)

        self.program = program
        self.clocks = 0
        self.files = []
        self.syscall_trace = []

        if program != None:
            self.elf = ELFFile(file(program))
            self.arch = {'x86': 'i386', 'x64': 'amd64', 'ARM': 'armv7'}[self.elf.get_machine_arch()]

            self._init_cpu(self.arch)
            self._init_fds()
            self._execve(program, argv, envp)

    @classmethod
    def empty_platform(cls, arch):
        '''
        Create a platform without an ELF loaded.

        :param str arch: The architecture of the new platform
        :rtype: Linux
        '''
        platform = cls(None)
        platform._init_cpu(arch)
        platform._init_fds()
        return platform

    def _init_fds(self):
        # open standard files stdin, stdout, stderr
        logger.debug("Opening file descriptors (0,1,2) (STDIN, STDOUT, STDERR)")
        self.input = Socket()
        self.output = Socket()
        self.stderr = Socket()

        stdin = Socket()
        stdout = Socket()
        stderr = Socket()
        #A transmit to stdin,stdout or stderr will be directed to out
        stdin.peer = self.output
        stdout.peer = self.output
        stderr.peer = self.stderr
        #A receive from stdin will get data from input
        self.input.peer = stdin
        #A receive on stdout or stderr will return no data (rx_bytes: 0)

        assert self._open(stdin) == 0
        assert self._open(stdout) == 1
        assert self._open(stderr) == 2

    def _init_cpu(self, arch):
        cpu = self._mk_proc(arch)
        self.procs = [cpu]
        self._current = 0
        self._function_abi = CpuFactory.get_function_abi(cpu, 'linux', arch)
        self._syscall_abi = CpuFactory.get_syscall_abi(cpu, 'linux', arch)

    def _execve(self, program, argv, envp):
        '''
        Load `program` and establish program state, such as stack and arguments.

        :param program str: The ELF binary to load
        :param argv list: argv array
        :param envp list: envp array
        '''
        argv = [] if argv is None else argv
        envp = [] if envp is None else envp

        logger.debug("Loading {} as a {} elf".format(program,self.arch))

        self.load(program)
        self._arch_specific_init()

        self._stack_top = self.current.STACK
        self.setup_stack([program]+argv, envp)

        nprocs = len(self.procs)
        nfiles = len(self.files)
        assert nprocs > 0
        self.running = range(nprocs)

        #Each process can wait for one timeout
        self.timers = [ None ] * nprocs
        #each fd has a waitlist
        self.rwait = [set() for _ in xrange(nfiles)]
        self.twait = [set() for _ in xrange(nfiles)]

    def _mk_proc(self, arch):
        if arch in {'i386', 'armv7'}:
            mem = Memory32()
        else:
            mem = Memory64()
        return CpuFactory.get_cpu(mem, arch)

    @property
    def current(self):
        return self.procs[self._current]

    def __getstate__(self):
        state = {}
        state['clocks'] = self.clocks
        state['input'] = self.input.buffer
        state['output'] = self.output.buffer

        files = []
        for fd in self.files:
            if isinstance(fd, Socket):
                files.append(('Socket', fd.buffer))
            else:
                files.append(('File',fd))
        state['files'] = files

        state['procs'] = self.procs
        state['current'] = self._current
        state['running'] = self.running
        state['rwait'] = self.rwait
        state['twait'] = self.twait
        state['timers'] = self.timers
        state['syscall_trace'] = self.syscall_trace
        state['base'] = self.base
        state['elf_bss'] = self.elf_bss
        state['end_code'] = self.end_code
        state['end_data'] = self.end_data
        state['elf_brk'] = self.elf_brk
        state['auxv'] = self.auxv
        state['program'] = self.program
        state['functionabi'] = self._function_abi
        state['syscallabi'] = self._syscall_abi
        state['uname_machine'] = self._uname_machine
        if hasattr(self, '_arm_tls_memory'):
            state['_arm_tls_memory'] = self._arm_tls_memory
        return state

    def __setstate__(self, state):
        """
        :todo: some asserts
        :todo: fix deps? (last line)
        """
        self.input = Socket()
        self.input.buffer = state['input']
        self.output = Socket()
        self.output.buffer = state['output']

        self.files = []
        for ty, buf in state['files']:
            if ty == 'Socket':
                f = Socket()
                f.buffer = buf
                self.files.append(f)
            else:
                self.files.append(buf)

        self.files[0].peer = self.output
        self.files[1].peer = self.output
        self.files[2].peer = self.output
        self.input.peer = self.files[0]

        self.procs = state['procs']
        self._current = state['current']
        self.running = state['running']
        self.rwait = state['rwait']
        self.twait = state['twait']
        self.timers = state['timers']
        self.clocks = state['clocks']

        self.syscall_trace = state['syscall_trace']
        self.base = state['base']
        self.elf_bss = state['elf_bss']
        self.end_code = state['end_code']
        self.end_data = state['end_data']
        self.elf_brk = state['elf_brk']
        self.auxv = state['auxv']
        self.program = state['program']
        self._function_abi = state['functionabi']
        self._syscall_abi = state['syscallabi']
        self._uname_machine = state['uname_machine']
        if '_arm_tls_memory' in state:
            self._arm_tls_memory = state['_arm_tls_memory']

    def _init_arm_kernel_helpers(self):
        '''
        ARM kernel helpers

        https://www.kernel.org/doc/Documentation/arm/kernel_user_helpers.txt
        '''

        page_data = bytearray('\xf1\xde\xfd\xe7' * 1024)

        # Extracted from a RPi2
        preamble = (
            'ff0300ea' +
            '650400ea' +
            'f0ff9fe5' +
            '430400ea' +
            '220400ea' +
            '810400ea' +
            '000400ea' +
            '870400ea'
        ).decode('hex')

        # XXX(yan): The following implementations of cmpxchg and cmpxchg64 were
        # handwritten to not use any exclusive instructions (e.g. ldrexd) or
        # locking. For actual implementations, refer to
        # arch/arm64/kernel/kuser32.S in the Linux source code.
        __kuser_cmpxchg64 = (
            '30002de9' + # push    {r4, r5}
            '08c09de5' + # ldr     ip, [sp, #8]
            '30009ce8' + # ldm     ip, {r4, r5}
            '010055e1' + # cmp     r5, r1
            '00005401' + # cmpeq   r4, r0
            '0100a013' + # movne   r0, #1
            '0000a003' + # moveq   r0, #0
            '0c008c08' + # stmeq   ip, {r2, r3}
            '3000bde8' + # pop     {r4, r5}
            '1eff2fe1'   # bx      lr
        ).decode('hex')

        __kuser_dmb = (
            '5bf07ff5' + # dmb ish
            '1eff2fe1'   # bx lr
        ).decode('hex')

        __kuser_cmpxchg = (
            '003092e5' + # ldr     r3, [r2]
            '000053e1' + # cmp     r3, r0
            '0000a003' + # moveq   r0, #0
            '00108205' + # streq   r1, [r2]
            '0100a013' + # movne   r0, #1
            '1eff2fe1'   # bx      lr
        ).decode('hex')

        # Map a TLS segment
        self._arm_tls_memory = self.current.memory.mmap(None, 4, 'rw ')

        __kuser_get_tls = (
            '04009FE5' + # ldr r0, [pc, #4]
            '010090e8' + # ldm r0, {r0}
            '1eff2fe1'   # bx lr
        ).decode('hex') + struct.pack('<I', self._arm_tls_memory)

        tls_area = '\x00'*12

        version = struct.pack('<I', 5)

        def update(address, code):
            page_data[address:address+len(code)] = code

        # Offsets from Documentation/arm/kernel_user_helpers.txt in Linux
        update(0x000, preamble)
        update(0xf60, __kuser_cmpxchg64)
        update(0xfa0, __kuser_dmb)
        update(0xfc0, __kuser_cmpxchg)
        update(0xfe0, __kuser_get_tls)
        update(0xff0, tls_area)
        update(0xffc, version)

        self.current.memory.mmap(0xffff0000, len(page_data), 'r x', page_data)

    def load_vdso(self, bits):
        #load vdso #TODO or #IGNORE
        vdso_top = {32: 0x7fff0000, 64: 0x7fff00007fff0000}[bits]
        vdso_size = len(file('vdso%2d.dump'%bits).read())
        vdso_addr = self.memory.mmapFile(self.memory._floor(vdso_top - vdso_size),
                                     vdso_size, 'r x',
                                     {32: 'vdso32.dump', 64: 'vdso64.dump'}[bits],
                                     0 )
        return vdso_addr


    def setup_stack(self, argv, envp):
        '''
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
        '''
        cpu = self.current

        # In case setup_stack() is called again, we make sure we're growing the
        # stack from the original top
        cpu.STACK = self._stack_top

        auxv = self.auxv
        logger.debug("Setting argv, envp and auxv.")
        logger.debug("\tArguments: %s"%repr(argv))
        if envp:
            logger.debug("\tEnvironment:")
            for e in envp:
                logger.debug("\t\t%s"%repr(e))

        logger.debug("\tAuxv:")
        for name, val in auxv.items():
            logger.debug("\t\t%s: %s"%(name, hex(val)))

        #We save the argument and environment pointers
        argvlst=[]
        envplst=[]

        #end envp marker empty string
        for evar in envp:
            cpu.push_bytes('\x00')
            envplst.append(cpu.push_bytes(evar))

        for arg in argv:
            cpu.push_bytes('\x00')
            argvlst.append(cpu.push_bytes(arg))


        #Put all auxv strings into the string stack area.
        #And replace the value be its pointer

        for name, value in auxv.items():
            if hasattr(value, '__len__'):
                cpu.push_bytes(value)
                auxv[name]=cpu.STACK

        #The "secure execution" mode of secure_getenv() is controlled by the
        #AT_SECURE flag contained in the auxiliary vector passed from the
        #kernel to user space.
        auxvnames = {
            'AT_IGNORE': 1, # Entry should be ignored
            'AT_EXECFD': 2, # File descriptor of program
            'AT_PHDR': 3, # Program headers for program
            'AT_PHENT':4, # Size of program header entry
            'AT_PHNUM':5, # Number of program headers
            'AT_PAGESZ': 6, # System page size
            'AT_BASE': 7, # Base address of interpreter
            'AT_FLAGS':8, # Flags
            'AT_ENTRY':9, # Entry point of program
            'AT_NOTELF': 10, # Program is not ELF
            'AT_UID':11, # Real uid
            'AT_EUID': 12, # Effective uid
            'AT_GID':13, # Real gid
            'AT_EGID': 14, # Effective gid
            'AT_CLKTCK': 17, # Frequency of times()
            'AT_PLATFORM': 15, # String identifying platform.
            'AT_HWCAP':16, # Machine-dependent hints about processor capabilities.
            'AT_FPUCW':18, # Used FPU control word.
            'AT_SECURE': 23, # Boolean, was exec setuid-like?
            'AT_BASE_PLATFORM': 24, # String identifying real platforms.
            'AT_RANDOM': 25, # Address of 16 random bytes.
            'AT_EXECFN': 31, # Filename of executable.
            'AT_SYSINFO':32, #Pointer to the global system page used for system calls and other nice things.
            'AT_SYSINFO_EHDR': 33, #Pointer to the global system page used for system calls and other nice things.
        }
        #AT_NULL
        cpu.push_int(0)
        cpu.push_int(0)
        for name, val in auxv.items():
            cpu.push_int(val)
            cpu.push_int(auxvnames[name])


        # NULL ENVP
        cpu.push_int(0)
        for var in reversed(envplst):              # ENVP n
            cpu.push_int(var)
        envp = cpu.STACK

        # NULL ARGV
        cpu.push_int(0)
        for arg in reversed(argvlst):              # Argv n
            cpu.push_int(arg)
        argv = cpu.STACK

        #ARGC
        cpu.push_int(len(argvlst))


    def load(self, filename):
        '''
        Loads and an ELF program in memory and prepares the initial CPU state.
        Creates the stack and loads the environment variables and the arguments in it.

        :param filename: pathname of the file to be executed. (used for auxv)
        :raises error:
            - 'Not matching cpu': if the program is compiled for a different architecture
            - 'Not matching memory': if the program is compiled for a different address size
        :todo: define va_randomize and read_implies_exec personality
        '''
        #load elf See binfmt_elf.c
        #read the ELF object file
        cpu = self.current
        elf = self.elf
        arch = self.arch
        addressbitsize = {'x86':32, 'x64':64, 'ARM': 32}[elf.get_machine_arch()]
        logger.debug("Loading %s as a %s elf"%(filename, arch))

        assert elf.header.e_type in ['ET_DYN', 'ET_EXEC', 'ET_CORE']

        #Get interpreter elf
        interpreter = None
        for elf_segment in elf.iter_segments():
            if elf_segment.header.p_type != 'PT_INTERP':
                continue
            interpreter_filename = elf_segment.data()[:-1]
            logger.info('Interpreter filename: %s', interpreter_filename)
            interpreter = ELFFile(file(interpreter_filename))
            break
        if not interpreter is None:
            assert interpreter.get_machine_arch() == elf.get_machine_arch()
            assert interpreter.header.e_type in ['ET_DYN', 'ET_EXEC']

        #Stack Executability
        executable_stack = False
        for elf_segment in elf.iter_segments():
            if elf_segment.header.p_type != 'PT_GNU_STACK':
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
        load_addr = 0

        for elf_segment in elf.iter_segments():
            if elf_segment.header.p_type != 'PT_LOAD':
                continue

            align = 0x1000 #elf_segment.header.p_align

            ELF_PAGEOFFSET = elf_segment.header.p_vaddr & (align-1)

            flags = elf_segment.header.p_flags
            memsz = elf_segment.header.p_memsz + ELF_PAGEOFFSET
            offset = elf_segment.header.p_offset - ELF_PAGEOFFSET
            filesz = elf_segment.header.p_filesz + ELF_PAGEOFFSET
            vaddr = elf_segment.header.p_vaddr - ELF_PAGEOFFSET
            memsz = cpu.memory._ceil(memsz)
            if base == 0 and elf.header.e_type == 'ET_DYN':
                assert vaddr == 0
                if addressbitsize == 32:
                    base = 0x56555000
                else:
                    base = 0x555555554000

            perms = perms_from_elf(flags)
            hint = base+vaddr
            if hint == 0:
                hint = None

            logger.debug("Loading elf offset: %08x addr:%08x %08x %s" %(offset, base+vaddr, base+vaddr+memsz, perms))
            base = cpu.memory.mmapFile(hint, memsz, perms, elf_segment.stream.name, offset) - vaddr

            if load_addr == 0 :
                load_addr = base + vaddr

            k = base + vaddr + filesz;
            if k > elf_bss :
                elf_bss = k;
            if (flags & 4) and end_code < k: #PF_X
                end_code = k
            if end_data < k:
                end_data = k
            k = base + vaddr + memsz
            if k > elf_brk:
                elf_brk = k

        elf_entry = elf.header.e_entry
        if elf.header.e_type == 'ET_DYN':
            elf_entry += load_addr
        entry = elf_entry
        real_elf_brk = elf_brk

        # We need to explicitly zero any fractional pages
        # after the data section (i.e. bss).  This would
        # contain the junk from the file that should not
        # be in memory
        #TODO:
        #cpu.write_bytes(elf_bss, '\x00'*((elf_bss | (align-1))-elf_bss))

        logger.debug("Zeroing main elf fractional pages. From %x to %x.", elf_bss, elf_brk)
        logger.debug("Main elf bss:%x"%elf_bss)
        logger.debug("Main elf brk %x:"%elf_brk)

	#FIXME Need a way to inspect maps and perms so
	#we can rollback all to the initial state after zeroing
        #if elf_brk-elf_bss > 0:
        #    saved_perms = cpu.mem.perms(elf_bss)
        #    cpu.memory.mprotect(cpu.mem._ceil(elf_bss), elf_brk-elf_bss, 'rw ')
        #    logger.debug("Zeroing main elf fractional pages (%d bytes)", elf_brk-elf_bss)
        #    cpu.write_bytes(elf_bss, ['\x00'] * (elf_brk-elf_bss))
        #    cpu.memory.mprotect(cpu.memory._ceil(elf_bss), elf_brk-elf_bss, saved_perms)


        if cpu.memory.access_ok(slice(elf_bss,elf_brk), 'w'):
            cpu.memory[elf_bss:elf_brk] = '\x00'*(elf_brk-elf_bss)
        else:
            logger.warning("Failing to zerify the trailing: elf_brk-elf_bss")

        stack_size = 0x21000

        if addressbitsize == 32:
            stack_top = 0xc0000000
        else:
            stack_top = 0x800000000000
        stack_base = stack_top - stack_size
        stack = cpu.memory.mmap(stack_base, stack_size, 'rwx', name='stack') + stack_size
        assert stack_top == stack

        reserved = cpu.memory.mmap(base+vaddr+memsz,0x1000000,'   ')
        interpreter_base = 0
        if interpreter is not None:
            base = 0
            elf_bss = 0
            end_code = 0
            end_data = 0
            elf_brk = 0
            entry = interpreter.header.e_entry
            for elf_segment in interpreter.iter_segments():
                if elf_segment.header.p_type != 'PT_LOAD':
                    continue
                align = 0x1000#elf_segment.header.p_align
                vaddr = elf_segment.header.p_vaddr
                filesz = elf_segment.header.p_filesz
                flags = elf_segment.header.p_flags
                offset = elf_segment.header.p_offset
                memsz = elf_segment.header.p_memsz

                ELF_PAGEOFFSET = (vaddr & (align-1))
                memsz = memsz + ELF_PAGEOFFSET
                offset = offset - ELF_PAGEOFFSET
                filesz = filesz + ELF_PAGEOFFSET
                vaddr = vaddr - ELF_PAGEOFFSET
                memsz = cpu.memory._ceil(memsz)

                if base == 0 and interpreter.header.e_type == 'ET_DYN':
                    assert vaddr == 0
                    total_size = self._interp_total_size(interpreter)
                    base = stack_base - total_size

                if base == 0:
                    assert vaddr == 0
                perms = perms_from_elf(flags)
                hint = base+vaddr
                if hint == 0:
                    hint = None

                base = cpu.memory.mmapFile(hint, memsz, perms, elf_segment.stream.name, offset)
                base -= vaddr
                logger.debug("Loading interpreter offset: %08x addr:%08x %08x %s%s%s" %(offset, base+vaddr, base+vaddr+memsz, (flags&1 and 'r' or ' '), (flags&2 and 'w' or ' '), (flags&4 and 'x' or ' ')))

                k = base + vaddr+ filesz;
                if k > elf_bss :
                    elf_bss = k;
                if (flags & 4) and end_code < k: #PF_X
                    end_code = k
                if end_data < k:
                    end_data = k
                k = base + vaddr+ memsz
                if k > elf_brk:
                    elf_brk = k

            if interpreter.header.e_type == 'ET_DYN':
                entry += base
            interpreter_base = base

            logger.debug("Zeroing interpreter elf fractional pages. From %x to %x.", elf_bss, elf_brk)
            logger.debug("Interpreter bss:%x"%elf_bss)
            logger.debug("Interpreter brk %x:"%elf_brk)

            cpu.memory.mprotect(cpu.memory._floor(elf_bss), elf_brk-elf_bss, 'rw ')
	    try:
	        cpu.memory[elf_bss:elf_brk] = '\x00'*(elf_brk-elf_bss)
	    except Exception, e:
	        logger.debug("Exception zeroing Interpreter fractional pages: %s"%str(e))
            #TODO #FIXME mprotect as it was before zeroing?


        #free reserved brk space
        cpu.memory.munmap(reserved, 0x1000000)

        #load vdso
        #vdso_addr = load_vdso(addressbitsize)

        cpu.STACK = stack
        cpu.PC = entry

        logger.debug("Entry point: %016x", entry)
        logger.debug("Stack start: %016x", stack)
        logger.debug("Brk: %016x", real_elf_brk)
        logger.debug("Mappings:")
        for m in str(cpu.memory).split('\n'):
            logger.debug("  %s", m)
        self.base = base
        self.elf_bss = elf_bss
        self.end_code = end_code
        self.end_data = end_data
        self.elf_brk = real_elf_brk

        at_random = cpu.push_bytes('A'*16)
        at_execfn = cpu.push_bytes(filename+'\x00')

        self.auxv = {
            'AT_PHDR'   : load_addr+elf.header.e_phoff, # Program headers for program
            'AT_PHENT'  : elf.header.e_phentsize,       # Size of program header entry
            'AT_PHNUM'  : elf.header.e_phnum,           # Number of program headers
            'AT_PAGESZ' : cpu.memory.page_size,         # System page size
            'AT_BASE'   : interpreter_base,             # Base address of interpreter
            'AT_FLAGS'  : elf.header.e_flags,           # Flags
            'AT_ENTRY'  : elf_entry,                    # Entry point of program
            'AT_UID'    : 1000,                         # Real uid
            'AT_EUID'   : 1000,                         # Effective uid
            'AT_GID'    : 1000,                         # Real gid
            'AT_EGID'   : 1000,                         # Effective gid
            'AT_CLKTCK' : 100,                          # Frequency of times()
            'AT_HWCAP'  : 0,                            # Machine-dependent hints about processor capabilities.
            'AT_RANDOM' : at_random,                    # Address of 16 random bytes.
            'AT_EXECFN' : at_execfn,                    # Filename of executable.
        }

    def _open(self, f):
        '''
        It opens a file on the given a file descriptor
        :rtype: int
        :param filename: pathname of the file to open.
        :param mode: file permissions mode.
        :return: a file description of the opened file.
        '''
        if None in self.files:
            fd = self.files.index(None)
            self.files[fd]=f
        else:
            fd = len(self.files)
            self.files.append(f)
        return fd

    def _close(self, fd):
        '''
        Closes a file descriptor
        :rtype: int
        :param fd: the file descriptor to close.
        :return: C{0} on success.
        '''
        self.files[fd] = None

    def _dup(self, fd):
        '''
        Duplicates a file descriptor
        :rtype: int
        :param fd: the file descriptor to close.
        :return: C{0} on success.
        '''
        return self._open(self.files[fd])

    def _is_open(self, fd):
        return fd >= 0 and fd < len(self.files) and self.files[fd] is not None

    def sys_umask(self, mask):
        '''
        umask - Set file creation mode mask

        :param int mask: New mask
        '''
        logger.debug("umask({:o})".format(mask))
        return os.umask(mask)

    def sys_chdir(self, path):
        '''
        chdir - Change current working directory
        :param int path: Pointer to path
        '''
        path_str = self.current.read_string(path)
        logger.debug("chdir({})".format(path_str))
        try:
            os.chdir(path_str)
            return 0
        except OSError as e:
            return e.errno

    def sys_lseek(self, fd, offset, whence):
        '''
        lseek - reposition read/write file offset

        The lseek() function repositions the file offset of the open file description associated
        with the file descriptor fd to the argument offset according to the directive whence


        :param self: current CPU.
        :param fd: a valid file descriptor
        :param offset: the offset in bytes
        :param whence: SEEK_SET: The file offset is set to offset bytes.
                       SEEK_CUR: The file offset is set to its current location plus offset bytes.
                       SEEK_END: The file offset is set to the size of the file plus offset bytes.

        :return: 0 (Success), or EBADF (fd is not a valid file descriptor or is not open)

         '''
        if not self._is_open(fd):
            logger.info("LSEEK: Not valid file descriptor on lseek. Returning EBADF")
            return -errno.EBADF

        if isinstance(self.files[fd], Socket):
            logger.info("LSEEK: Not valid file descriptor on lseek. Fd not seekable. Returning EBADF")
            return -errno.EBADF

        # Read the data and put in tin memory
        self.files[fd].seek(offset)
        #self.syscall_trace.append(("_seek", fd, offset, whence))

        logger.debug("LSEEK(%d, 0x%08x, %d)"%(fd, offset, whence))
        return 0

    def sys_read(self, fd, buf, count):
        data = ''
        if count != 0:
            if not self._is_open(fd):
                logger.info("READ: Not valid file descriptor on read. Returning EBADF")
                return -errno.EBADF

            # TODO check count bytes from buf
            if not buf in self.current.memory: # or not  self.current.memory.isValid(buf+count):
                logger.info("READ: buf points to invalid address. Returning EFAULT")
                return -errno.EFAULT

            if isinstance(self.files[fd],Socket) and self.files[fd].is_empty():
                return 0

            # Read the data and put in tin memory
            data = self.files[fd].read(count)
            self.syscall_trace.append(("_read", fd, data))
            self.current.write_bytes(buf, data)

        logger.debug("READ(%d, 0x%08x, %d, 0x%08x) -> <%s> (size:%d)"%(fd, buf, count, len(data), repr(data)[:min(count,10)],len(data)))
        return len(data)

    def sys_write(self, fd, buf, count):
        ''' write - send bytes through a file descriptor
          The write system call writes up to count bytes from the buffer pointed
          to by buf to the file descriptor fd. If count is zero, write returns 0
          and optionally sets *tx_bytes to zero.

          :param fd            a valid file descriptor
          :param buf           a memory buffer
          :param count         number of bytes to send
          :return: 0          Success
                    EBADF      fd is not a valid file descriptor or is not open.
                    EFAULT     buf or tx_bytes points to an invalid address.
        '''
        data = []
        cpu = self.current
        if count != 0:

            if not self._is_open(fd):
                logger.error("WRITE: Not valid file descriptor. Returning EBADFD %d", fd)
                return -errno.EBADF

            # TODO check count bytes from buf
            if buf not in cpu.memory or buf+count not in cpu.memory:
                logger.debug("WRITE: buf points to invalid address. Returning EFAULT")
                return -errno.EFAULT

            if fd > 2 and self.files[fd].is_full():
                cpu.PC -= cpu.instruction.size
                self.wait([],[fd],None)
                raise RestartSyscall()

            data = cpu.read_bytes(buf, count)
            self.files[fd].write(data)

            for line in ''.join([str(x) for x in data]).split('\n'):
                logger.debug("WRITE(%d, 0x%08x, %d) -> <%.48r>"%(fd, buf, count, line))
            self.syscall_trace.append(("_write", fd, data))
            self.signal_transmit(fd)

        return len(data)

    def sys_access(self, buf, mode):
        '''
        Checks real user's permissions for a file
        :rtype: int

        :param buf: a buffer containing the pathname to the file to check its permissions.
        :param mode: the access permissions to check.
        :return:
            -  C{0} if the calling process can access the file in the desired mode.
            - C{-1} if the calling process can not access the file in the desired mode.
        '''
        filename = ""
        for i in xrange(0,255):
            c = Operators.CHR(self.current.read_int(buf + i, 8))
            if c == '\x00':
                break
            filename += c

            #if path.isfile(PATH) and access(PATH, MODE):
            #    print "File exists and is readable"
            #else:
            #    print "Either file is missing or is not readable"
        logger.debug("access(%s, %x) -> %r", filename, mode, os.access(filename, mode))
        if os.access(filename, mode):
            return 0
        else:
            return -1

    def sys_newuname(self, old_utsname):
        '''
        Writes system information in the variable C{old_utsname}.
        :rtype: int
        :param old_utsname: the buffer to write the system info.
        :return: C{0} on success
        '''
        from datetime import datetime

        def pad(s):
            return s +'\x00'*(65-len(s))

        now = datetime.now().strftime("%a %b %d %H:%M:%S ART %Y")
        info =  (('sysname',    'Linux'),
                 ('nodename',   'ubuntu'),
                 ('release',    '4.4.0-77-generic'),
                 ('version',    '#98 SMP ' + now),
                 ('machine',    self._uname_machine),
                 ('domainname', ''))

        uname_buf = ''.join(pad(pair[1]) for pair in info)
        self.current.write_bytes(old_utsname, uname_buf)
        logger.debug("sys_newuname(...) -> %s", uname_buf)
        return 0

    def sys_brk(self, brk):
        '''
        Changes data segment size (moves the C{elf_brk} to the new address)
        :rtype: int
        :param brk: the new address for C{elf_brk}.
        :return: the value of the new C{elf_brk}.
        :raises error:
                    - "Error in brk!" if there is any error allocating the memory
        '''
        if brk != 0:
            assert brk > self.elf_brk
            mem = self.current.memory
            size = brk-self.elf_brk
            perms = mem.perms(self.elf_brk-1)
            if brk > mem._ceil(self.elf_brk):
                addr = mem.mmap(mem._ceil(self.elf_brk), size, perms)
                assert mem._ceil(self.elf_brk) == addr, "Error in brk!"
            self.elf_brk += size
        logger.debug("sys_brk(0x%08x) -> 0x%08x", brk, self.elf_brk)
        return self.elf_brk

    def sys_arch_prctl(self, code, addr):
        '''
        Sets architecture-specific thread state
        :rtype: int

        :param code: must be C{ARCH_SET_FS}.
        :param addr: the base address of the FS segment.
        :return: C{0} on success
        :raises error:
            - if C{code} is different to C{ARCH_SET_FS}
        '''
        ARCH_SET_GS = 0x1001
        ARCH_SET_FS = 0x1002
        ARCH_GET_FS = 0x1003
        ARCH_GET_GS = 0x1004
        assert code == ARCH_SET_FS
        self.current.FS=0x63
        self.current.set_descriptor(self.current.FS, addr, 0x4000, 'rw')
        logger.debug("sys_arch_prctl(%04x, %016x) -> 0", code, addr)
        return 0

    def sys_ioctl(self, fd, request, argp):
        if fd > 2:
            return self.files[fd].ioctl(request, argp)
        else:
            return -errno.EINVAL


    def sys_open(self, buf, flags, mode):
        '''
        :param buf: address of zero-terminated pathname
        :param flags: file access bits
        :param mode: file permission mode
        '''
        filename = self.current.read_string(buf)
        try:
            if os.path.abspath(filename).startswith('/proc/self'):
                if filename == '/proc/self/exe':
                    filename = os.abspath(self.program)
                else:
                    logger.info("FIXME!")
            mode = {os.O_RDWR: 'r+', os.O_RDONLY: 'r', os.O_WRONLY: 'w'}[flags&7]
            if filename in self.symbolic_files:
                logger.debug("%s file is considered symbolic" % filename)
                assert flags & 7 == os.O_RDWR or flags & 7 == os.O_RDONLY, (
                    "Symbolic files should be readable?")
                f = SymbolicFile(self.constraints, filename, mode)
            else:
                f = File(filename, mode) # todo modes, flags
            logger.debug("Opening file %s for %s real fd %d",
                         filename, mode, f.fileno())
        # FIXME(theo) generic exception
        except Exception as e:
            logger.info("Could not open file %s. Reason %s" % (filename, str(e)))
            return -1

        return self._open(f)

    def sys_rename(self, oldnamep, newnamep):
        '''
        Rename filename `oldnamep` to `newnamep`.

        :param int oldnamep: pointer to oldname
        :param int newnamep: pointer to newname
        '''
        oldname = self.current.read_string(oldnamep)
        newname = self.current.read_string(newnamep)

        ret = 0
        try:
            os.rename(oldname, newname)
        except OSError as e:
             ret = -e.errno

        logger.debug("sys_rename('{}', '{}') -> {}".format(oldname, newname, ret))

        return ret

    def sys_fsync(self, fd):
        '''
        Synchronize a file's in-core state with that on disk.
        '''

        ret = 0
        try:
            f = self.files[fd]
            if isinstance(f, Socket):
                ret = -errno.EINVAL
            else:
                f.sync()
        except IndexError:
            ret = -errno.EBADF

        logger.debug("sys_fsync({}) -> {}".format(fd, ret))

        return ret

    def sys_getpid(self, v):
        logger.debug("GETPID, warning pid modeled as concrete 1000")
        return 1000

    def sys_ARM_NR_set_tls(self, val):
        if hasattr(self, '_arm_tls_memory'):
            self.current.write_int(self._arm_tls_memory, val)
            self.current.set_arm_tls(val)
        return 0

    #Signals..
    def sys_kill(self, pid, sig):
        logger.debug("KILL, Ignoring Sending signal %d to pid %d", sig, pid )
        return 0

    def sys_rt_sigaction(self, signum, act,oldact):
        'Wrapper for sys_sigaction'
        return self.sys_sigaction(signum, act, oldact)

    def sys_sigaction(self, signum, act, oldact):
        logger.debug("SIGACTION, Ignoring changing signal handler for signal %d", signum)
        return 0

    def sys_rt_sigprocmask(self, cpu, how, newset, oldset):
        'Wrapper for sys_sigprocmask'
        return self.sys_sigprocmask(cpu, how, newset, oldset)

    def sys_sigprocmask(self, cpu, how, newset, oldset):
        logger.debug("SIGACTION, Ignoring changing signal mask set cmd:%d", how)
        return 0

    def sys_close(self, fd):
        '''
        Closes a file descriptor
        :rtype: int
        :param fd: the file descriptor to close.
        :return: C{0} on success.
        '''
        if fd > 0 :
            self._close(fd)
        logger.debug('sys_close(%d)', fd)
        return 0

    def sys_readlink(self, path, buf, bufsize):
        '''
        Read
        :rtype: int

        :param path: the "link path id"
        :param buf: the buffer where the bytes will be putted.
        :param bufsize: the max size for read the link.
        :todo: Out eax number of bytes actually sent | EAGAIN | EBADF | EFAULT | EINTR | errno.EINVAL | EIO | ENOSPC | EPIPE
        '''
        if bufsize <= 0:
            return -errno.EINVAL
        filename = self.current.read_string(path)
        if filename == '/proc/self/exe':
            data = os.path.abspath(self.program)
        else:
            data = os.readlink(filename)[:bufsize]
        self.current.write_bytes(buf, data)
        logger.debug("READLINK %d %x %d -> %s",path,buf,bufsize,data)
        return len(data)

    def sys_mprotect(self, start, size, prot):
        '''
        Sets protection on a region of memory. Changes protection for the calling process's
        memory page(s) containing any part of the address range in the interval [C{start}, C{start}+C{size}-1].
        :rtype: int

        :param start: the starting address to change the permissions.
        :param size: the size of the portion of memory to change the permissions.
        :param prot: the new access permission for the memory.
        :return: C{0} on success.
        '''
        perms = perms_from_protflags(prot)
        ret = self.current.memory.mprotect(start, size, perms)
        logger.debug("sys_mprotect(0x%016x, 0x%x, %s) -> %r (%r)", start, size, perms, ret, prot)
        return 0

    def sys_munmap(self, addr, size):
        '''
        Unmaps a file from memory. It deletes the mappings for the specified address range
        :rtype: int

        :param addr: the starting address to unmap.
        :param size: the size of the portion to unmap.
        :return: C{0} on success.
        '''
        self.current.memory.munmap(addr, size)
        return 0

    def sys_getuid(self):
        '''
        Gets user identity.
        :rtype: int

        :return: this call returns C{1000} for all the users.
        '''
        return 1000
    def sys_getgid(self):
        '''
        Gets group identity.
        :rtype: int

        :return: this call returns C{1000} for all the groups.
        '''
        return 1000
    def sys_geteuid(self):
        '''
        Gets user identity.
        :rtype: int

        :return: This call returns C{1000} for all the users.
        '''
        return 1000
    def sys_getegid(self):
        '''
        Gets group identity.
        :rtype: int

        :return: this call returns C{1000} for all the groups.
        '''
        return 1000


    def sys_readv(self, fd, iov, count):
        '''
        Works just like C{sys_read} except that data is read into multiple buffers.
        :rtype: int

        :param fd: the file descriptor of the file to read.
        :param iov: the buffer where the the bytes to read are stored.
        :param count: amount of C{iov} buffers to read from the file.
        :return: the amount of bytes read in total.
        '''
        cpu = self.current
        ptrsize = cpu.address_bit_size
        sizeof_iovec = 2 * (ptrsize // 8)
        total = 0
        for i in xrange(0, count):
            buf = cpu.read_int(iov + i * sizeof_iovec, ptrsize)
            size = cpu.read_int(iov + i * sizeof_iovec + (sizeof_iovec // 2), ptrsize)

            data = self.files[fd].read(size)
            total += len(data)
            cpu.write_bytes(buf, data)
            self.syscall_trace.append(("_read", fd, data))
            logger.debug("READV(%r, %r, %r) -> <%r> (size:%r)"%(fd, buf, size, data, len(data)))
        return total

    def sys_writev(self, fd, iov, count):
        '''
        Works just like C{sys_write} except that multiple buffers are written out.
        :rtype: int

        :param fd: the file descriptor of the file to write.
        :param iov: the buffer where the the bytes to write are taken.
        :param count: amount of C{iov} buffers to write into the file.
        :return: the amount of bytes written in total.
        '''
        cpu = self.current
        ptrsize = cpu.address_bit_size
        sizeof_iovec = 2 * (ptrsize // 8)
        total = 0
        for i in xrange(0, count):
            buf = cpu.read_int(iov + i * sizeof_iovec, ptrsize)
            size = cpu.read_int(iov + i * sizeof_iovec + (sizeof_iovec // 2), ptrsize)

            data = ""
            for j in xrange(0,size):
                data += Operators.CHR(cpu.read_int(buf + j, 8))
            logger.debug("WRITEV(%r, %r, %r) -> <%r> (size:%r)"%(fd, buf, size, data, len(data)))
            self.files[fd].write(data)
            self.syscall_trace.append(("_write", fd, data))
            total+=size
        return total

    def sys_set_thread_area(self, user_info):
        '''
        Sets a thread local storage (TLS) area. Sets the base address of the GS segment.
        :rtype: int

        :param user_info: the TLS array entry set corresponds to the value of C{u_info->entry_number}.
        :return: C{0} on success.
        '''
        n = self.current.read_int(user_info, 32)
        pointer = self.current.read_int(user_info + 4, 32)
        m = self.current.read_int(user_info + 8, 32)
        flags = self.current.read_int(user_info + 12, 32)
        assert n == 0xffffffff
        assert flags == 0x51  #TODO: fix
        self.current.GS=0x63
        self.current.set_descriptor(self.current.GS, pointer, 0x4000, 'rw')
        self.current.write_int(user_info, (0x63 - 3) / 8, 32)
        return 0

    def sys_getpriority(self, which, who):
        '''
        System call ignored.
        :rtype: int

        :return: C{0}
        '''
        logger.debug("Ignoring sys_get_priority")
        return 0

    def sys_setpriority(self, which, who, prio):
        '''
        System call ignored.
        :rtype: int

        :return: C{0}
        '''
        logger.debug("Ignoring sys_setpriority")
        return 0

    def sys_acct(self, path):
        '''
        System call not implemented.
        :rtype: int

        :return: C{-1}
        '''
        logger.debug("BSD account not implemented!")
        return -1

    def sys_exit(self, error_code):
        'Wrapper for sys_exit_group'
        return self.sys_exit_group(error_code)

    def sys_exit_group(self, error_code):
        '''
        Exits all threads in a process
        :raises Exception: 'Finished'
        '''
        procid = self.procs.index(self.current)
        self.sched()
        self.running.remove(procid)
        #self.procs[procid] = None
        logger.debug("EXIT_GROUP PROC_%02d %s", procid, error_code)
        if len(self.running) == 0 :
            raise ProcessExit(error_code)
        return error_code

    def sys_ptrace(self, request, pid, addr, data):
        logger.debug("sys_ptrace(%016x, %d, %016x, %016x) -> 0", request, pid, addr, data)
        return 0
    def sys_nanosleep(self, req, rem):
        logger.debug("sys_nanosleep(...)")
        return 0
    def sys_set_tid_address(self, tidptr):
        logger.debug("sys_set_tid_address(%016x) -> 0", tidptr)
        return 1000 #tha pid
    def sys_faccessat(self, dirfd, pathname, mode, flags):
        filename = self.current.read_string(pathname)
        logger.debug("sys_faccessat(%016x, %s, %x, %x) -> 0", dirfd, filename, mode, flags)
        return -1

    def sys_set_robust_list(self, head, length):
        logger.debug("sys_set_robust_list(%016x, %d) -> -1", head, length)
        return -1
    def sys_futex(self, uaddr, op, val, timeout, uaddr2, val3):
        logger.debug("sys_futex(...) -> -1")
        return -1
    def sys_getrlimit(self, resource, rlim):
        logger.debug("sys_getrlimit(%x, %x) -> -1",resource, rlim)
        return -1
    def sys_fadvise64(self, fd, offset, length, advice):
        logger.debug("sys_fadvise64(%x, %x, %x, %x) -> 0", fd, offset, length, advice)
        return 0
    def sys_gettimeofday(self, tv, tz):
        logger.debug("sys_gettimeofday(%x, %x) -> 0", tv, tz)
        return 0

    #Distpatchers...
    def syscall(self):
        '''
        Syscall dispatcher.
        '''

        index = self._syscall_abi.syscall_number()

        try:
            table = getattr(linux_syscalls, self.current.machine)
            name = table.get(index,None)
            implementation = getattr(self, name)
        except (AttributeError, KeyError):
            raise SyscallNotImplemented(self.current.address_bit_size, index, name)

        return self._syscall_abi.invoke(implementation)

    def sys_clock_gettime(self, clock_id, timespec):
        logger.info("sys_clock_time not really implemented")
	return 0

    def sys_time(self, tloc):
        import time
        t = time.time()
        if tloc != 0 :
            self.current.write_int(tloc, int(t), self.current.address_bit_size)
        return int(t)


    def sched(self):
        ''' Yield CPU.
            This will choose another process from the running list and change
            current running process. May give the same cpu if only one running
            process.
        '''
        if len(self.procs)>1:
            logger.debug("SCHED:")
            logger.debug("\tProcess: %r", self.procs)
            logger.debug("\tRunning: %r", self.running)
            logger.debug("\tRWait: %r", self.rwait)
            logger.debug("\tTWait: %r", self.twait)
            logger.debug("\tTimers: %r", self.timers)
            logger.debug("\tCurrent clock: %d", self.clocks)
            logger.debug("\tCurrent cpu: %d", self._current)

        if len(self.running) == 0:
            logger.debug("None running checking if there is some process waiting for a timeout")
            if all([x is None for x in self.timers]):
                raise Deadlock()
            self.clocks = min(filter(lambda x: x is not None, self.timers))+1
            self.check_timers()
            assert len(self.running) != 0, "DEADLOCK!"
            self._current = self.running[0]
            return
        next_index = (self.running.index(self._current) + 1) % len(self.running)
        next = self.running[ next_index ]
        if len(self.procs)>1:
            logger.debug("\tTransfer control from process %d to %d", self._current, next)
        self._current = next

    def wait(self, readfds, writefds, timeout):
        ''' Wait for file descriptors or timeout.
            Adds the current process in the correspondent waiting list and
            yield the cpu to another running process.
        '''
        logger.debug("WAIT:")
        logger.debug("\tProcess %d is going to wait for [ %r %r %r ]", self._current, readfds, writefds, timeout)
        logger.debug("\tProcess: %r", self.procs)
        logger.debug("\tRunning: %r", self.running)
        logger.debug("\tRWait: %r", self.rwait)
        logger.debug("\tTWait: %r", self.twait)
        logger.debug("\tTimers: %r", self.timers)


        for fd in readfds:
            self.rwait[fd].add(self._current)
        for fd in writefds:
            self.twait[fd].add(self._current)
        if timeout is not None:
            self.timers[self._current] = self.clocks + timeout
        procid = self._current
        #self.sched()
        next_index = (self.running.index(procid) + 1) % len(self.running)
        self._current = self.running[ next_index ]
        logger.debug("\tTransfer control from process %d to %d", procid, self._current)
        logger.debug( "\tREMOVING %r from %r. Current: %r",procid, self.running, self._current)
        self.running.remove(procid)
        if self._current not in self.running:
            logger.debug( "\tCurrent not running. Checking for timers...")
            self._current=None
            self.check_timers()

    def awake(self, procid):
        ''' Remove procid from waitlists and reestablish it in the running list '''
        logger.debug("Remove procid:%d from waitlists and reestablish it in the running list", procid)
        for wait_list in self.rwait:
            if procid in wait_list: wait_list.remove(procid)
        for wait_list in self.twait:
            if procid in wait_list: wait_list.remove(procid)
        self.timers[procid]=None
        self.running.append(procid)
        if self._current is None:
            self._current = procid

    def connections(self, fd):
        if fd in [0,1,2]:
            return None
        if fd%2:
            return fd + 1
        else:
            return fd - 1

    def signal_receive(self, fd):
        ''' Awake one process waiting to receive data on fd '''
        connections = self.connections
        if connections(fd) and self.twait[connections(fd)]:
            procid = random.sample(self.twait[connections(fd)], 1)[0]
            self.awake(procid)

    def signal_transmit(self, fd):
        ''' Awake one process waiting to transmit data on fd '''
        connection = self.connections(fd)
        if connection is None or connection >= len(self.rwait):
            return

        procs = self.rwait[connection]
        if procs:
            procid = random.sample(procs, 1)[0]
            self.awake(procid)

    def check_timers(self):
        ''' Awake process if timer has expired '''
        if self._current is None :
            #Advance the clocks. Go to future!!
            advance = min([self.clocks] + filter(lambda x: x is not None, self.timers)) +1
            logger.debug("Advancing the clock from %d to %d", self.clocks, advance)
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
        syscallret = None
        try:
            self.current.execute()
            self.clocks += 1
            if self.clocks % 10000 == 0:
                self.check_timers()
                self.sched()
        except (Interruption, Syscall) as e:
            try:
                syscallret = self.syscall()
            except RestartSyscall:
                pass


        return True


    #64bit syscalls

    def sys_newfstat(self, fd, buf):
        '''
        Determines information about a file based on its file descriptor.
        :rtype: int
        :param fd: the file descriptor of the file that is being inquired.
        :param buf: a buffer where data about the file will be stored.
        :return: C{0} on success.
        '''
        stat = self.files[fd].stat()

        def add(width, val):
            format = {2:'H',4:'L',8:'Q'}[width]
            return struct.pack('<'+format, val)

        def to_timespec(width, ts):
            'Note: this is a platform-dependent timespec (8 or 16 bytes)'
            return add(width, int(ts)) + add(width, int(ts % 1 * 1e9))

        # From linux/arch/x86/include/uapi/asm/stat.h
        # Numerous fields are native width-wide
        nw = self.current.address_bit_size / 8

        bufstat  = add(nw, stat.st_dev)     # long st_dev
        bufstat += add(nw, stat.st_ino)     # long st_ino
        bufstat += add(nw, stat.st_nlink)   # long st_nlink
        bufstat += add(4, stat.st_mode)     # 32 mode
        bufstat += add(4, stat.st_uid)      # 32 uid
        bufstat += add(4, stat.st_gid)      # 32 gid
        bufstat += add(4, 0)                # 32 _pad
        bufstat += add(nw, stat.st_rdev)    # long st_rdev
        bufstat += add(nw, stat.st_size)    # long st_size
        bufstat += add(nw, stat.st_blksize) # long st_blksize
        bufstat += add(nw, stat.st_blocks)  # long st_blocks
        bufstat += to_timespec(nw, stat.st_atime) # long   st_atime, nsec;
        bufstat += to_timespec(nw, stat.st_mtime) # long   st_mtime, nsec;
        bufstat += to_timespec(nw, stat.st_ctime) # long   st_ctime, nsec;

        logger.debug("sys_newfstat({}, ...) -> {} bytes".format(fd, len(bufstat)))

        self.current.write_bytes(buf, bufstat)
        return 0


    def sys_fstat64(self, fd, buf):
        '''
        Determines information about a file based on its file descriptor (for Linux 64 bits).
        :rtype: int
        :param fd: the file descriptor of the file that is being inquired.
        :param buf: a buffer where data about the file will be stored.
        :return: C{0} on success.
        :todo: Fix device number.
        '''
        stat = self.files[fd].stat()

        def add(width, val):
            format = {2:'H',4:'L',8:'Q'}[width]
            return struct.pack('<'+format, val)

        def to_timespec(ts):
            return struct.pack('<LL', int(ts), int(ts % 1 * 1e9))

        logger.debug("sys_fstat64 {}".format(fd))

        bufstat  = add(8, stat.st_dev)        # unsigned long long      st_dev;
        bufstat += add(4, 0)                  # unsigned char   __pad0[4];
        bufstat += add(4, stat.st_ino)        # unsigned long   __st_ino;
        bufstat += add(4, stat.st_mode)       # unsigned int    st_mode;
        bufstat += add(4, stat.st_nlink)      # unsigned int    st_nlink;
        bufstat += add(4, stat.st_uid)        # unsigned long   st_uid;
        bufstat += add(4, stat.st_gid)        # unsigned long   st_gid;
        bufstat += add(8, stat.st_rdev)       # unsigned long long st_rdev;
        bufstat += add(4, 0)                  # unsigned char   __pad3[4];
        bufstat += add(4, 0)                  # unsigned char   __pad3[4];
        bufstat += add(8, stat.st_size)       # long long       st_size;
        bufstat += add(8, stat.st_blksize)    # unsigned long   st_blksize;
        bufstat += add(8, stat.st_blocks)     # unsigned long long st_blocks;
        bufstat += to_timespec(stat.st_atime) # unsigned long   st_atime;
        bufstat += to_timespec(stat.st_mtime) # unsigned long   st_mtime;
        bufstat += to_timespec(stat.st_ctime) # unsigned long   st_ctime;
        bufstat += add(8, stat.st_ino)        # unsigned long long      st_ino;

        self.current.write_bytes(buf, bufstat)
        return 0

    def sys_newstat(self, fd, buf):
        '''
        Wrapper for stat64()
        '''
        return self.sys_stat64(fd, buf)

    def sys_stat64(self, path, buf):
        '''
        Determines information about a file based on its filename (for Linux 64 bits).
        :rtype: int
        :param path: the pathname of the file that is being inquired.
        :param buf: a buffer where data about the file will be stored.
        :return: C{0} on success.
        '''
        return self._stat(path, buf, True)

    def sys_stat32(self, path, buf):
        return self._stat(path, buf, False)

    def _stat(self, path, buf, is64bit):
        fd = self.sys_open(path, 0, 'r')
        if is64bit:
            ret = self.sys_fstat64(fd, buf)
        else:
            ret = self.sys_fstat(fd, buf)
        self.sys_close(fd)
        return ret

    def _arch_specific_init(self):
        assert self.arch in {'i386', 'amd64', 'armv7'}

        if self.arch == 'i386':
            self._uname_machine = 'i386'
        elif self.arch == 'amd64':
            self._uname_machine = 'x86_64'
        elif self.arch == 'armv7':
            self._uname_machine = 'armv71'
            self._init_arm_kernel_helpers()

        # Establish segment registers for x86 architectures
        if self.arch in {'i386', 'amd64'}:
            x86_defaults = { 'CS': 0x23, 'SS': 0x2b, 'DS': 0x2b, 'ES': 0x2b, }
            for reg, val in x86_defaults.iteritems():
                self.current.regfile.write(reg, val)

    @staticmethod
    def _interp_total_size(interp):
        '''
        Compute total load size of interpreter.

        :param ELFFile interp: interpreter ELF .so
        :return: total load size of interpreter, not aligned
        :rtype: int
        '''
        load_segs = filter(lambda x: x.header.p_type == 'PT_LOAD', interp.iter_segments())
        last = load_segs[-1]
        return last.header.p_vaddr + last.header.p_memsz


############################################################################
# Symbolic versions follows

class SLinux(Linux):
    """
    Builds a symbolic extension of a Linux OS

    :param str programs: path to ELF binary
    :param list argv: argv not including binary
    :param list envp: environment variables
    :param tuple[str] symbolic_files: files to consider symbolic
    """
    def __init__(self, programs, argv=None, envp=None, symbolic_files=None):
        argv = [] if argv is None else argv
        envp = [] if envp is None else envp
        symbolic_files = [] if symbolic_files is None else symbolic_files

        self._constraints = ConstraintSet()
        self.random = 0
        self.symbolic_files = symbolic_files
        super(SLinux, self).__init__(programs, argv, envp)

    def _mk_proc(self, arch):
        if arch in {'i386', 'armv7'}:
            mem = SMemory32(self.constraints)
        else:
            mem = SMemory64(self.constraints)

        return CpuFactory.get_cpu(mem, arch)

    @property
    def constraints(self):
        return self._constraints

    #marshaling/pickle
    def __getstate__(self):
        state = super(SLinux, self).__getstate__()
        state['constraints'] = self.constraints
        state['random'] = self.random
        state['symbolic_files'] = self.symbolic_files
        return state

    def __setstate__(self, state):
        self._constraints = state['constraints']
        self.random = state['random']
        self.symbolic_files = state['symbolic_files']
        super(SLinux, self).__setstate__(state)


    #Dispatchers...

    def sys_read(self, fd, buf, count):
        if issymbolic(fd):
            logger.debug("Ask to read from a symbolic file descriptor!!")
            raise ConcretizeArgument(0)

        if issymbolic(buf):
            logger.debug("Ask to read to a symbolic buffer")
            raise ConcretizeArgument(1)

        if issymbolic(count):
            logger.debug("Ask to read a symbolic number of bytes ")
            raise ConcretizeArgument(2)

        return super(SLinux, self).sys_read(fd, buf, count)


    def sys_fstat(self, fd, buf):
        '''
        Determines information about a file based on its file descriptor.
        :rtype: int
        :param fd: the file descriptor of the file that is being inquired.
        :param buf: a buffer where data about the file will be stored.
        :return: C{0} on success.
        '''
        stat = self.files[fd].stat()

        def add(width, val):
            format = {2:'H',4:'L',8:'Q'}[width]
            return struct.pack('<'+format, val)

        def to_timespec(ts):
            return struct.pack('<LL', int(ts), int(ts % 1 * 1e9))

        logger.debug("sys_fstat {}".format(fd))

        bufstat  = add(8, stat.st_dev)    # dev_t st_dev;
        bufstat += add(4, 0)              # __pad1
        bufstat += add(4, stat.st_ino)    # unsigned long  st_ino;
        bufstat += add(4, stat.st_mode)   # unsigned short st_mode;
        bufstat += add(4, stat.st_nlink)  # unsigned short st_nlink;
        bufstat += add(4, stat.st_uid)    # unsigned short st_uid;
        bufstat += add(4, stat.st_gid)    # unsigned short st_gid;
        bufstat += add(4, stat.st_rdev)   # unsigned long  st_rdev;
        bufstat += add(4, stat.st_size)   # unsigned long  st_size;
        bufstat += add(4, stat.st_blksize)# unsigned long  st_blksize;
        bufstat += add(4, stat.st_blocks) # unsigned long  st_blocks;
        bufstat += to_timespec(stat.st_atime)  # unsigned long  st_atime;
        bufstat += to_timespec(stat.st_mtime)  # unsigned long  st_mtime;
        bufstat += to_timespec(stat.st_ctime)  # unsigned long  st_ctime;
        bufstat += add(4, 0)              # unsigned long  __unused4;
        bufstat += add(4, 0)              # unsigned long  __unused5;

        self.current.write_bytes(buf, bufstat)
        return 0

    def sys_mmap_pgoff(self, address, size, prot, flags, fd, offset):
        'Wrapper for mmap2'
        return self.sys_mmap2(address, size, prot, flags, fd, offset)

    def sys_mmap2(self, address, size, prot, flags, fd, offset):
        '''
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
        '''
        return self.sys_mmap(address, size, prot, flags, fd, offset*0x1000)

    def sys_mmap(self, address, size, prot, flags, fd, offset):
        '''
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
        '''

        if address == 0:
            address = None

        cpu = self.current
        if flags & 0x10 !=0 :
            cpu.memory.munmap(address,size)

        perms = perms_from_protflags(prot)

        if (flags & 0x20 != 0):
            result = cpu.memory.mmap(address, size, perms)
        elif fd == 0:
            assert offset == 0
            result = cpu.memory.mmap(address, size, perms)
            data = self.files[fd].read(size)
            cpu.write_bytes(result,data)
        else:
            #FIXME Check if file should be symbolic input and do as with fd0
            result = cpu.memory.mmapFile(address, size, perms, self.files[fd].name, offset)

        actually_mapped = '0x{:016x}'.format(result)
        if address is None or result != address:
            address = address or 0
            actually_mapped += ' [requested: 0x{:016x}]'.format(address)

        if (flags & 0x10 !=0) and result != address:
            cpu.memory.munmap(result, size)
            result = -1

        logger.debug("sys_mmap(%s, 0x%x, %s, %x, %d) - (0x%x)", actually_mapped, size, perms, flags, fd, result)
        return result


    def sys_write(self, fd, buf, count):
        if issymbolic(fd):
            logger.debug("Ask to write to a symbolic file descriptor!!")
            raise ConcretizeArgument(0)

        if issymbolic(buf):
            logger.debug("Ask to write to a symbolic buffer")
            raise ConcretizeArgument(1)

        if issymbolic(count):
            logger.debug("Ask to write a symbolic number of bytes ")
            raise ConcretizeArgument(2)

        return super(SLinux, self).sys_write(fd, buf, count)

class DecreeEmu(object):

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
            raise ConcretizeArgument(0)

        if issymbolic(count):
            logger.info("Ask to read a symbolic number of random bytes ")
            raise ConcretizeArgument(1)

        if issymbolic(rnd_bytes):
            logger.info("Ask to return rnd size to a symbolic address ")
            raise ConcretizeArgument(2)

        data = []
        for i in xrange(count):
            value = cgcrandom.stream[DecreeEmu.RANDOM]
            data.append(value)
            DecreeEmu.random += 1

        cpu = platform.current
        cpu.write(buf, data)
        if rnd_bytes:
            cpu.store(rnd_bytes, len(data), 32)
        logger.info("RANDOM(0x%08x, %d, 0x%08x) -> %d", buf, count, rnd_bytes, len(data))
        return 0
