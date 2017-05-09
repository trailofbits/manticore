import cgcrandom
import weakref
import sys, os, struct
from ..core.memory import Memory, MemoryException, SMemory32, Memory32
from ..core.smtlib import Expression, Operators, solver
# TODO use cpu factory
from ..core.cpu.x86 import I386Cpu, Sysenter, I386StdcallAbi
from ..core.cpu.abstractcpu import Interruption, Syscall, \
        ConcretizeRegister, ConcretizeArgument, IgnoreAPI
from ..core.executor import ForkState, SyscallNotImplemented
from ..utils.helpers import issymbolic
from ..platforms.platform import Platform

from ..binary.pe import minidump

from contextlib import closing
import StringIO
import logging
import random
from windows_syscalls import syscalls_num
logger = logging.getLogger("PLATFORM")

class ProcessExit(Exception):
    def __init__(self, code):
        super(ProcessExit, self).__init__("Process exited correctly. Code: %s"%code)

class RestartSyscall(Exception):
    pass

class Deadlock(Exception):
    pass

class SymbolicAPIArgument(Exception):
    pass

class SymbolicSyscallArgument(ConcretizeRegister):
    def __init__(self, number, message='Concretizing syscall argument', policy='SAMPLED'):
        reg_name = ['EBX', 'ECX', 'EDX', 'ESI', 'EDI', 'EBP' ][number]
        super(SymbolicSyscallArgument, self).__init__(reg_name, message, policy)

#FIXME Consider moving this to executor.state?
def toStr(state, value):
    if issymbolic(value):
        minmax = solver.get_all_values(state.constraints, value, maxcnt=2, silent=True)
        if len(minmax) > 1:
            return '?'*(value.size/8) + ' ' + repr(minmax)
        else:
            value = minmax[0]
    return '{:08x}'.format(value)

class Windows(Platform):
    '''
    A simple Windows Operating System Platform.
    This class emulates some Windows system calls
    '''

    STATUS_SUCCESS = 0x0


    # handles are always 4 byte aligned
    LATEST_HANDLE = 0x10000
    REG_KEY_HANDLE = 0x13370

    def NT_SUCCESS(self, code):
        return code < 0x80000000

    def _mk_memory(self):
        return Memory32()

    def __init__(self, path, additional_context = None, snapshot_folder=None):
        '''
        Builds a Windows OS platform
        '''
        super(Windows, self).__init__(path)

        self.clocks = 0
        self.files = [] 
        self.syscall_trace = []

        #This should be moved to a "load_dump" or "load_state" function
        md = minidump.MiniDump(path)
        assert md.get_architecture() == "x86"

        major, minor = map(int, md.version.split(' ')[0].split('.'))
        if major == 6:
            self.flavor = "Windows7SP%d"%minor
            if minor >= 2:
                self.flavor = "Windows8"
                if minor > 2:
                   self.flavor = "Windows8.%d"%(minor-2)
        elif major == 10:
            self.flavor = "Windows10SP%d"%minor
        else:
            raise NotImplementedError("Windows version {}.{} not supported".format(major, minor))
        logger.info('Initializing %s platform', self.flavor)

        # Setting up memory maps
        memory = self._mk_memory()
        data = md.get_memory_data()
        query = md.get_memory_map()


        if snapshot_folder is None:
            for addr in sorted(data.keys()):
                perms, size = query[addr]
                memory.mmap(addr&0xffffffff, size, perms, data_init=data[addr])
        else:
            filename = os.path.join(snapshot_folder, 'memory.bin')
            with open(filename, 'w+') as f:
                pos = 0
                for addr in sorted(data.keys()):
                    perms, size = query[addr]
                    if pos & 0xfff !=0:
                        pos = (pos & ~0xfff )+0x1000
                        f.seek( pos )
                    f.write(data[addr])
                    pos+=size

            pos = 0
            for addr in sorted(data.keys()):
                perms, size = query[addr]
                if pos & 0xfff !=0:
                    pos = (pos & ~0xfff )+0x1000
                memory.mmapFile(addr&0xffffffff, size, perms, filename, offset=pos)
                pos+=size


        if (additional_context and 'memory' in additional_context):
            for address, value in additional_context['memory'].iteritems():
                t = iter(value.encode('hex'))
                decoded = " ".join(a+b for a,b in zip(t, t))
                logger.info('Overwriting memory at {:#08x} with bytes {}'.format(address, decoded))
                try:
                    memory.write(address, value)
                except MemoryException as e:
                    logger.info('Memory overwrite failed: {}'.format(e))
        logger.info('Total memory used: %d bytes', sum([size for (_, size) in query.values()]))

        selectedThreadId = md.get_threads()[0].ThreadId
        exc = md.get_exception_info()
        if exc is not None:
            selectedThreadId = exc.ThreadId

        #Load threads and setup waiting lists
        self.running = []
        self.procs = []
        for thread in md.get_threads():
            cxt = md.get_register_context_by_tid(thread.ThreadId)
            #Let's just ignore all extra threads for now
            if selectedThreadId != thread.ThreadId:
                continue

            cpu = I386Cpu(memory)
            cpu.EIP=cxt.Eip
            cpu.ESP=cxt.Esp
            cpu.EBP=cxt.Ebp
            cpu.EAX=cxt.Eax
            cpu.EBX=cxt.Ebx
            cpu.ECX=cxt.Ecx
            cpu.EDX=cxt.Edx
            cpu.ESI=cxt.Esi
            cpu.EDI=cxt.Edi
            cpu.FS=cxt.SegFs
            if (additional_context and 'registers' in additional_context):
                for name, value in additional_context['registers'].iteritems():
                    setattr(cpu, name, value)
                    logger.info('Overriding register {} with new value {:#x}'.format(name, value)) #DEBUG

            # Setting up segmentation for FS
            cpu.set_descriptor(cpu.FS, thread.Teb, 0x4000, 'rw')

            self.procs.append(cpu)
            if selectedThreadId == thread.ThreadId:
                self.running.append(self.procs.index(cpu))
        

        self._function_abi = I386StdcallAbi(self.procs[0])
        # open standard files stdin, stdout, stderr
        logger.info("Not Opening any file")

        nprocs = len(self.procs)
        assert nprocs > 0
        assert len(self.running) == 1, "For now lets consider only one thread running"
        self._current = self.running[0]
        

    @property
    def current(self):
        return self.procs[self._current]

    def __getstate__(self):
        state = {}
        state['clocks'] = self.clocks
        state['procs'] = self.procs
        state['current'] = self._current
        state['running'] = self.running
        state['syscall_trace'] = self.syscall_trace
        state['files'] = self.files
        state['flavor'] = self.flavor
        state['function_abi'] = self._function_abi

        return state

    def __setstate__(self, state):
        """
        :todo: some asserts
        :todo: fix deps? (last line)
        """
        self.procs = state['procs']
        self._current = state['current']
        self.running = state['running']
        self.clocks = state['clocks']
        self.syscall_trace = state['syscall_trace']
        self.files = state['files']
        self.flavor = state['flavor']
        self._function_abi = state['function_abi']

    def _read_string(self, cpu, buf):
        """
        Reads a null terminated concrete buffer form memory
        :todo: FIX. move to cpu or memory 
        """
        filename = ""
        for i in xrange(0,1024):
            c = Operators.CHR(cpu.read_int(buf+i,8))
            if c == '\x00':
                break
            filename += c
        return filename


    def load(self, cpu, filename):
        ''' 
        Loads PE program in memory and prepares the initial CPU state and the stack.
         :param filename: pathname of the file to be executed.
        '''
        raise Exception("Not Implementes")

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

    def sysenter(self, cpu):
        ''' 
        32 bit dispatcher.
        :param cpu: current CPU.
        _terminate, transmit, receive, fdwait, allocate, deallocate and random
        '''
        if not cpu.EAX in syscalls_num[self.flavor]:
            raise SyscallNotImplemented("32 bit %s WINDOWS system call number %s (UNKNOWN) Not Implemented" % (self.flavor, cpu.EAX))

        syscall_name = syscalls_num[self.flavor][cpu.EAX]
        if not hasattr(self, syscall_name):
            raise SyscallNotImplemented("32 bit %s WINDOWS system call number %s (%s) Not Implemented" % (self.flavor, cpu.EAX, syscall_name))
        func = getattr(self, syscall_name)

        logger.debug("SYSCALL32: %s (nargs: %d)", func.func_name, func.func_code.co_argcount)
        nargs = func.func_code.co_argcount
        args = [ ]
        for i in range(nargs-1):
            args.append(cpu.read_int(cpu.EDX+(i+2)*4, 32))
        cpu.EAX = func(*args)


    def sched(self):
        ''' Yield CPU.
            This will choose another process from the RUNNNIG list and change
            current running process. May give the same cpu if only one running
            proccess.
        '''
        if len(self.procs)>1:
            logger.info("SCHED:")
            logger.info("\tProcess: %r", self.procs)
            logger.info("\tRunning: %r", self.running)
            logger.info("\tCurrent cpu: %d", self._current)

        if len(self.running) == 0:
            logger.info("None running checking if there is some process waiting for a timeout")
            assert len(self.running) != 0, "DEADLOCK!"

        next_index = (self.running.index(self._current) + 1) % len(self.running)
        next = self.running[ next_index ]
        if len(self.procs) > 1:
            logger.info("\tTransfer control from process %d to %d", self._current, next)
        self._current = next

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
                self.sched()
        except Sysenter as e:
            try:
                e = None
                self.sysenter(self.current)
            except RestartSyscall:
                pass

        return True

    def NtWriteFile(self, FileHandle, Event, ApcRoutine, ApcContext, IoStatusBlock, Buffer, Length, ByteOffset, Key):
        logger.info("NtWriteFile(%s, %s, %s, %s, %s, %s, %s, %s, %s)", 
                toStr(self, FileHandle), 
                toStr(self, Event), 
                toStr(self, ApcRoutine), 
                toStr(self, ApcContext), 
                toStr(self, IoStatusBlock), 
                toStr(self, Buffer), 
                toStr(self, Length), 
                toStr(self, ByteOffset), 
                toStr(self, Key))
        return Windows.STATUS_SUCCESS 
        
    def NtReleaseKeyedEvent(self, KeyedEventHandle, Key, Alertable, Timeout):
        logger.info("NtReleaseKeyedEvent(%s, %s, %s, %s)", 
                toStr(self, KeyedEventHandle),
                toStr(self, Key),
                toStr(self, Alertable),
                toStr(self, Timeout))
        return Windows.STATUS_SUCCESS 

    def NtQueryPerformanceCounter(self, PerformanceCounter, PerformanceFrequency):
        """ PerformanceCounter and PerformanceFrequency are 64-bit integers"""

        logger.info("NtQueryPerformanceCounter(%s, %s)",
                toStr(self, PerformanceCounter), 
                toStr(self, PerformanceFrequency))

        cpu = self.current
        cpu.write_int(PerformanceCounter, self.clocks, 64)
        if PerformanceFrequency:
            cpu.write_int(PerformanceFrequency, 1000, 64)

        return Windows.STATUS_SUCCESS 

    def NtClose(self, Handle):

        logger.info("NtClose(%s)", toStr(self, Handle))

        return Windows.STATUS_SUCCESS 

    def NtFreeVirtualMemory(self, ProcessHandle, BaseAddress, RegionSize, FreeType):
        logger.info("""ZwFreeVirtualMemory(
    _In_    HANDLE  ProcessHandle: {},
    _Inout_ PVOID   *BaseAddress: {},
    _Inout_ PSIZE_T RegionSize: {},
    _In_    ULONG   FreeType: {});""".format(
                  toStr(self, ProcessHandle),
                  toStr(self, BaseAddress),
                  toStr(self, RegionSize),
                  toStr(self, FreeType)))

        return Windows.STATUS_SUCCESS 

    def _fileHandle(self, filename):
        """ Get a file handle for a file name, or return a new fake handle"""
        self.LATEST_HANDLE += 4
        return self.LATEST_HANDLE

    def _getRegHandle(self, regkey):
        r = self.REG_KEY_HANDLE
        self.REG_KEY_HANDLE += 4
        return r

    def NtOpenFile(self, FileHandle, DesiredAccess, ObjectAttributes, IoStatusBlock, ShareAccess, OpenOptions):

        #TODO: extract name from ObjectAttributes

        logger.info("""NtOpenFile(
    _Out_ PHANDLE            FileHandle: {},
    _In_  ACCESS_MASK        DesiredAccess: {},
    _In_  POBJECT_ATTRIBUTES ObjectAttributes: {},
    _Out_ PIO_STATUS_BLOCK   IoStatusBlock: {},
    _In_  ULONG              ShareAccess: {},
    _In_  ULONG              OpenOptions: {});""".format(
        toStr(self, FileHandle),
        toStr(self, DesiredAccess),
        toStr(self, ObjectAttributes),
        toStr(self, IoStatusBlock),
        toStr(self, ShareAccess),
        toStr(self, OpenOptions)))

        fh = self._fileHandle(None)
        self.current.write_int(FileHandle, fh, 32)

        return Windows.STATUS_SUCCESS


############################################################################
# Symbolic versions follows

class SWindows(Windows):
    '''
    A symbolic extension of a Decree Operating System Platform.
    '''
    def __init__(self, constraints, path, additional_context=None, snapshot_folder=None):
        '''
        Builds a symbolic extension of a Decree OS
        :param constraints: a constraints set.
        :param path: path to minidump to load.
        :param additional_context: optional object for overriding data read from minidump, e.g., initial register values.
        '''
        self._constraints =  constraints
        super(SWindows, self).__init__(path, additional_context, snapshot_folder)

    def _mk_memory(self):
        return SMemory32(self.constraints)

    @property
    def constraints(self):
        return self._constraints

    #marshaling/pickle
    def __getstate__(self):
        state = super(SWindows, self).__getstate__()
        state['constraints'] = self.constraints
        return state

    def __setstate__(self, state):
        self._constraints = state['constraints']
        super(SWindows, self).__setstate__(state)


def readStringFromPointer(state, cpu, ptr, utf16, max_symbols=8):

    if issymbolic(ptr):
        ptrs = solver.get_all_values(state.constraints, ptr, maxcnt=2, silent=True)
        if len(ptrs) == 1:
            ptr = ptrs[0]
        else:
            raise SymbolicAPIArgument()

    if ptr == 0:
        # this happens a lot, just handle it
        return ""

    concrete_str = ""
    i = 0

    if utf16:
        width = 16
    else:
        width = 8

    while True:
        # read a char
        value = cpu.read_int(ptr+i, width)

        # ooh, a symbolic char
        if issymbolic(value):
            # how symbolic is it?
            vals = solver.get_all_values(state.constraints, value, maxcnt=max_symbols, silent=True)
            if len(vals) == 1:
                # effectively concrete
                value = vals[0]
                if value == 0:
                    break
                concrete_str += Operators.CHR(value)
            elif len(vals) < max_symbols:
                concrete_str += '?'
            else:
                # this could be a bug!
                msg = "Detected Symbolic String (prefix: {})".format(concrete_str)
                raise MemoryException(msg, 0xFFFFFFFF)
        # if its null, bail
        elif value == 0:
            break
        else:
            concrete_str += Operators.CHR(value)

        i += (width/8)

    return concrete_str

class ntdll(object):

    @staticmethod
    def NtWriteFile(platform, FileHandle, Event, ApcRoutine, ApcContext, IoStatusBlock, Buffer, Length, ByteOffset, Key):
        return platform.NtWriteFile(FileHandle, Event, ApcRoutine, ApcContext, IoStatusBlock, Buffer, Length, ByteOffset, Key)
 
    @staticmethod
    def NtReleaseKeyedEvent(platform, KeyedEventHandle, Key, Alertable, Timeout):
        return platform.NtReleaseKeyedEvent(KeyedEventHandle, Key, Alertable, Timeout)

    @staticmethod
    def NtQueryPerformanceCounter(platform, PerformanceCounter, PerformanceFrequency):
        return platform.NtQueryPerformanceCounter(PerformanceCounter, PerformanceFrequency)

    @staticmethod
    def NtClose(platform, Handle):
        return platform.NtClose(Handle)

    @staticmethod
    def RtlAllocateHeap(platform, handle, flags, size):
        if issymbolic(size):
            logger.info("RtlAllcoateHeap({}, {}, SymbolicSize); concretizing size".format(str(handle), str(flags)) )
            raise ConcretizeArgument(2)
        else:
            raise IgnoreAPI("RtlAllocateHeap({}, {}, {:08x})".format(str(handle), str(flags), size))

    @staticmethod
    def RtlpReportHeapFailure(platform):
        raise MemoryException("Heap Failure Detected via RtlpReportHeapFailure!", 0xFFFFFFFF)

    @staticmethod
    def RtlpLogHeapFailure(platform):
        raise MemoryException("Heap Failure Detected via RtlpLogHeapFailure!", 0xFFFFFFFE)


class kernel32(object):

    @staticmethod
    def RegOpenKeyExW(platform, hKey, lpSubKey, ulOptions, samDesired, phkResult):
        return kernel32._RegOpenKeyEx(platform, True, hKey, lpSubKey, ulOptions, samDesired, phkResult)

    @staticmethod
    def RegOpenKeyExA(platform, hKey, lpSubKey, ulOptions, samDesired, phkResult):
        return kernel32._RegOpenKeyEx(platform, False, hKey, lpSubKey, ulOptions, samDesired, phkResult)

    @staticmethod
    def _RegOpenKeyEx(platform, utf16, hKey, lpSubKey, ulOptions, samDesired, phkResult):
        """LONG WINAPI RegOpenKeyEx(
           _In_     HKEY    hKey,
           _In_opt_ LPCTSTR lpSubKey,
           _In_     DWORD   ulOptions,
           _In_     REGSAM  samDesired,
           _Out_    PHKEY   phkResult
           );
            Detect symbolic registry access. Attempt to simulate fake registry opening """

        cpu = platform.current
        myname = "RegOpenKeyEx{}".format(utf16 and "W" or "A")

        try:
            key_str = readStringFromPointer(platform, cpu, lpSubKey, utf16)
        except MemoryException as me:
            raise MemoryException("{}: {}".format(myname, me.cause), 0xFFFFFFFF)
        except SymbolicAPIArgument:
            raise ConcretizeArgument(1)

        logger.info("{}({}, [{}], {}, {}, {})".format(
            myname,
            str(hKey), key_str, str(ulOptions), str(samDesired),
            str(phkResult)))

        if issymbolic(phkResult):

            #Check if the symbol has a single solution.
            values = solver.get_all_values(platform.constraints, phkResult, maxcnt=2, silent=True)
            if len(values) == 1:
                phkResult = values[0]

        if issymbolic(phkResult):

            if solver.can_be_true(platform.constraints, phkResult==0):
                raise ForkState(phkResult==0)
            else:
                cpu.write_int(phkResult, platform._getRegHandle(key_str), 32)
                return 0

        elif phkResult != 0:
            cpu.write_int(phkResult, platform._getRegHandle(key_str), 32)
            return 0
        else:
            raise IgnoreAPI("{}({}, [{}], {}, {}, {})".format(myname,
                str(hKey), key_str, str(ulOptions), str(samDesired),
                str(phkResult)))

    @staticmethod
    def RegCreateKeyExW(platform, hkey, lpSubKey, Reserved, lpClass, dwOptions,
            samDesired, lpSecurityAttributes, phkResult, lpdwDisposition):
        return kernel32._RegCreateKeyEx(platform, True, hkey, lpSubKey, Reserved, lpClass, dwOptions,
            samDesired, lpSecurityAttributes, phkResult, lpdwDisposition)

    @staticmethod
    def RegCreateKeyExA(platform, hkey, lpSubKey, Reserved, lpClass, dwOptions,
            samDesired, lpSecurityAttributes, phkResult, lpdwDisposition):
        return kernel32._RegCreateKeyEx(platform, False, hkey, lpSubKey, Reserved, lpClass, dwOptions,
            samDesired, lpSecurityAttributes, phkResult, lpdwDisposition)

    @staticmethod
    def _RegCreateKeyEx(platform, utf16, hKey, lpSubKey, Reserved, lpClass, dwOptions,
            samDesired, lpSecurityAttributes, phkResult, lpdwDisposition):
        """ LONG WINAPI RegCreateKeyEx(
          _In_       HKEY                  hKey,
          _In_       LPCTSTR               lpSubKey,
          _Reserved_ DWORD                 Reserved,
          _In_opt_   LPTSTR                lpClass,
          _In_       DWORD                 dwOptions,
          _In_       REGSAM                samDesired,
          _In_opt_   LPSECURITY_ATTRIBUTES lpSecurityAttributes,
          _Out_      PHKEY                 phkResult,
          _Out_opt_  LPDWORD               lpdwDisposition
        );"""
        cpu = platform.current
        myname = "RegCreateKeyEx{}".format(utf16 and "W" or "A")

        try:
            key_str = readStringFromPointer(platform, cpu, lpSubKey, utf16)
        except MemoryException as me:
            raise MemoryException("{}: {}".format(myname, me.cause), 0xFFFFFFFF)
        except SymbolicAPIArgument:
            raise ConcretizeArgument(1)

        logger.info("{}({}, [{}], {}, {}, {}, {}, {}, {}, {})".format(myname,
            str(hKey), key_str, str(Reserved), str(lpClass), str(dwOptions), 
            str(lpSecurityAttributes), str(samDesired), str(phkResult), str(lpdwDisposition)))

        if issymbolic(phkResult):

            #Check if the symbol has a single solution.
            values = solver.get_all_values(platform.constraints, phkResult, maxcnt=2, silent=True)
            if len(values) == 1:
                phkResult = values[0]

        if issymbolic(phkResult):

            if solver.can_be_true(platform.constraints, phkResult==0):
                raise ForkState(phkResult==0)
            else:
                cpu.write_int(phkResult, platform._getRegHandle(key_str), 32)
                return 0

        elif phkResult != 0:
            cpu.write_int(phkResult, platform._getRegHandle(key_str), 32)
            return 0
        else:
            raise IgnoreAPI("{}({}, [{}], {}, {}, {}, {}, {}, {}, {})".format(myname,
                str(hKey), key_str, str(Reserved), str(lpClass), str(dwOptions), 
                str(lpSecurityAttributes), str(samDesired), str(phkResult), str(lpdwDisposition)))

    @staticmethod
    def HeapAlloc(platform, handle, flags, size):
        ntdll.RtlAllocateHeap(platform, handle, flags, size)

    # TODO: move this to Windows class if we ever
    # implement a real handle table
    @staticmethod
    def GetStdHandle(platform, nStdHandle):
        logger.info("GetStdHandle(%x)", nStdHandle)
        # ignore nStdHandle -- just return a valid value
        STD_INPUT_HANDLE = -10
        STD_OUTPUT_HANDLE = -11
        STD_ERROR_HANDLE = -12

        if issymbolic(nStdHandle):

            #Check if the symbol has a single solution.            
            values = solver.get_all_values(platform.constraints, nStdHandle, maxcnt=2, silent=True)
            if len(values) == 1:
                nStdHandle = values[0]
            else:
                #potentially multiple values. Fork on each one.
                if nStdHandle.solver.canBe(nStdHandle, STD_INPUT_HANDLE):
                    raise ForkState(nStdHandle==STD_INPUT_HANDLE)

                if nStdHandle.solver.canBe(nStdHandle, STD_OUTPUT_HANDLE):
                    raise ForkState(nStdHandle==STD_OUTPUT_HANDLE)

                if nStdHandle.solver.canBe(nStdHandle, STD_ERROR_HANDLE):
                    raise ForkState(nStdHandle==STD_ERROR_HANDLE)
                #here nStdHandle is symbolic and not in [ STD_INPUT_HANDLE, STD_OUTPUT_HANDLE, STD_ERROR_HANDLE ]
                #Symbolic value can be different from all STD_..._HANDLE
                return -1 # INVALID_HANDLE_VALUE

        elif nStdHandle == STD_INPUT_HANDLE:
            return 0xFF4 # arbitrary valid handle
        elif nStdHandle == STD_OUTPUT_HANDLE:
            return 0xFF8 # arbitrary valid handle
        elif nStdHandle == STD_ERROR_HANDLE:
            return 0xFFC # arbitrary valid handle
        else:
            return -1 #INVALID_HANDLE_VALUE

    @staticmethod
    def CloseHandle(platform, hObject):
        logger.info("CloseHandle(%x)", hObject)
        if platform.NT_SUCCESS(platform.NtClose(hObject)):
            return 1
        else:
            return 0

    # TODO: possibly implement using NtCreateFile and/or use a handle table
    @staticmethod
    def CreateFileW(platform, lpFileName, dwDesiredAccess, dwShareMode, lpSecurityAttributes, dwCreationDisposition, dwFlagsAndAttributes, hTemplateFile):
        return kernel32._CreateFile(platform, True, lpFileName, dwDesiredAccess, dwShareMode, lpSecurityAttributes, dwCreationDisposition, dwFlagsAndAttributes, hTemplateFile)

    @staticmethod
    def CreateFileA(platform, lpFileName, dwDesiredAccess, dwShareMode, lpSecurityAttributes, dwCreationDisposition, dwFlagsAndAttributes, hTemplateFile):
        return kernel32._CreateFile(platform, False, lpFileName, dwDesiredAccess, dwShareMode, lpSecurityAttributes, dwCreationDisposition, dwFlagsAndAttributes, hTemplateFile)

    @staticmethod
    def _CreateFile(platform, utf16, lpFileName, dwDesiredAccess, dwShareMode, lpSecurityAttributes, dwCreationDisposition, dwFlagsAndAttributes, hTemplateFile):
        '''https://msdn.microsoft.com/en-us/library/windows/desktop/aa363858(v=vs.85).aspx'''

        cpu = platform.current
        try:
            filename = readStringFromPointer(platform, cpu, lpFileName, utf16)
        except MemoryException as me:
            msg = "CreateFile{}: {}".format(utf16 and "W" or "A", me.cause)
            raise MemoryException(msg, 0xFFFFFFFF)
        except SymbolicAPIArgument:
            raise ConcretizeArgument(0)


        logger.info("""CreateFile%s(
    _In_     LPCTSTR               lpFileName: [%s],
    _In_     DWORD                 dwDesiredAccess: %s,
    _In_     DWORD                 dwShareMode: %s,
    _In_opt_ LPSECURITY_ATTRIBUTES lpSecurityAttributes: %s,
    _In_     DWORD                 dwCreationDisposition: %s,
    _In_     DWORD                 dwFlagsAndAttributes: %s,
    _In_opt_ HANDLE                hTemplateFile: %s
    );""" % (utf16 and "W" or "A",
            filename,
            toStr(platform, dwDesiredAccess),
            toStr(platform, dwShareMode),
            toStr(platform, lpSecurityAttributes),
            toStr(platform, dwCreationDisposition),
            toStr(platform, dwFlagsAndAttributes),
            toStr(platform, hTemplateFile),))

        cpu = platform.current

        return platform._fileHandle(lpFileName)

    #TODO possibly implement via NtWriteFile
    @staticmethod
    def WriteFile(platform, hFile, lpBuffer, nNumberOfBytesToWrite, lpNumberOfBytesWritten, lpOverlapped):
        '''https://msdn.microsoft.com/en-us/library/windows/desktop/aa365747(v=vs.85).aspx'''
        logger.info("""WriteFile(
    _In_        HANDLE       hFile: %s,
    _In_        LPCVOID      lpBuffer: %s,
    _In_        DWORD        nNumberOfBytesToWrite: %s,
    _Out_opt_   LPDWORD      lpNumberOfBytesWritten: %s,
    _Inout_opt_ LPOVERLAPPED lpOverlapped: %s
    );"""%(
        toStr(platform, hFile),
        toStr(platform, lpBuffer),
        toStr(platform, nNumberOfBytesToWrite),
        toStr(platform, lpNumberOfBytesWritten),
        toStr(platform, lpOverlapped))
    )

        if issymbolic(lpNumberOfBytesWritten):

            #Check if the symbol has a single solution.
            values = solver.get_all_values(platform.constraints, lpNumberOfBytesWritten, maxcnt=2, silent=True)
            if len(values) == 1:
                logger.info("ONE VALUE lpNumberOfBytesWritten: {}".format(lpNumberOfBytesWritten))
                lpNumberOfBytesWritten = values[0]

        cpu = platform.current
        if issymbolic(lpNumberOfBytesWritten):

            if solver.can_be_true(platform.constraints, lpNumberOfBytesWritten==0):
                raise ForkState(lpNumberOfBytesWritten==0)

            logger.info("WRITING TO SYMB lpNumberOfBytesWritten: {}".format(lpNumberOfBytesWritten))
            cpu.write_int(lpNumberOfBytesWritten, nNumberOfBytesToWrite, 32)

        elif lpNumberOfBytesWritten != 0:
            cpu.write_int(lpNumberOfBytesWritten, nNumberOfBytesToWrite, 32)

        return 1

    @staticmethod
    def CreateProcessW(platform, lpApplicationName, lpCommandLine, lpProcessAttributes,
            lpThreadAttributes, bInheritHandles, dwCreationFlags, lpEnvironment, 
            lpCurrentDirectory, lpStartupInfo, lpProcessInformation):
        return kernel32._CreateProcess(platform, True, lpApplicationName, lpCommandLine, lpProcessAttributes,
                lpThreadAttributes, bInheritHandles, dwCreationFlags, lpEnvironment, 
                lpCurrentDirectory, lpStartupInfo, lpProcessInformation)

    @staticmethod
    def CreateProcessA(platform, lpApplicationName, lpCommandLine, lpProcessAttributes,
            lpThreadAttributes, bInheritHandles, dwCreationFlags, lpEnvironment, 
            lpCurrentDirectory, lpStartupInfo, lpProcessInformation):
        return kernel32._CreateProcess(platform, False, lpApplicationName, lpCommandLine, lpProcessAttributes,
                lpThreadAttributes, bInheritHandles, dwCreationFlags, lpEnvironment, 
                lpCurrentDirectory, lpStartupInfo, lpProcessInformation)

    @staticmethod
    def _CreateProcess(platform, utf16, lpApplicationName, lpCommandLine, lpProcessAttributes,
            lpThreadAttributes, bInheritHandles, dwCreationFlags, lpEnvironment, 
            lpCurrentDirectory, lpStartupInfo, lpProcessInformation):
        """BOOL WINAPI CreateProcess(
          _In_opt_    LPCTSTR               lpApplicationName,
          _Inout_opt_ LPTSTR                lpCommandLine,
          _In_opt_    LPSECURITY_ATTRIBUTES lpProcessAttributes,
          _In_opt_    LPSECURITY_ATTRIBUTES lpThreadAttributes,
          _In_        BOOL                  bInheritHandles,
          _In_        DWORD                 dwCreationFlags,
          _In_opt_    LPVOID                lpEnvironment,
          _In_opt_    LPCTSTR               lpCurrentDirectory,
          _In_        LPSTARTUPINFO         lpStartupInfo,
          _Out_       LPPROCESS_INFORMATION lpProcessInformation
        );"""

        myname = "CreateProcess{}".format(utf16 and "W" or "A")
        cpu = platform.current

        try:
            appname = readStringFromPointer(platform, cpu, lpApplicationName, utf16)
        except MemoryException as me:
            msg = "{}: {}".format(myname, me.cause)
            raise MemoryException(msg, 0xFFFFFFFF)
        except SymbolicAPIArgument:
            raise ConcretizeArgument(0)

        try:
            cmdline = readStringFromPointer(platform, cpu, lpCommandLine, utf16)
        except MemoryException as me:
            msg = "{}: {}".format(myname, me.cause)
            raise MemoryException(msg, 0xFFFFFFFF)
        except SymbolicAPIArgument:
            raise ConcretizeArgument(1)

        raise IgnoreAPI("{}([{}], [{}], {}, {}, {}, {}, {}, {}, {}, {})".format(myname,
            appname, cmdline, str(lpProcessAttributes), 
            str(lpThreadAttributes), str(bInheritHandles), str(dwCreationFlags), str(lpEnvironment), 
            str(lpCurrentDirectory), str(lpStartupInfo), str(lpProcessInformation)))

class KERNELBASE(kernel32):
    #has the same functions as kernel32, needed for windows forward exports
    # and namespacing
    pass

def Ignore0(self):
    cpu = self.current
    logger.info('Ignore0 at %x No arguments', cpu.PC)
    return 1

def Ignore1(self, arg1):
    cpu = self.current
    logger.info('Ignore1 at %x Arguments(%x)', cpu.PC, arg1)
    return 1

def Ignore2(self, arg1, arg2):
    cpu = self.current
    logger.info('Ignore2 at %x Arguments(%x, %x)', cpu.PC, arg1, arg2)
    return 1

def Ignore3(self, arg1, arg2, arg3):
    cpu = self.current
    logger.info('Ignore3 at %x Arguments(%x, %x, %x)', cpu.PC, arg1, arg2, arg3)
    return 1

def Ignore4(self, arg1, arg2, arg3, arg4):
    cpu = self.current
    logger.info('Ignore4 at %x Arguments(%x, %x, %x, %x)', cpu.PC, arg1, arg2, arg3, arg4)
    return 1

def Ignore5(self, arg1, arg2, arg3, arg4, arg5):
    cpu = self.current
    logger.info('Ignore5 at %x Arguments(%x, %x, %x, %x, %x)', cpu.PC, arg1, arg2, arg3, arg4, arg5)
    return 1

def Ignore6(self, arg1, arg2, arg3, arg4, arg5, arg6):
    cpu = self.current
    logger.info('Ignore6 at %x Arguments(%x, %x, %x, %x, %x, %x)', cpu.PC, arg1, arg2, arg3, arg4, arg5, arg6)
    return 1
