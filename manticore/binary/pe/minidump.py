import struct
from StringIO import StringIO
class Structure(object):
    def __init__(self):
        if not hasattr(self, "_fields_"):
            raise NotImplementedError("No _fields_ in structure")
        
        self.__size__ = 0
        self.__struct_fields__ = {}
        
        for _, field_type in self._fields_:
            if type(field_type) == str:
                self.__size__ += struct.calcsize(field_type)
            else:
                obj = field_type()
                self.__size__ += len(obj)

    def __getattr__(self, name):
        if name in self.__struct_fields__:
            return self.__struct_fields__[name]
        raise AttributeError(name)
    
    def __len__(self):
        return self.__size__
    
    def __repr__(self):
        return self.tree()

    def parse(self, fd):
        for field_name, field_type in self._fields_:
            if type(field_type) == str:
                size = struct.calcsize(field_type)
                value = struct.unpack(field_type, fd.read(size))[0]
                self.__struct_fields__[field_name] = value
            else:
                obj = field_type()
                obj.parse(fd)
                self.__struct_fields__[field_name] = obj

    
    def tree(self, depth=0):
        def stringify(name):
            assert name in self.__struct_fields__
            value = self.__struct_fields__[name]
            if type(value) == int:
                return "0x%08x" % value
            elif type(value) == long:
                return "0x%016x" % value
            elif type(value) == str:
                return repr(value)
            else:
                return "%s\n%s" % (value.__class__.__name__, value.tree(depth + 2))

        out  = "  " * depth
        if depth != 0: out += "+"
        out += "%s\n" % self.__class__.__name__

        for field_name, field_type in self._fields_:
            out += "  " * depth + "  .%-32s = %s\n" % (field_name, stringify(field_name))
        
        return out[ : -1]

class MINIDUMP_HEADER(Structure):
    _fields_ = [("Signature", "4s"), \
                ("Version", "<I"), \
                ("NumberOfStreams", "<I"), \
                ("StreamDirectoryRva", "<I"), \
                ("Checksum", "<I"), \
                ("TimeDateStamp", "<I"), \
                ("Flags", "<Q")]

class MINIDUMP_LOCATION_DESCRIPTOR(Structure):
    _fields_ = [("DataSize", "<I"), \
                ("Rva", "<I")]

class MINIDUMP_EXCEPTION(Structure):
    _fields_ = [("ExceptionCode", "<I"), \
                ("ExceptionFlags", "<I"), \
                ("ExceptionRecord", "<Q"), \
                ("ExceptionAddress", "<Q"), \
                ("NumberOfParameters", "<I"), \
                ("__unusedAlignment", "<I"), \
                ("ExceptionInfomration0", "<Q"), \
                ("ExceptionInfomration1", "<Q"), \
                ("ExceptionInfomration2", "<Q"), \
                ("ExceptionInfomration3", "<Q"), \
                ("ExceptionInfomration4", "<Q"), \
                ("ExceptionInfomration5", "<Q"), \
                ("ExceptionInfomration6", "<Q"), \
                ("ExceptionInfomration7", "<Q"), \
                ("ExceptionInfomration8", "<Q"), \
                ("ExceptionInfomration9", "<Q"), \
                ("ExceptionInfomration10", "<Q"), \
                ("ExceptionInfomration11", "<Q"), \
                ("ExceptionInfomration12", "<Q"), \
                ("ExceptionInfomration13", "<Q"), \
                ("ExceptionInfomration14", "<Q")]

class MINIDUMP_EXCEPTION_STREAM(Structure):
    _fields_ = [("ThreadId", "<I"), \
                ("__alignment", "<I"), \
                ("ExceptionRecord", MINIDUMP_EXCEPTION), \
                ("ThreadContext", MINIDUMP_LOCATION_DESCRIPTOR)]

class MINIDUMP_MEMORY_DESCRIPTOR64(Structure):
    _fields_ = [("StartOfMemory", "<Q"), \
                ("DataSize", "<Q")]

class VS_FIXEDFILEINFO(Structure):
    _fields_ = [("dwSignature", "<I"), \
                ("dwStrucVersion", "<I"), \
                ("dwFileVersionMS", "<I"), \
                ("dwFileVersionLS", "<I"), \
                ("dwProductVersionMS", "<I"), \
                ("dwProductVersionLS", "<I"), \
                ("dwFileFlagsMask", "<I"), \
                ("dwFileFlags", "<I"), \
                ("dwFileOS", "<I"), \
                ("dwFileType", "<I"), \
                ("dwFileSubtype", "<I"), \
                ("dwFileDateMS", "<I"), \
                ("dwFileDateLS", "<I")]

class MINIDUMP_STRING(Structure):
    def __init__(self):
        self._fields_ = [("Length", "<I")]
        Structure.__init__(self)

    def __len__(self):
        if self.__size__ == 0: raise Exception("Variadic Structure")
        return self.__size__
    
    def parse(self, fd):
        count = struct.unpack("<I", fd.read(4))[0]
        bytes = fd.read(count)

        self.__struct_fields__["Length"] = count
        self.__struct_fields__["Buffer"] = bytes
        
        self._fields_.append(("Buffer", "%ds" % count))

class MINIDUMP_MODULE(Structure):
    _fields_ = [("BaseOfImage", "<Q"), \
                ("SizeOfImage", "<I"), \
                ("CheckSum", "<I"), \
                ("TimeDateStamp", "<I"), \
                ("ModuleNameRva", "<I"), \
                ("VersionInfo", VS_FIXEDFILEINFO), \
                ("CvRecord", MINIDUMP_LOCATION_DESCRIPTOR), \
                ("MiscRecord", MINIDUMP_LOCATION_DESCRIPTOR), \
                ("Reserved0", "<Q"), \
                ("Reserved1", "<Q")]

class MINIDUMP_MODULE_LIST(Structure):
    def __init__(self):
        self._fields_ = [("NumberOfModules", "<I")]
        Structure.__init__(self)

    def __len__(self):
        if self.__size__ == 0: raise Exception("Variadic Structure")
        return self.__size__

    def parse(self, fd):
        count = struct.unpack("<I", fd.read(4))[0]
        self.__struct_fields__["NumberOfModules"] = count
        self.__struct_fields__["Modules"] = {}

        for i in range(0, count):
            mm = MINIDUMP_MODULE()
            mm.parse(fd)
            
            pos = fd.tell()
            fd.seek(mm.ModuleNameRva)
            
            ms = MINIDUMP_STRING()
            ms.parse(fd)
            
            self.__struct_fields__["Modules"][str(ms.Buffer)] = mm

            fd.seek(pos)

    def tree(self, depth=0):
        out  = "  " * depth
        if depth != 0: out += "+"
        out += "%s\n" % self.__class__.__name__
        
        out += "  " * depth + "  .%-32s = 0x%08x\n" % ("NumberOfModules", self.__struct_fields__["NumberOfModules"])
        out += "  " * depth + "  .%-32s = MINIDUMP_MODULE[]\n" % "Modules"
        
        i = 0
        for module_name in self.__struct_fields__["Modules"]:
            out += "  " * depth + "    [%02i] \"%s\" %s\n" % (i, module_name, \
                                                              self.__struct_fields__["Modules"][module_name].tree(depth + 2))
            i += 1

        return out[ : -1]

class MINIDUMP_MEMORY64_LIST(Structure):
    def __init__(self):
        self._fields_ = [("NumberOfMemoryRanges", "<Q"), \
                         ("BaseRva", "<Q")]
        Structure.__init__(self)
    
    def __len__(self):
        if self.__size__ == 0: raise Exception("Variadic Structure")
        return self.__size__

    def parse(self, fd):
        nitems, rva = struct.unpack("<QQ", fd.read(16))
        self.__struct_fields__["NumberOfMemoryRanges"] = nitems
        self.__struct_fields__["BaseRva"] = rva
        
        obj = MINIDUMP_MEMORY_DESCRIPTOR64()
        self.__size__ = 16 + nitems * len(obj)
        
        self.__struct_fields__["MemoryRanges"] = []
        for i in range(0, nitems):
            desc = MINIDUMP_MEMORY_DESCRIPTOR64()
            desc.parse(fd)

            self.__struct_fields__["MemoryRanges"].append(desc)

    def tree(self, depth=0):
        out  = "  " * depth
        if depth != 0: out += "+"
        out += "%s\n" % self.__class__.__name__

        out += "  " * depth + "  .%-32s = 0x%016x\n" % ("NumberOfMemoryRanges", self.__struct_fields__["NumberOfMemoryRanges"])
        out += "  " * depth + "  .%-32s = 0x%016x\n" % ("BaseRva", self.__struct_fields__["BaseRva"])
        out += "  " * depth + "  .%-32s = MINIDUMP_MEMORY_DESCRIPTOR64[]\n" % "MemoryRanges"
        
        i = 0
        for desc in self.__struct_fields__["MemoryRanges"]:
            out += "  " * depth + "    [%02i] %s\n" % (i, desc.tree(depth + 2))
            i += 1
        
        return out[ : -1]

class MINIDUMP_DIRECTORY(Structure):
    _fields_ = [("StreamType", "<I"), \
                ("Location", MINIDUMP_LOCATION_DESCRIPTOR)]

class MINIDUMP_MEMORY_INFO(Structure):
    _fields_ = [("BaseAddress", "<Q"), \
                ("AllocationBase", "<Q"), \
                ("AllocationProtect", "<I"), \
                ("__alignment1", "<I"), \
                ("RegionSize", "<Q"), \
                ("State", "<I"), \
                ("Protect", "<I"), \
                ("Type", "<I"), \
                ("__alignment2", "<I")]

class MINIDUMP_MEMORY_INFO_LIST(Structure):
    _fields_ = [("SizeOfHeader", "<I"), \
                ("SizeOfEntry", "<I"), \
                ("NumberOfEntries", "<Q")]

class MINIDUMP_SYSTEM_INFO(Structure):
    _fields_ = [("ProcessorArchitecture", "<H"), \
                ("ProcessorLevel", "<H"), \
                ("ProcessorRevision", "<H"), \
                ("NumberOfProcessors", "B"), \
                ("ProductType", "B"), \
                ("MajorVersion", "<I"), \
                ("MinorVersion", "<I"), \
                ("BuildNumber", "<I"), \
                ("PlatformId", "<I"), \
                ("CSDVersionRva", "<I"), \
                ("SuiteMask", "<H"), \
                ("Reserved2", "<H"), \
                ("VendorId", "12s"), \
                ("VersionInformation", "<I"), \
                ("FeatureInformation", "<I"), \
                ("AMDExtendedCpuFeatures", "<I")]

class MINIDUMP_THREAD(Structure):
    _fields_ = [("ThreadId", "<I"), \
                ("SuspendCount", "<I"), \
                ("PriorityClass", "<I"), \
                ("Priority", "<I"), \
                ("Teb", "<Q"), \
                ("Stack", MINIDUMP_MEMORY_DESCRIPTOR64), \
                ("ThreadContext", MINIDUMP_LOCATION_DESCRIPTOR)]

    def parse(self, fd):
        Structure.parse(self, fd)
        a = fd.tell()
        fd.seek(self.ThreadContext.Rva)
        self.__struct_fields__["Context"] = fd.read(self.ThreadContext.DataSize)
        fd.seek(a) 

    def getContext(self, architecture):
        if architecture == "x86":
            cxt = CONTEXT_x86()
        elif architecture == "amd64":
            cxt = CONTEXT_amd64()
        elif architecture == "arm32":
            cxt = CONTEXT_arm32()
        else:
            raise Exception("Unknown architecture for context parsing!")
        assert len(self.Context) == len(cxt)

        cxt.parse(StringIO(self.Context))
        return cxt

class MINIDUMP_THREAD_LIST(Structure):
    def __init__(self):
        self._fields_ = [("NumberOfThreads", "<I")]
        Structure.__init__(self)

    def __len__(self):
        if self.__size__ == 0: raise Exception("Variadic Structure")
        return self.__size__

    def parse(self, fd):
        count = struct.unpack("<I", fd.read(4))[0]
        self.__struct_fields__["NumberOfThreads"] = count
        self.__struct_fields__["Threads"] = []

        for i in range(0, count):
            mt = MINIDUMP_THREAD()
            mt.parse(fd)
            self.__struct_fields__["Threads"].append(mt)

    def tree(self, depth=0):
        out  = "  " * depth
        if depth != 0: out += "+"
        out += "%s\n" % self.__class__.__name__
        
        out += "  " * depth + "  .%-32s = 0x%08x\n" % ("NumberOfThreads", self.__struct_fields__["NumberOfThreads"])
        out += "  " * depth + "  .%-32s = MINIDUMP_THREAD[]\n" % "Threads"
        
        i = 0
        for thread in self.__struct_fields__["Threads"]:
            out += "  " * depth + "    [%02i] %s\n" % (i, thread.tree(depth + 2))
            i += 1

        return out[ : -1]

class FLOATING_SAVE_AREA_x86(Structure):
    _fields_ = [("ControlWord", "<I"), \
                ("StatusWord", "<I"), \
                ("TagWord", "<I"), \
                ("ErrorOffset", "<I"), \
                ("ErrorSelector", "<I"), \
                ("DataOffset", "<I"), \
                ("DataSelector", "<I"), \
                ("RegisterArea", "80s"), \
                ("Cr0NpxState", "<I")]

class CONTEXT_x86(Structure):
    _fields_ = [("ContextFlags", "<I"), \
                ("Dr0", "<I"), \
                ("Dr1", "<I"), \
                ("Dr2", "<I"), \
                ("Dr3", "<I"), \
                ("Dr6", "<I"), \
                ("Dr7", "<I"), \
                ("FloatSave", FLOATING_SAVE_AREA_x86), \
                ("SegGs", "<I"), \
                ("SegFs", "<I"), \
                ("SegEs", "<I"), \
                ("SegDs", "<I"), \
                ("Edi", "<I"), \
                ("Esi", "<I"), \
                ("Ebx", "<I"), \
                ("Edx", "<I"), \
                ("Ecx", "<I"), \
                ("Eax", "<I"), \
                ("Ebp", "<I"), \
                ("Eip", "<I"), \
                ("SegCs", "<I"), \
                ("EFlags", "<I"), \
                ("Esp", "<I"), \
                ("SegSs", "<I"), \
                ("ExtendedRegisters", "512s")]

class XMM_SAVE_AREA32(Structure):
    _fields_ = [("ControlWord", "<H"), \
                ("StatusWord", "<H"), \
                ("TagWord", "B"), \
                ("Reserved1", "B"), \
                ("ErrorOpcode", "<H"), \
                ("ErrorOffset", "<I"), \
                ("ErrorSelector", "<H"), \
                ("Reserved2", "<H"), \
                ("DataOffset", "<I"), \
                ("DataSelector", "<H"), \
                ("Reserved3", "<H"), \
                ("MxCsr", "<I"), \
                ("MxCsr_Mask", "<I"), \
                ("FloatRegisters", "128s"), \
                ("XmmRegisters", "256s"), \
                ("Reserved4", "96s")]

class CONTEXT_amd64(Structure):
    _fields_ = [("P1Home", "<Q"), \
                ("P2Home", "<Q"), \
                ("P3Home", "<Q"), \
                ("P4Home", "<Q"), \
                ("P5Home", "<Q"), \
                ("P6Home", "<Q"), \
                ("ContextFlags", "<I"), \
                ("MxCsr", "<I"), \
                ("SegCs", "<H"), \
                ("SegDs", "<H"), \
                ("SegEs", "<H"), \
                ("SegFs", "<H"), \
                ("SegGs", "<H"), \
                ("SegSs", "<H"), \
                ("EFlags", "<I"), \
                ("Dr0", "<Q"), \
                ("Dr1", "<Q"), \
                ("Dr2", "<Q"), \
                ("Dr3", "<Q"), \
                ("Dr6", "<Q"), \
                ("Dr7", "<Q"), \
                ("Rax", "<Q"), \
                ("Rcx", "<Q"), \
                ("Rdx", "<Q"), \
                ("Rbx", "<Q"), \
                ("Rsp", "<Q"), \
                ("Rbp", "<Q"), \
                ("Rsi", "<Q"), \
                ("Rdi", "<Q"), \
                ("R8", "<Q"), \
                ("R9", "<Q"), \
                ("R10", "<Q"), \
                ("R11", "<Q"), \
                ("R12", "<Q"), \
                ("R13", "<Q"), \
                ("R14", "<Q"), \
                ("R15", "<Q"), \
                ("Rip", "<Q"), \
                ("FltSave", XMM_SAVE_AREA32), \
                ("VectorRegister", "416s"), \
                ("DebugControl", "<Q"), \
                ("LastBranchToRip", "<Q"), \
                ("LastBranchFromRip", "<Q"), \
                ("LastExceptionToRip", "<Q"), \
                ("LastExceptionFromRip", "<Q")]

class CONTEXT_arm32(Structure):
    # XXX: this structure is INCOMPLETE
    _fields_ = [("ContextFlags", "<I"), \
                 ("R0", "<I"), \
                 ("R1", "<I"), \
                 ("R2", "<I"), \
                 ("R3", "<I"), \
                 ("R4", "<I"), \
                 ("R5", "<I"), \
                 ("R6", "<I"), \
                 ("R7", "<I"), \
                 ("R8", "<I"), \
                 ("R9", "<I"), \
                 ("R10", "<I"), \
                 ("R11", "<I"), \
                 ("R12", "<I"), \
                 ("Sp", "<I"), \
                 ("Lr", "<I"), \
                 ("Pc", "<I"), \
                 ("Cpsr", "<I"), \
                 ("Fpscr", "<I"), \
                 ("Padding", "<I")]

class MiniDump(object):
    def __init__(self, path, autoparse=True):
        self.path = path
        self.fd = open(self.path, "rb")
        
        self.memory_data = {}
        self.memory_query = {}
        self.context = None
        
        self.processor = None
        self.architecture = None
        self.processor_level = None
        self.version = None
        
        self.exception_info = None
        self.system_info = None
        self.module_map = {}
        self.threads = []

        if autoparse: self.parse()

    def __parse_memory_list64__(self, dirent):
        ml64 = MINIDUMP_MEMORY64_LIST()
        ml64.parse(self.fd)
        
        self.fd.seek(ml64.BaseRva)

        for desc in ml64.MemoryRanges:
            bytes = self.fd.read(desc.DataSize)
            self.memory_data[desc.StartOfMemory] = bytes

    def __parse_exception_stream__(self, dirent):
        exc = MINIDUMP_EXCEPTION_STREAM()
        exc.parse(self.fd)
        
        self.fd.seek(exc.ThreadContext.Rva)
        
        if self.architecture == "x86":
            cxt = CONTEXT_x86()
        elif self.architecture == "amd64":
            cxt = CONTEXT_amd64()
        elif self.architecture == "arm32":
            cxt = CONTEXT_arm32()
        else:
            raise Exception("Unknown architecture for context parsing!")
        
        cxt.parse(self.fd)
        self.context = cxt
        self.exception_info = exc

    def __parse_memory_info__(self, dirent):
        PAGE_EXECUTE = 0x10
        PAGE_EXECUTE_READ = 0x20
        PAGE_EXECUTE_READWRITE = 0x40
        PAGE_EXECUTE_WRITECOPY = 0x80
        PAGE_NOACCESS = 0x01
        PAGE_READONLY = 0x02
        PAGE_READWRITE = 0x04
        PAGE_WRITECOPY = 0x08

        def parse_perms(flags):
            if ((flags & 0xff) == PAGE_EXECUTE): return "x"
            if ((flags & 0xff) == PAGE_EXECUTE_READ): return "rx"
            if ((flags & 0xff) == PAGE_EXECUTE_READWRITE): return "rwx"
            if ((flags & 0xff) == PAGE_EXECUTE_WRITECOPY): return "rwx"
            if ((flags & 0xff) == PAGE_READONLY): return "r"
            if ((flags & 0xff) == PAGE_READWRITE): return "rw"
            if ((flags & 0xff) == PAGE_WRITECOPY): return "rw"
            if ((flags & 0xff) == PAGE_NOACCESS): return ""
            raise NotImplementedError

        mil = MINIDUMP_MEMORY_INFO_LIST()
        mil.parse(self.fd)
        
        for i in range(0, mil.NumberOfEntries):
            mi = MINIDUMP_MEMORY_INFO()
            mi.parse(self.fd)
            
            if mi.Protect == 0:
                perms = parse_perms(mi.AllocationProtect)
            else:
                perms = parse_perms(mi.Protect)

            self.memory_query[mi.BaseAddress] = (perms, mi.RegionSize)
    
    def __parse_systeminfo__(self, dirent):
        PROCESSOR_ARCHITECTURE_AMD64   = 9
        PROCESSOR_ARCHITECTURE_ARM     = 5
        PROCESSOR_ARCHITECTURE_IA64    = 6
        PROCESSOR_ARCHITECTURE_INTEL   = 0
        PROCESSOR_ARCHITECTURE_UNKNOWN = 0xffff

        msi = MINIDUMP_SYSTEM_INFO()
        msi.parse(self.fd)

        self.system_info = msi
        self.processor = msi.VendorId
        
        if msi.ProcessorArchitecture == PROCESSOR_ARCHITECTURE_AMD64:
            self.architecture = "amd64"
        elif msi.ProcessorArchitecture == PROCESSOR_ARCHITECTURE_ARM:
            self.architecture = "arm32"
        elif msi.ProcessorArchitecture == PROCESSOR_ARCHITECTURE_IA64:
            self.architecture = "ia64"
        elif msi.ProcessorArchitecture == PROCESSOR_ARCHITECTURE_INTEL:
            self.architecture = "x86"
        else:
            self.architecture = "unknown"
        
        if self.architecture == "x86":
            if msi.ProcessorLevel == 3:
                self.processor_level = "i386"
            elif msi.ProcessorLevel == 4:
                self.processor_level = "i486"
            elif msi.ProcessorLevel == 5:
                self.processor_level = "pentium"
            elif msi.ProcessorLevel == 6:
                self.processor_level = "pentium2"
        else:
            self.processor_level = "unknown"
        
        self.version = "%d.%d (build %d)" % (msi.MajorVersion, msi.MinorVersion, msi.BuildNumber)
    
    def __parse_modulelist__(self, dirent):
        mml = MINIDUMP_MODULE_LIST()
        mml.parse(self.fd)

        self.module_map = mml.Modules

    def __parse_threadlist__(self, dirent):
        mtl = MINIDUMP_THREAD_LIST()
        mtl.parse(self.fd)

        self.threads = mtl.Threads

    def parse(self):
        try:
            hdr = MINIDUMP_HEADER()
            hdr.parse(self.fd)
            
            assert hdr.Signature == "MDMP"
            self.fd.seek(hdr.StreamDirectoryRva)
            
            streamTbl = {3: self.__parse_threadlist__, \
                         4: self.__parse_modulelist__, \
                         6: self.__parse_exception_stream__, \
                         7: self.__parse_systeminfo__, \
                         9: self.__parse_memory_list64__, \
                         16: self.__parse_memory_info__}
            streams = {}
            for i in range(0, hdr.NumberOfStreams):
                dirent = MINIDUMP_DIRECTORY()
                dirent.parse(self.fd)
                
                streams[dirent.StreamType] = dirent
    
            if not 7 in streams: raise Exception("No SYSTEM_INFO stream found...context will not work correctly!")
            
            # it is important we parse SYSTEM_INFO first
            parse_order = streams.keys()
            parse_order.remove(7)
            parse_order = [7] + parse_order
            
            for item in parse_order:
                dirent = streams[item]
                if dirent.StreamType in streamTbl:
                    self.fd.seek(dirent.Location.Rva)
                    streamTbl[dirent.StreamType](dirent)

        finally:
            self.close()
    
    def get_exception_info(self):
        return self.exception_info
    
    def get_thread_by_tid(self, tid):
        for thread in self.threads:
            if thread.ThreadId == tid: return thread
        raise Exception("No thread of TID %d" % tid)
    
    def get_register_context_by_tid(self, tid):
        thread = self.get_thread_by_tid(tid)
        return thread.getContext(self.architecture)

    def get_threads(self):
        return self.threads

    def get_version(self):
        return self.version

    def get_architecture(self):
        return self.architecture

    def get_system_info(self):
        return self.system_info

    def get_module_map(self):
        return self.module_map

    def get_register_context(self):
        return self.context

    def get_memory_data(self):
        return self.memory_data

    def get_memory_map(self):
        return self.memory_query

    def close(self):
        if not self.fd is None:
            self.fd.close()
            self.fd = None


