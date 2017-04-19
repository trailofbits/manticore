''' Common binary formats interface 
Ideally you should be able to do something like 

        from binary import Binary
        binary = Binary(filename)
        assert cpu.machine == binary.arch, "Not matching cpu"
        logger.info("Loading %s as a %s elf"%(filename, binary.arch))
        for mm in binary.maps():
            cpu.mem.mmapFile( mm )
        for th in binary.threads():
            setup(th)

But there are difference between format that makes it difficult to find a simple
and common API.  interpreters? linkers? linked DLLs?

'''

class Binary(object):
    magics = { }
    def __new__(cls, path):
        if cls is Binary:
            cl = cls.magics[file(path).read(4)]
            return cl(path)
        else:
            return super(Binary, cls).__new__(cls, path)

    def __init__(self, path):
        self.path = path
        self.magic = Binary.magics[file(path).read(4)]

    def arch(self):
        pass

    def maps(self):
        pass

    def threads(self):
        pass



from elftools.elf.elffile import ELFFile
import StringIO
class CGCElf(Binary):

    @staticmethod
    def _cgc2elf(filename):
        #hack begin so we can use upstream Elftool
        with open(filename, 'rb') as fd:
            stream = StringIO.StringIO(fd.read())
            stream.write('\x7fELF')
            stream.name = fd.name
            return stream

    def __init__(self, filename):
        super(CGCElf, self).__init__(filename)
        stream = self._cgc2elf(filename)
        self.elf = ELFFile(stream)
        self.arch = {'x86':'i386','x64':'amd64'}[self.elf.get_machine_arch()]

        assert 'i386' == self.arch
        assert self.elf.header.e_type in ['ET_EXEC']

    def maps(self):
        for elf_segment in self.elf.iter_segments():
            if elf_segment.header.p_type not in ['PT_LOAD', 'PT_NULL', 'PT_PHDR', 'PT_CGCPOV2']:
                raise Exception("Not Supported Section")

            if elf_segment.header.p_type != 'PT_LOAD' or elf_segment.header.p_memsz == 0:
                continue

            flags = elf_segment.header.p_flags
            #PF_X 0x1 Execute - PF_W 0x2 Write - PF_R 0x4 Read
            perms = ['   ', '  x', ' w ', ' wx', 'r  ', 'r x', 'rw ', 'rwx'][flags&7]
            if 'r' not in perms:
                raise Exception("Not readable map from cgc elf not supported")

            #CGCMAP--
            assert elf_segment.header.p_filesz != 0 or elf_segment.header.p_memsz != 0 
            yield((elf_segment.header.p_vaddr,
                  elf_segment.header.p_memsz,
                  perms, 
                  elf_segment.stream.name, elf_segment.header.p_offset, elf_segment.header.p_filesz))

    def threads(self):
        yield(('Running', {'EIP': self.elf.header.e_entry}))


class Elf(Binary):
    def __init__(self, filename):
        super(Elf, self).__init__(filename)
        self.elf = ELFFile(file(filename)) 
        self.arch = {'x86':'i386','x64':'amd64'}[self.elf.get_machine_arch()]
        assert self.elf.header.e_type in ['ET_DYN', 'ET_EXEC', 'ET_CORE']


        #Get interpreter elf
        self.interpreter = None
        for elf_segment in self.elf.iter_segments():
            if elf_segment.header.p_type != 'PT_INTERP':
                continue
            self.interpreter = Elf(elf_segment.data()[:-1])
            break
        if not self.interpreter is None:
            assert self.interpreter.arch == self.arch
            assert self.interpreter.elf.header.e_type in ['ET_DYN', 'ET_EXEC']


    def maps(self):
        for elf_segment in self.elf.iter_segments():
            if elf_segment.header.p_type != 'PT_LOAD' or elf_segment.header.p_memsz == 0:
                continue

            flags = elf_segment.header.p_flags
            #PF_X 0x1 Execute - PF_W 0x2 Write - PF_R 0x4 Read
            perms = ['   ', '  x', ' w ', ' wx', 'r  ', 'r x', 'rw ', 'rwx'][flags&7]
            if 'r' not in perms:
                raise Exception("Not readable map from cgc elf not supported")

            #CGCMAP--
            assert elf_segment.header.p_filesz != 0 or elf_segment.header.p_memsz != 0 
            yield((elf_segment.header.p_vaddr,
                  elf_segment.header.p_memsz,
                  perms, 
                  elf_segment.stream.name, elf_segment.header.p_offset, elf_segment.header.p_filesz))

    def getInterpreter(self):
        return self.interpreter

    def threads(self):
        yield(('Running', {'EIP': self.elf.header.e_entry}))

from grr.snapshot import Grr
class CGCGrr(Binary):
    def __init__(self, filename):
        HEADERSIZE = 16384
        self.grr = Grr.from_buf(file(filename).read(HEADERSIZE))
        self.arch = 'i386'
        assert ''.join(self.grr.magic) == 'GRRS'
        assert self.grr.exe_num <= 16
        assert self.grr.ranges[0].fd_offs == 16384
        #TODO more asserts
        super(CGCGrr, self).__init__(filename)

    def maps(self):
        for r in self.grr.ranges:
            assert r.end>=r.begin
            assert (r.end-r.begin)&0xfff == 0
            assert r.fd_offs&0xfff == 0
            if r.end-r.begin == 0:
                continue
            perms = ''
            perms += r.is_r and 'r'or' '
            perms += r.is_w and 'w'or' '
            perms += r.is_x and 'x'or' '
            if 'r' not in perms:
                raise Exception("Not readable map from grr snapshot elf not supported")

            yield((r.begin, r.end-r.begin, perms, self.path, r.fd_offs, r.end-r.begin))

    def threads(self):
        #Basic
        regs = ['r15','r14','r13','r12','rbp','rbx','r11','r10','r9','r8','rax',
                'rcx','rdx','rsi','rdi','rip','cs','eflags','rsp','ss','ds','es','fs','gs']
        registers = dict([(name.upper(), getattr(self.grr.gregs, name)) for name in regs])

        #XMM
        for name in ['xmm0', 'xmm1', 'xmm2', 'xmm3', 'xmm4', 'xmm5', 'xmm6', 'xmm7', 'xmm8', 
                     'xmm9', 'xmm10', 'xmm11', 'xmm12', 'xmm13', 'xmm14', 'xmm15' ]:
            registers[name.upper()] = getattr(self.grr.fpregs.xmm_space, name).high << 64 | \
                                      getattr(self.grr.fpregs.xmm_space, name).low

        #FPU
        for i in xrange(8):
            registers['FP%d'%i] = ( getattr(self.grr.fpregs.st_space,'st%d'%i).mantissa, 
                                        getattr(self.grr.fpregs.st_space,'st%d'%i).exponent )

        yield ('Running', registers)

class Minidump(Binary):
    def __init__(self, filename):
        self.md = minidump.MiniDump(path)
        assert self.md.get_architecture() == "x86"
        self.arch = 'i386'

        major, minor = map(int, self.md.version.split(' ')[0].split('.'))
        if major == 6:
            self.flavor = "Windows7SP%d"%minor
        elif major == 10:
            self.flavor = "Windows10SP%d"%minor
        else:
            raise NotImplemented() #"Windows version not supported")

        super(Minidump, self).__init__(filename)



    def maps(self):
        # Setting up memory maps
        query = self.md.get_memory_map()
        data = self.get_memory_data()

        for addr in data:
            perms, size = query[addr]
            offsetofdatainminidump = 0
            yield((addr&0xffffffff, size, perms, self.path, offsetofdatainminidump, len(data[addr]) ) )

    def threads(self):
        selectedThreadId = self.md.get_threads()[0].ThreadId
        
        for thread in self.md.get_threads():
            cxt = md.get_register_context_by_tid(thread.ThreadId)
            #Let's just ignore all extra threads for now
            status = 'Sleeping'
            if selectedThreadId == thread.ThreadId:
                status = 'Running'
            registers = { 'EIP': cxt.Eip,
                            'ESP': cxt.Esp,
                            'EBP': cxt.Ebp,
                            'EAX': cxt.Eax,
                            'EBX': cxt.Ebx,
                            'ECX': cxt.Ecx,
                            'EDX': cxt.Edx,
                            'ESI': cxt.Esi,
                            'EDI': cxt.Edi,
                            'FS': cxt.SegFs}

            if (additional_context and 'registers' in additional_context):
                for name, value in additional_context['registers'].iteritems():
                    registers[name]= value
            yield((status, registers))




Binary.magics= { '\x7fCGC': CGCElf,
                 '\x7fELF': Elf,
                 'GRRS': CGCGrr,
                 'MDMP': Minidump}


if __name__ == '__main__':
    import sys
    print list(Binary(sys.argv[1]).threads())
    print list(Binary(sys.argv[1]).maps())


