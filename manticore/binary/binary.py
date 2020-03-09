import io
from typing import Dict, Type, Union

from elftools.elf.elffile import ELFFile


class Binary:
    magics: Dict[bytes, Type["Binary"]] = {}

    def __new__(cls, path):
        if cls is Binary:
            with open(path, "rb") as f:
                cl = cls.magics[f.read(4)]
            return cl(path)
        else:
            return super().__new__(cls)

    def __init__(self, path):
        self.path = path
        with open(path, "rb") as f:
            self.magic = Binary.magics[f.read(4)]

    def arch(self):
        pass

    def maps(self):
        pass

    def threads(self):
        pass


class BinaryException(Exception):
    """
    Binary file exception
    """

    pass


class CGCElf(Binary):
    @staticmethod
    def _cgc2elf(filename):
        # hack begin so we can use upstream Elftool
        with open(filename, "rb") as fd:
            stream = io.BytesIO(fd.read())
            stream.write(b"\x7fELF")
            stream.name = fd.name
            return stream

    def __init__(self, filename):
        super().__init__(filename)
        stream = self._cgc2elf(filename)
        self.elf = ELFFile(stream)
        self.arch = {"x86": "i386", "x64": "amd64"}[self.elf.get_machine_arch()]

        assert "i386" == self.arch
        assert self.elf.header.e_type in ["ET_EXEC"]

    def maps(self):
        for elf_segment in self.elf.iter_segments():
            if elf_segment.header.p_type not in ["PT_LOAD", "PT_NULL", "PT_PHDR", "PT_CGCPOV2"]:
                raise BinaryException("Not Supported Section")

            if elf_segment.header.p_type != "PT_LOAD" or elf_segment.header.p_memsz == 0:
                continue

            flags = elf_segment.header.p_flags
            # PF_X 0x1 Execute - PF_W 0x2 Write - PF_R 0x4 Read
            perms = ["   ", "  x", " w ", " wx", "r  ", "r x", "rw ", "rwx"][flags & 7]
            if "r" not in perms:
                raise BinaryException("Not readable map from cgc elf not supported")

            # CGCMAP--
            assert elf_segment.header.p_filesz != 0 or elf_segment.header.p_memsz != 0
            yield (
                (
                    elf_segment.header.p_vaddr,
                    elf_segment.header.p_memsz,
                    perms,
                    elf_segment.stream.name,
                    elf_segment.header.p_offset,
                    elf_segment.header.p_filesz,
                )
            )

    def threads(self):
        yield (("Running", {"EIP": self.elf.header.e_entry}))


class Elf(Binary):
    def __init__(self, filename):
        super().__init__(filename)
        self.elf = ELFFile(open(filename, "rb"))
        self.arch = {"x86": "i386", "x64": "amd64"}[self.elf.get_machine_arch()]
        assert self.elf.header.e_type in ["ET_DYN", "ET_EXEC", "ET_CORE"]

        # Get interpreter elf
        self.interpreter = None
        for elf_segment in self.elf.iter_segments():
            if elf_segment.header.p_type != "PT_INTERP":
                continue
            self.interpreter = Elf(elf_segment.data()[:-1])
            break
        if self.interpreter is not None:
            assert self.interpreter.arch == self.arch
            assert self.interpreter.elf.header.e_type in ["ET_DYN", "ET_EXEC"]

    def __del__(self):
        if self.elf is not None:
            self.elf.stream.close()

    def maps(self):
        for elf_segment in self.elf.iter_segments():
            if elf_segment.header.p_type != "PT_LOAD" or elf_segment.header.p_memsz == 0:
                continue

            flags = elf_segment.header.p_flags
            # PF_X 0x1 Execute - PF_W 0x2 Write - PF_R 0x4 Read
            perms = ["   ", "  x", " w ", " wx", "r  ", "r x", "rw ", "rwx"][flags & 7]
            if "r" not in perms:
                raise BinaryException("Not readable map from cgc elf not supported")

            # CGCMAP--
            assert elf_segment.header.p_filesz != 0 or elf_segment.header.p_memsz != 0
            yield (
                (
                    elf_segment.header.p_vaddr,
                    elf_segment.header.p_memsz,
                    perms,
                    elf_segment.stream.name,
                    elf_segment.header.p_offset,
                    elf_segment.header.p_filesz,
                )
            )

    def getInterpreter(self):
        return self.interpreter

    def threads(self):
        yield (("Running", {"EIP": self.elf.header.e_entry}))


Binary.magics = {b"\x7fCGC": CGCElf, b"\x7fELF": Elf}
