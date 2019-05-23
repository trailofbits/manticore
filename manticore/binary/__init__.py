""" Common binary formats interface
Ideally you should be able to do something like

        from binary import Binary
        binary = Binary(filename)
        assert cpu.machine == binary.arch, "Not matching cpu"
        logger.info(f"Loading {filename} as a {binary.arch} elf")
        for mm in binary.maps():
            cpu.mem.mmapFile( mm )
        for th in binary.threads():
            setup(th)

But there are difference between format that makes it difficult to find a simple
and common API.  interpreters? linkers? linked DLLs?

"""

from .binary import Binary, CGCElf, Elf  # noqa


if __name__ == "__main__":
    import sys

    print(list(Binary(sys.argv[1]).threads()))
    print(list(Binary(sys.argv[1]).maps()))
