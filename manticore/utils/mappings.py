import sys
import ctypes
import mmap as MMAP

mmap_function = None
munmap_function = None

# initialize global functions depending on platform


def get_libc():
    osname = sys.platform.lower()
    if osname.startswith("darwin"):
        filename = "libc.dylib"
    elif osname.startswith("linux"):
        filename = "libc.so.6"
    elif osname.startswith("netbsd"):
        filename = "libc.so"
    else:
        raise ValueError("Unsupported host OS: " + osname)

    return ctypes.cdll.LoadLibrary(filename)


libc = get_libc()

# void* mmap(void* addr, size_t len, int prot, int flags, int fd, off_t offset)
mmap_function = libc.mmap
mmap_function.restype = ctypes.c_void_p
mmap_function.argtype = [ctypes.c_void_p, ctypes.c_size_t,
                         ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_size_t]


# int munmap(void* addr, size_t len)
munmap_function = libc.munmap
munmap_function.restype = ctypes.c_int
munmap_function.argtype = [ctypes.c_void_p, ctypes.c_size_t]


def mmap(fd, offset, size):
    prot = MMAP.PROT_READ | MMAP.PROT_WRITE
    flags = MMAP.MAP_PRIVATE

    if size & 0xfff != 0:
        size = (size & ~0xfff) + 0x1000

    assert size > 0

    result = mmap_function(0, size, prot, flags, fd, offset)
    return ctypes.cast(result, ctypes.POINTER(ctypes.c_char))


def munmap(address, size):
    result = munmap_function(address, size)
    assert result == 0
