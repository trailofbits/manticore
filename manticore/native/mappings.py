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
mmap_function.argtype = [
    ctypes.c_void_p,
    ctypes.c_size_t,
    ctypes.c_int,
    ctypes.c_int,
    ctypes.c_int,
    ctypes.c_size_t,
]


# int munmap(void* addr, size_t len)
munmap_function = libc.munmap
munmap_function.restype = ctypes.c_int
munmap_function.argtype = [ctypes.c_void_p, ctypes.c_size_t]


def mmap(fd, offset, size):
    prot = MMAP.PROT_READ | MMAP.PROT_WRITE
    flags = MMAP.MAP_PRIVATE

    # When trying to map the contents of a file into memory, the offset must be a multiple of the page size (see
    # `man mmap`). So we need to align it before passing it to mmap(). Doing so also increases the size of the memory
    # area needed, so we need to account for that difference.
    aligned_offset = offset & ~0xFFF
    size += offset - aligned_offset

    if size & 0xFFF != 0:
        size = (size & ~0xFFF) + 0x1000
    assert size > 0

    result = mmap_function(0, size, prot, flags, fd, aligned_offset)
    assert result != ctypes.c_void_p(-1).value

    # Now when returning the pointer to the user, we need to skip the corrected offset so that the user doesn't end up
    # with a pointer to another region of the file than the one they requested.
    return ctypes.cast(result + offset - aligned_offset, ctypes.POINTER(ctypes.c_char))


def munmap(address, size):
    # When unmapping the memory area, we need to recover the pointer and the size that were given to mmap(). The
    # pointer can be recovered by aligning it on the page size. The size needs to be increased by that difference to
    # account for cases where the requested memory area was larger.
    address = ctypes.cast(address, ctypes.c_void_p).value
    aligned_address = address & ~0xFFF
    size += address - aligned_address
    assert size > 0
    aligned_address = ctypes.cast(aligned_address, ctypes.POINTER(ctypes.c_char))

    result = munmap_function(aligned_address, size)
    assert result == 0
