i386 = {
    "brk": 45,
    "mmap": 192,  # sys_mmap_pgoff
    "munmap": 91,
}
amd64 = {
    "brk": 12,
    "mmap": 9,
    "munmap": 11,
}
armv7 = {
    "brk": 45,
    "mmap": 192,  # sys_mmap2
    "munmap": 91,
}
aarch64 = {
    "brk": 214,
    "mmap": 222,
    "munmap": 215,
}
