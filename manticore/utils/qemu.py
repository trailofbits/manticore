import copy
import traceback
import os
import sys
import time
import subprocess
import logging


logger = logging.getLogger("QEMU")

count = 0

subproc = None
prog = ''
stats = None
_arch = None

def set_program(_prog):
    global prog
    prog = _prog

def get_lines(n=1):
    lines = []
    str_buffer = ''
    received_lines = 0
    while received_lines < n:
        c = subproc.stdout.read(1)
        str_buffer += c
        if c == '\n':
            lines.append(str_buffer)
            str_buffer = ''
            received_lines += 1

    return lines

def parse_mmu_debug_output(s):
    d = {}

    # Get guest address space
    d['reserved'] = int(s.pop(0).split()[1], 0)
    d['host_mmap_min_addr'] = int(s.pop(0).split('=')[1], 0)
    d['guest_base'] = int(s.pop(0).split()[1], 0)

    # get rid of mapping heading
    s.pop(0)
    d['maps'] = []
    
    while '-' in s[0]:
        line = s.pop(0)
        range, size, protections = line.split()
        start, end = range.split('-')
        d['maps'].append((int(start, 16),
                          int(end, 16),
                          int(size, 16),
                          protections))

    while s:
        line = s.pop(0)
        if not line:
            continue
        var, addr = line.split()
        d[var] = int(addr, 0)

    return d


def start(arch, port=1234):
    global subproc, stats
    aslr_file = '/proc/sys/kernel/randomize_va_space'
    try:
        with open(aslr_file, 'r') as f:
            if f.read().strip() != '0':
                logger.warning("Disable ASLR before running qemu-user")
                logger.warning("  sudo sh -c 'echo 0 > %s'", aslr_file)
    finally:
        pass
                    
    args = ['qemu-%s'%(arch,), '-g', str(port), '-d', 'mmu', prog]
    logger.debug("Running: %s"%(' '.join(args),))
    subproc = subprocess.Popen(args, env={}, stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE,
                                     stderr=subprocess.STDOUT)
    mmu_debug_output = get_lines(16)

    stats = parse_mmu_debug_output(mmu_debug_output)

def correspond(text):
    """Communicate with the child process without closing stdin."""
    if text:
        subproc.stdin.write(text)
    subproc.stdin.flush()
    return get_lines()
