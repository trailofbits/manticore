from manticore import Manticore
from manticore.platforms import linux_syscalls

import logging

from sys import argv, exit
import struct
import qemu
import gdb

logger = logging.getLogger('TRACE')

## We need to keep some complex objects in between hook invocations so we keep them
## as globals. Tracing is inherently a single-threaded process, so using a 
## manticore context would be heavier than needed.
stack_top = 0xc0000000
stack_size = 0x20000
initialized = False
last_instruction = None
in_helper = False

def dump_gdb(cpu, addr, count):
    for offset in range(addr, addr+count, 4):
        val = int(gdb.getM(offset)  & 0xffffffff)
        val2 = int(cpu.read_int(offset))
        print '{:x}: g{:08x} m{:08x}'.format(offset, val, val2)

def cmp_regs(cpu, should_print=False):
    '''
    Compare registers from a remote gdb session to current mcore.

    :param manticore.core.cpu Cpu: Current cpu
    :param bool should_print: Whether to print values to stdout
    :return: Whether or not any differences were detected
    :rtype: bool
    '''
    differing = False
    gdb_regs = gdb.getCanonicalRegisters()
    for name in sorted(gdb_regs):
        vg = gdb_regs[name]
        if name.endswith('psr'):
            name = 'apsr'
        v = cpu.read_register(name.upper())
        if should_print:
            print '{} gdb:{:x} mcore:{:x}'.format(name, vg, v)
        if vg != v:
            if should_print:
                print '^^ unequal'
            differing = True
    return differing

def on_after(state, last_instruction):
    '''
    Handle syscalls (import memory) and bail if we diverge
    '''
    global in_helper

    # Synchronize qemu state to manticore's after a system call
    if last_instruction.mnemonic == 'svc':
        writes = state.cpu.memory.pop_record_writes()
        logger.debug("Got %d writes", len(writes))
        for addr, val in writes:
            gdb.setByte(addr, val[0])
        for reg in state.cpu.canonical_registers:
            if reg.endswith('PSR'):
                continue
            val = state.cpu.read_register(reg)
            logger.debug("Writing: %s", repr(val))
            gdb.setR(reg, val)

        # Write return val to gdb
        gdb.setR('R0', state.cpu.R0)

    # Ignore Linux kernel helpers
    if (state.cpu.PC >> 16) == 0xffff:
        in_helper = True
        return

    # If we executed a few instructions of a helper, we need to sync Manticore's
    # state to GDB as soon as we stop executing a helper.
    if in_helper:
        for reg in state.cpu.canonical_registers:
            if reg.endswith('PSR'):
                continue
            # Don't sync pc
            if reg == 'R15':
                continue
            gdb.setR(reg, state.cpu.read_register(reg))
        in_helper = False

    if cmp_regs(state.cpu):
        cmp_regs(state.cpu, should_print=True)
        state.abandon()

def sync_svc(state, syscall):
    '''
    Mirror some service calls in manticore. 
    '''
    name = linux_syscalls.armv7[syscall]
    try:
        # Make sure mmap returns the same address
        if 'mmap' in name:
            returned = gdb.getR('R0')
            state.cpu.write_register('R0', returned)
        if 'exit' in name:
            return
    except ValueError:
        for reg in state.cpu.canonical_registers:
            print '{}: {:x}'.format(reg, state.cpu.read_register(reg))
        raise

    logger.debug('Syscall: {} {}'.format(syscall, linux_syscalls.armv7[syscall]))
    for i in range(4):
        logger.debug("R{}: {:x}".format(i, gdb.getR('R%d'%i)))

    state.cpu.memory.push_record_writes()

def initialize(state):
    '''
    Synchronize the stack and register state (manticore->qemu)
    '''
    gdb_regs = gdb.getCanonicalRegisters()
    logger.debug("Copying {} bytes in the stack..".format(stack_top - state.cpu.SP))
    stack_bottom = min(state.cpu.SP, gdb.getR('SP'))
    for address in range(stack_bottom, stack_top):
        b = state.cpu.read_int(address, 8)
        gdb.setByte(address, chr(b))

    logger.debug("Done")

    for gdb_reg in gdb_regs:
        if gdb_reg.endswith('psr'):
            mcore_reg = 'APSR'
        else:
            mcore_reg = gdb_reg.upper()
        value = state.cpu.read_register(mcore_reg)
        gdb.setR(gdb_reg, value)


def verify(argv):
    logger.debug("Verifying program \"{}\"".format(argv))

    # Address and stack_size are from linux.py
    # TODO(yan): Refactor these constants into a reachable value in platform
    qemu.start('arm', argv, va_size=stack_top, stack_size=stack_size)
    gdb.start('arm', argv)

    m = Manticore(argv[0], argv[1:])
    m.verbosity = 2
    logger.setLevel(logging.DEBUG)

    @m.hook(None)
    def on_instruction(state):
        global initialized, last_instruction

        # Initialize our state to QEMU's
        if not initialized:
            initialize(state)
            initialized = True

        if last_instruction:
            on_after(state, last_instruction)

        last_instruction = state.cpu.instruction

        loc, instr = [x.strip() for x in gdb.getInstruction().split(':')]
        mnemonic = instr.split('\t')[0]
            
        # Capture syscall number before we run the syscall
        syscall = gdb.getR('R7')

        # Kernel helpers are inline in QEMU
        if (state.cpu.PC >> 16) != 0xffff:
            gdb.stepi()

        if mnemonic == 'svc':
            sync_svc(state, syscall)

    m.run()

if __name__ == "__main__":
    args = argv[1:]

    if len(args) == 0:
        print "usage: python {} PROGRAM1 ...".format(argv[0])
        exit()

    verify(args)

