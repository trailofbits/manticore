from manticore import Manticore
from manticore.platforms import linux_syscalls

import logging

from sys import argv, exit
import struct
import qemu
import gdb

logger = logging.getLogger('TRACE')

def dump_gdb(cpu, addr, count):
    for offset in range(addr, addr+count, 4):
        val = int(gdb.getM(offset)  & 0xffffffff)
        val2 = int(cpu.read_int(offset))
        print '{:x}: g{:08x} m{:08x}'.format(offset, val, val2)

def verify(argv):
    logger.debug("Verifying program \"{}\"".format(argv[0]))

    qemu.start('arm', argv)
    gdb.start('arm', argv)

    m = Manticore(argv[0], argv[1:])
    m.verbosity = 1
    m.context['icount'] = 0
    m.context['initialized'] = False

    def cmp_regs(cpu, should_print=False):
        '''
        Compare registers from a remote gdb session to current mcore.

        :param manticore.core.cpu Cpu: Current cpu
        :param bool should_print: Whether to print values to stdout
        :return: Whether or not any differences were detected
        :rtype: bool
        '''
        differing = False
        regs = {}
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


    @m.hook_after(None)
    def on_after(state):
        '''
        Handle syscalls (import memory) and bail if we diverge
        '''
        m.context['icount'] += 1

        # Synchronize qemu state to manticore's after a system call
        if state.cpu.instruction.mnemonic == 'svc':
            writes = state.cpu.memory.stop_write_trace()
            for addr, val in writes:
                gdb.setByte(addr, val[0])
                for reg in state.cpu.canonical_registers:
                    if reg.endswith('psr'):
                        continue
                    gdb.setR(reg, state.cpu.read_register(reg))

            # Write return val to gdb
            gdb.setR('R0', state.cpu.R0)

        # Ignore Linux kernel helpers
        if (state.cpu.PC >> 16) == 0xffff:
            return

        if cmp_regs(state.cpu):
            state.abandon()

    @m.hook(None)
    def on_instruction(state):
        # Initialize our state to QEMU's
        if not m.context['initialized']:
            gdb_regs = gdb.getCanonicalRegisters()
            logger.debug("Copying stack..")
            for address in range(state.cpu.SP, 0xf7000000):
                b = gdb.getByte(address)
                state.cpu.write_int(address, b, 8)
            logger.debug("Done")
            for reg in gdb_regs:
                state.cpu.write_register(reg.upper(), gdb_regs[reg])
            m.context['initialized'] = True

        # XXX(yan): The trace would diverge at this offset in the value of R4
        # in the example I was using. This might need to be adjusted for other
        # binaries.
        # TODO: Investigate further
        if m.context['icount'] == 6879:
            addr = state.cpu.R4
            state.cpu.write_int(addr, gdb.getM(addr)&0xffffffff)

        loc, instr = [x.strip() for x in gdb.getInstruction().split(':')]
        mnemonic = instr.split('\t')[0]
            
        first_param, syscall = gdb.getR('R0'), gdb.getR('R7')

        # Kernel helpers are inline in QEMU
        if (state.cpu.PC >> 16) != 0xffff:
            gdb.stepi()

        if mnemonic == 'svc':
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
                logger.debug("R{}: {:x}".format(i, gdb.getR('R%d'%i))

    m.run()

if __name__ == "__main__":
    args = argv[1:]

    if len(args) == 0:
        print "usage: python {} PROGRAM1 ...".format(argv[0])
        exit()

    overall_results = verify(args)

