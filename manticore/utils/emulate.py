import logging
import inspect

from ..core.memory import MemoryException, FileMap, AnonMap
from ..core.smtlib import Operators

from .helpers import issymbolic
######################################################################
# Abstract classes for capstone/unicorn based cpus
# no emulator by default
from unicorn import *
from unicorn.x86_const import *
from unicorn.arm_const import *

from capstone import *
from capstone.arm import *
from capstone.x86 import *

import pprint as pp
import struct

logger = logging.getLogger("EMULATOR")

class UnicornEmulator(object):
    '''
    Helper class to emulate a single instruction via Unicorn.
    '''
    def __init__(self, cpu):
        self._cpu = cpu
        self.flag_registers = set(['CF','PF','AF','ZF','SF','IF','DF','OF'])

        text = cpu.memory.map_containing(cpu.PC)
        cpu.subscribe('did_write_memory', self.write_back_memory)
        cpu.subscribe('did_write_register', self.write_back_register)
        cpu.subscribe('did_set_descriptor', self.update_segment)
        # Keep track of all memory mappings. We start with just the text section
        self.mem_map = {}
        for m in cpu.memory.maps:
            if True:#type(m) is FileMap:
                permissions = UC_PROT_NONE
                if 'r' in m.perms:
                    permissions |= UC_PROT_READ
                if 'w' in m.perms:
                    permissions |= UC_PROT_WRITE
                if 'x' in m.perms:
                    permissions |= UC_PROT_EXEC
                self.mem_map[m.start] = (len(m), permissions)

        # Keep track of all the memory Unicorn needs while executing this
        # instruction
        self._should_be_written = {}

        # Establish Manticore state, potentially from past emulation
        # attempts
        self.reset()
        for base in self.mem_map:
            size, perms = self.mem_map[base]
            print("About to map %s bytes from %02x to %02x" % (size, base, base + size))
            self._emu.mem_map(base, size, perms)

        self._emu.hook_add(UC_HOOK_MEM_READ_UNMAPPED,  self._hook_unmapped)
        self._emu.hook_add(UC_HOOK_MEM_WRITE_UNMAPPED, self._hook_unmapped)
        self._emu.hook_add(UC_HOOK_MEM_FETCH_UNMAPPED, self._hook_unmapped)
        # self._emu.hook_add(UC_HOOK_MEM_READ,           self._hook_xfer_mem)
        self._emu.hook_add(UC_HOOK_MEM_WRITE,          self._hook_xfer_mem)
        self._emu.hook_add(UC_HOOK_INTR,               self._interrupt)

        self.registers = set(self._cpu.canonical_registers)

        # Refer to EFLAGS instead of individual flags for x86
        if self._cpu.arch == CS_ARCH_X86:
            # The last 8 canonical registers of x86 are individual flags; replace
            # with the eflags
            self.registers -= self.flag_registers
            self.registers.add('EFLAGS')

            # TODO(mark): Unicorn 1.0.1 does not support reading YMM registers,
            # and simply returns back zero. If a unicorn emulated instruction writes to an
            # XMM reg, we will read back the corresponding YMM register, resulting in an
            # incorrect zero value being actually written to the XMM register. This is
            # fixed in Unicorn PR #819, so when that is included in a release, delete
            # these two lines.
            self.registers -= set(['YMM0', 'YMM1', 'YMM2', 'YMM3', 'YMM4', 'YMM5', 'YMM6', 'YMM7', 'YMM8', 'YMM9', 'YMM10', 'YMM11', 'YMM12', 'YMM13', 'YMM14', 'YMM15'])
            self.registers |= set(['XMM0', 'XMM1', 'XMM2', 'XMM3', 'XMM4', 'XMM5', 'XMM6', 'XMM7', 'XMM8', 'XMM9', 'XMM10', 'XMM11', 'XMM12', 'XMM13', 'XMM14', 'XMM15'])

        print("Setting initial register state")
        for reg in self.registers:
            val = self._cpu.read_register(reg)
            if issymbolic(val):
                from ..core.cpu.abstractcpu import ConcretizeRegister
                raise ConcretizeRegister(self._cpu, reg, "Concretizing for emulation.",
                                         policy='ONE')
            self._emu.reg_write(self._to_unicorn_id(reg), val)

        self.create_GDT()
        for index, m in enumerate(self.mem_map):
            size = self.mem_map[m][0]
            print("Reading map %s (%s kb)" % (index, size / 1024))
            map_bytes = self._cpu.read_bytes(m, size)
            print("Writing map %s" % index)
            self._emu.mem_write(m, ''.join(map_bytes))
        print("Unicorn init complete")

    def reset(self):
        self._emu = self._unicorn()
        self._to_raise = None

    def _unicorn(self):
        if self._cpu.arch == CS_ARCH_ARM:
            if self._cpu.mode == CS_MODE_ARM:
                return Uc(UC_ARCH_ARM, UC_MODE_ARM)
            elif self._cpu.mode == CS_MODE_THUMB:
                return Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        elif self._cpu.arch == CS_ARCH_X86:
            if self._cpu.mode == CS_MODE_32:
                return Uc(UC_ARCH_X86, UC_MODE_32)
            elif self._cpu.mode == CS_MODE_64:
                return Uc(UC_ARCH_X86, UC_MODE_64)

        raise RuntimeError("Unsupported architecture")


    def in_map(self, addr):
        for m in self.mem_map:
            if addr >= m and addr <= (m + self.mem_map[m][0]):
                return True
        return False

    def _create_emulated_mapping(self, uc, address):
        '''
        Create a mapping in Unicorn and note that we'll need it if we retry.

        :param uc: The Unicorn instance.
        :param address: The address which is contained by the mapping.
        :rtype Map
        '''

        m = self._cpu.memory.map_containing(address)
        if m.start not in self.mem_map.keys():
            permissions = UC_PROT_NONE
            if 'r' in m.perms:
                permissions |= UC_PROT_READ
            if 'w' in m.perms:
                permissions |= UC_PROT_WRITE
            if 'x' in m.perms:
                permissions |= UC_PROT_EXEC
            print("About to map %s bytes from %02x to %02x" % (len(m), m.start, m.start + len(m)))
            uc.mem_map(m.start, len(m), permissions)

            self.mem_map[m.start] = (len(m), permissions)

        return m

    def get_unicorn_pc(self):
        if self._cpu.arch == CS_ARCH_ARM:
            return self._emu.reg_read(UC_ARM_REG_R15)
        elif self._cpu.arch == CS_ARCH_X86:
            if self._cpu.mode == CS_MODE_32:
                return self._emu.reg_read(UC_X86_REG_EIP)
            elif self._cpu.mode == CS_MODE_64:
                return self._emu.reg_read(UC_X86_REG_RIP)


    def _hook_xfer_mem(self, uc, access, address, size, value, data):
        '''
        Handle memory operations from unicorn.
        '''
        assert access in (UC_MEM_WRITE, UC_MEM_READ, UC_MEM_FETCH)

        if access == UC_MEM_WRITE:
            print("Writing %s bytes to %02x: %02x" % (size, address, value))
            self._cpu.write_int(address, value, size*8)

        # If client code is attempting to read a value, we need to bring it
        # in from Manticore state. If we try to mem_write it here, Unicorn
        # will segfault. We add the value to a list of things that need to
        # be written, and ask to restart the emulation.
        # elif access == UC_MEM_READ:
        #     print("Reading %s bytes from %02x: %02x" % (size, address, value))
        #     value = self._cpu.read_bytes(address, size)
        #
        #     if address in self._should_be_written:
        #         return True
        #
        #     self._should_be_written[address] = value
        #
        #     self._should_try_again = True
        #     return False

        return True


    def _hook_unmapped(self, uc, access, address, size, value, data):
        '''
        We hit an unmapped region; map it into unicorn.
        '''

        try:
            print("Mapping memory at " + hex(address))
            m = self._create_emulated_mapping(uc, address)
        except MemoryException as e:
            print("Failed to map memory")
            self._to_raise = e
            self._should_try_again = False
            return False

        self._should_try_again = True
        return False

    def _interrupt(self, uc, number, data):
        '''
        Handle software interrupt (SVC/INT)
        '''
        print("Caught interrupt: %s" % number)
        from ..core.cpu.abstractcpu import Interruption
        self._to_raise = Interruption(number)
        return True

    def _to_unicorn_id(self, reg_name):
        # TODO(felipe, yan): Register naming is broken in current unicorn
        # packages, but works on unicorn git's master. We leave this hack
        # in until unicorn gets updated.
        if unicorn.__version__ <= '1.0.0' and reg_name == 'APSR':
            reg_name = 'CPSR'
        if self._cpu.arch == CS_ARCH_ARM:
            return globals()['UC_ARM_REG_' + reg_name]
        elif self._cpu.arch == CS_ARCH_X86:
            # TODO(yan): This needs to handle AF register
            custom_mapping = {'PC':'RIP'}
            try:
                return globals()['UC_X86_REG_' + reg_name]
            except KeyError:
                try:
                    return globals()['UC_X86_REG_' + custom_mapping[reg_name]]
                except:
                    print 'UC_X86_REG_' + str(reg_name) + ' not in '
                    pp.pprint([k for k in globals() if 'UC_X86_REG' in k])
                    raise

        else:
            # TODO(yan): raise a more appropriate exception
            raise TypeError

    def emulate(self, instruction):
        '''
        Emulate a single instruction.
        '''

        # The emulation might restart if Unicorn needs to bring in a memory map
        # or bring a value from Manticore state.
        while True:
            for address, values in self._should_be_written.items():
                for offset, byte in enumerate(values, start=address):
                    if issymbolic(byte):
                        from ..core.cpu.abstractcpu import ConcretizeMemory
                        raise ConcretizeMemory(self._cpu.memory, offset, 8,
                                               "Concretizing for emulation")

                self._emu.mem_write(address, ''.join(values))

            # Try emulation
            self._should_try_again = False

            self._step(instruction)

            if not self._should_try_again:
                break


    def _step(self, instruction):
        '''
        A single attempt at executing an instruction.
        '''
        # XXX(yan): This concretizes the entire register state. This is overly
        # aggressive. Once capstone adds consistent support for accessing
        # referred registers, make this only concretize those registers being
        # read from.
        # for reg in self.registers:
        #     val = self._cpu.read_register(reg)
        #     if issymbolic(val):
        #         from ..core.cpu.abstractcpu import ConcretizeRegister
        #         raise ConcretizeRegister(self._cpu, reg, "Concretizing for emulation.",
        #                                  policy='ONE')
        #     self._emu.reg_write(self._to_unicorn_id(reg), val)

        # Bring in the instruction itself
        instruction = self._cpu.decode_instruction(self._cpu.PC)

        saved_PC = self._cpu.PC

        try:
            self._emu.emu_start(self._cpu.PC, self._cpu.PC+instruction.size, count=1)
        except UcError as e:
            # We request re-execution by signaling error; if we we didn't set
            # _should_try_again, it was likely an actual error
            if not self._should_try_again:
                raise

        if self._should_try_again:
            return

        if logger.isEnabledFor(logging.DEBUG):
            logger.debug("="*10)
            for register in self._cpu.canonical_registers:
                logger.debug("Register % 3s  Manticore: %08x, Unicorn %08x",
                        register, self._cpu.read_register(register),
                        self._emu.reg_read(self._to_unicorn_id(register)) )
            logger.debug(">"*10)

        # Bring back Unicorn registers to Manticore
        for reg in self.registers:
            val = self._emu.reg_read(self._to_unicorn_id(reg))
            self._cpu.write_register(reg, val)

        #Unicorn hack. On single step unicorn wont advance the PC register
        # mu_pc = self.get_unicorn_pc()
        # if saved_PC == mu_pc:
        #     self._cpu.PC = saved_PC + instruction.size

        # Raise the exception from a hook that Unicorn would have eaten
        if self._to_raise:
            print("Raising %s" % self._to_raise)
            raise self._to_raise

        return

    def sync_unicorn_to_manticore(self):
        for reg in self.registers:
            oldval = self._cpu.read_register(reg)
            if issymbolic(oldval):
                from ..core.cpu.abstractcpu import ConcretizeRegister
                raise ConcretizeRegister(self._cpu, reg, "Concretizing for emulation.",
                                         policy='ONE')
            val = self._emu.reg_read(self._to_unicorn_id(reg))
            if val != oldval:
                print("(M) %s: %s -> %s" % (reg, oldval, val))
            self._cpu.write_register(reg, val)

    def write_back_memory(self, where, expr, size):
        if issymbolic(expr):
            print("Concretizing memory")
            from ..core.memory import ConcretizeMemory
            raise ConcretizeMemory(self._cpu.memory, where, size, policy='ONE')
            # data = '+'*(size/8)
        # else:
        data = [Operators.CHR(Operators.EXTRACT(expr, offset, 8)) for offset in xrange(0, size, 8)]
        # print(data)
        # print("Writing back %s bits to %02x: %s" % (size, where, ''.join(data)))
        if not self.in_map(where):
            self._create_emulated_mapping(self._emu, where)
        self._emu.mem_write(where, ''.join(data))

    def write_back_register(self, reg, val):
        if reg in self.flag_registers:
            self._emu.reg_write(self._to_unicorn_id('EFLAGS'), self._cpu.read_register('EFLAGS'))
            return
        oldval = self._emu.reg_read(self._to_unicorn_id(reg))
        if oldval != val:
            print("(U) %s: %s -> %s" % (reg, oldval, val))
        self._emu.reg_write(self._to_unicorn_id(reg), val)

    def update_segment(self, selector, base, size, perms):
        print("(U) Updating selector %s to 0x%02x (%s bytes) (%s)" % (selector, base, size, perms))
        dest = self.gdt_base + (selector*8)
        entry = self.make_table_entry(base, size)
        self._emu.mem_write(dest, entry)


    def make_table_entry(self, base, limit, access_byte=0xff, flags=0xf0):
        # http://wiki.osdev.org/Global_Descriptor_Table#Structure
        out = 0
        out |= (limit & 0xffff)
        out |= ((base & 0xffffff) << 16)
        out |= ((access_byte & 0xff) << 40)
        out |= (((limit >> 16) & 0xf) << 48)
        out |= ((flags & 0xff) << 52)
        out |= (((base >> 24) & 0xff) << 56)
        return struct.pack('<Q', out)

    def create_GDT(self, base=0x1000, size=8192):
        self.gdt_base = base
        self.gdt_size = size

        self._emu.mem_map(base, size)
        self._emu.reg_write(UC_X86_REG_GDTR, (0, base, size, 0))
