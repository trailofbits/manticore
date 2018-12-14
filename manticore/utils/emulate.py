import logging
import inspect

from ..native.memory import MemoryException, FileMap, AnonMap
from ..core.smtlib import Operators, solver

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

import time

logger = logging.getLogger(__name__)
logger.setLevel(logging.INFO)

# https://stackoverflow.com/a/1094933
def sizeof_fmt(num, suffix='B'):
    for unit in ' KMGTPEZ':
        if abs(num) < 1024.0:
            return "%3.1f%s%s" % (num, unit if unit != ' ' else '', suffix)
        num /= 1024.0
    return "%.1f%s%s" % (num, 'Y', suffix)


class ConcreteUnicornEmulator(object):
    '''
    Helper class to emulate instructions in bulk via Unicorn.
    '''
    def __init__(self, cpu):
        self.init_time = time.time()
        self.out_of_step_time = self.init_time - self.init_time
        self.in_step_time = self.out_of_step_time
        self.sync_time = self.in_step_time

        self._cpu = cpu
        self._mem_delta = {}
        self.flag_registers = set(['CF','PF','AF','ZF','SF','IF','DF','OF'])

        cpu.subscribe('did_write_memory', self.write_back_memory)
        cpu.subscribe('did_write_register', self.write_back_register)
        cpu.subscribe('did_set_descriptor', self.update_segment)
        cpu.subscribe('will_execute_instruction', self.pre_execute_callback)
        cpu.subscribe('did_map_memory', self.map_memory_callback)
        cpu.subscribe('did_execute_instruction', self.post_execute_callback)

        if self._cpu.arch == CS_ARCH_X86:
            self._uc_arch = UC_ARCH_X86
            self._uc_mode = {
                CS_MODE_32: UC_MODE_32,
                CS_MODE_64: UC_MODE_64
            }[self._cpu.mode]
        else:
            raise NotImplementedError(f'Unsupported architecture: {self._cpu.arch}')

        self.reset()

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

        # Establish Manticore state, potentially from past emulation
        # attempts
        for base in self.mem_map:
            size, perms = self.mem_map[base]
            self._emu.mem_map(base, size, perms)

        self._emu.hook_add(UC_HOOK_MEM_READ_UNMAPPED,  self._hook_unmapped)
        self._emu.hook_add(UC_HOOK_MEM_WRITE_UNMAPPED, self._hook_unmapped)
        self._emu.hook_add(UC_HOOK_MEM_FETCH_UNMAPPED, self._hook_unmapped)
        self._emu.hook_add(UC_HOOK_MEM_WRITE,          self._hook_xfer_mem)
        self._emu.hook_add(UC_HOOK_INTR,               self._interrupt)

        self.registers = set(self._cpu.canonical_registers)
        # The last 8 canonical registers of x86 are individual flags; replace with the eflags
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

        for reg in self.registers:
            val = self._cpu.read_register(reg)
            if issymbolic(val):
                from ..core.cpu.abstractcpu import ConcretizeRegister
                raise ConcretizeRegister(self._cpu, reg, "Concretizing for emulation.",
                                         policy='ONE')
            logger.debug("Writing %s into %s", val, reg)
            self._emu.reg_write(self._to_unicorn_id(reg), val)

        for m in self.mem_map:
            size = self.mem_map[m][0]
            self.copy_map(m, size)

        self.init_time = time.time() - self.init_time
        self._last_step_time = time.time()

    def reset(self):
        self._emu = Uc(self._uc_arch, self._uc_mode)
        self._to_raise = None

    def in_map(self, addr):
        for m in self.mem_map:
            if addr >= m and addr <= (m + self.mem_map[m][0]):
                return True
        return False

    def copy_map(self, address, size):
        # map = self._cpu.memory.map_containing(address)
        # if type(map) is FileMap:
        #     permissions = UC_PROT_NONE
        #     if 'r' in map.perms:
        #         permissions |= UC_PROT_READ
        #     if 'w' in map.perms:
        #         permissions |= UC_PROT_WRITE
        #     if 'x' in map.perms:
        #         permissions |= UC_PROT_EXEC
        #     self._emu.mem_map_ptr(address, size, permissions, map._data)

        start_time = time.time()
        map_bytes = self._cpu._raw_read(address, size)
        logger.info("Reading %s map at 0x%02x took %s seconds", sizeof_fmt(size), address, time.time() - start_time)
        self._emu.mem_write(address, map_bytes)

    def map_memory_callback(self, address, size, perms, name, offset, result):
        logger.info(' '.join(("Mapping Memory @",
              hex(address) if type(address) is int else "0x??",
              sizeof_fmt(size), "-",
              perms, "-",
              f"{name}:{hex(offset) if name else ''}", "->",
              hex(result))))
        if address not in self.mem_map.keys() and address is not None:
            self.copy_mapping_to_unicorn(address)
            self.copy_map(address, size)


    def copy_mapping_to_unicorn(self, address):
        '''
        Create a mapping in Unicorn and note that we'll need it if we retry.

        :param address: The address which is contained by the mapping.
        :rtype Map
        '''

        m = self._cpu.memory.map_containing(address)
        size = m.end - m.start
        if m.start not in self.mem_map.keys():
            logger.info(f"Creating {sizeof_fmt(size)} map @ {hex(m.start)} in Unicorn")
            permissions = UC_PROT_NONE
            if 'r' in m.perms:
                permissions |= UC_PROT_READ
            if 'w' in m.perms:
                permissions |= UC_PROT_WRITE
            if 'x' in m.perms:
                permissions |= UC_PROT_EXEC
            self._emu.mem_map(m.start, size, permissions)

            self.mem_map[m.start] = (size, permissions)

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
            self._mem_delta[address] = (value, size)

        return True

    def _hook_unmapped(self, uc, access, address, size, value, data):
        '''
        We hit an unmapped region; map it into unicorn.
        '''
        try:
            m = self.copy_mapping_to_unicorn(address)
            self.copy_map(m.start, m.size)
        except MemoryException as e:
            logger.error("Failed to map memory {}-{}, ({}): {}".format(hex(address), hex(address + size), access, e))
            self._to_raise = e
            self._should_try_again = False
            return False

        self._should_try_again = True
        return False

    def _interrupt(self, uc, number, data):
        '''
        Handle software interrupt (SVC/INT)
        '''
        logger.info("Caught interrupt: %s" % number)
        from ..native.cpu.abstractcpu import Interruption  # prevent circular imports
        self._to_raise = Interruption(number)
        return True

    def _to_unicorn_id(self, reg_name):
        if self._cpu.arch == CS_ARCH_ARM:
            return globals()['UC_ARM_REG_' + reg_name]
        elif self._cpu.arch == CS_ARCH_X86:
            # TODO(yan): This needs to handle AF register
            custom_mapping = {'PC':'RIP'}
            try:
                return globals()['UC_X86_REG_' + custom_mapping.get(reg_name, reg_name)]
            except KeyError:
                logger.error("Can't find register UC_X86_REG_%s", str(reg_name))
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

            # Try emulation
            self._should_try_again = False

            self._step(instruction)

            if not self._should_try_again:
                break

    def _step(self, instruction):
        '''
        A single attempt at executing an instruction.
        '''

        # Bring in the instruction itself
        instruction = self._cpu.decode_instruction(self._cpu.PC)

        try:
            pc = self._cpu.PC
            if self._cpu.arch == CS_ARCH_ARM and self._uc_mode == UC_MODE_THUMB:
                pc |= 1
            self._emu.emu_start(pc, self._cpu.PC + instruction.size, count=1)
        except UcError as e:
            # We request re-execution by signaling error; if we we didn't set
            # _should_try_again, it was likely an actual error
            if not self._should_try_again:
                raise

        if self._should_try_again:
            return

        if logger.isEnabledFor(logging.DEBUG):
            logger.debug("=" * 10)
            for register in self._cpu.canonical_registers:
                logger.debug("Register % 3s  Manticore: %08x, Unicorn %08x",
                        register, self._cpu.read_register(register),
                        self._emu.reg_read(self._to_unicorn_id(register)) )
            logger.debug(">"*10)

        # self.sync_unicorn_to_manticore()
        self._cpu.PC = self.get_unicorn_pc()

        # Raise the exception from a hook that Unicorn would have eaten
        if self._to_raise:
            logger.info("Raising %s", self._to_raise)
            raise self._to_raise

        return

    def sync_unicorn_to_manticore(self):
        start = time.time()
        for reg in self.registers:
            val = self._emu.reg_read(self._to_unicorn_id(reg))
            self._cpu.write_register(reg, val)
        for location in self._mem_delta:
            value, size = self._mem_delta[location]
            logger.debug("Writing %s bytes to 0x%02x", size, location)
            self._cpu.write_int(location, value, size*8)
        self._mem_delta = {}
        self.sync_time += (time.time() - start)

    def write_back_memory(self, where, expr, size):
        if where in self._mem_delta.keys():
            return
        if issymbolic(expr):
            data = [Operators.CHR(Operators.EXTRACT(expr, offset, 8)) for offset in range(0, size, 8)]
            concrete_data = []
            for c in data:
                if issymbolic(c):
                    c = chr(solver.get_value(self._cpu.memory.constraints, c))
                concrete_data.append(c)
            data = concrete_data
        else:
            data = [Operators.CHR(Operators.EXTRACT(expr, offset, 8)) for offset in range(0, size, 8)]
        logger.debug("Writing back %s bits to 0x%02x", size, where)
        if not self.in_map(where):
            self.copy_mapping_to_unicorn(where)
        # TODO - the extra encoding is to handle null bytes output as strings when we concretize. That's probably a bug.
        self._emu.mem_write(where, b''.join(b.encode('utf-8') if type(b) is str else b for b in data))

    def write_back_register(self, reg, val):
        if reg in self.flag_registers:
            self._emu.reg_write(self._to_unicorn_id('EFLAGS'), self._cpu.read_register('EFLAGS'))
            return
        self._emu.reg_write(self._to_unicorn_id(reg), val)

    def update_segment(self, selector, base, size, perms):
        logger.info("Updating selector %s to 0x%02x (%s bytes) (%s)", selector, base, size, perms)
        if selector == 99:
            self.set_fs(base)

    def set_fs(self, addr):
        '''
        set the FS.base hidden descriptor-register field to the given address.
        this enables referencing the fs segment on x86-64.
        '''
        FSMSR = 0xC0000100
        return self._emu.msr_write(FSMSR, addr)

    def pre_execute_callback(self, _pc, _insn):
        start_time = time.time()
        self.out_of_step_time += (start_time - self._last_step_time)
        self._last_step_time = start_time

    def post_execute_callback(self, _last_pc, _pc, _insn):
        start_time = time.time()
        self.in_step_time += (start_time - self._last_step_time)
        self._last_step_time = start_time