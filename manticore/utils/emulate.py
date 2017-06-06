
import logging
import inspect

from ..core.memory import MemoryException, FileMap, AnonMap

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

logger = logging.getLogger("EMULATOR")

class UnicornEmulator(object):
    '''
    Helper class to emulate a single instruction via Unicorn.
    '''
    def __init__(self, cpu):
        self._cpu = cpu

        text = cpu.memory.map_containing(cpu.PC)
        # Keep track of all memory mappings. We start with just the text section
        self._should_be_mapped = {
                text.start: (len(text), UC_PROT_READ | UC_PROT_EXEC)
        }

        # Keep track of all the memory Unicorn needs while executing this 
        # instruction
        self._should_be_written = {}

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


    def _create_emulated_mapping(self, uc, address):
        '''
        Create a mapping in Unicorn and note that we'll need it if we retry.

        :param uc: The Unicorn instance.
        :param address: The address which is contained by the mapping.
        :rtype Map
        '''

        m = self._cpu.memory.map_containing(address)

        permissions = UC_PROT_NONE
        if 'r' in m.perms:
            permissions |= UC_PROT_READ
        if 'w' in m.perms:
            permissions |= UC_PROT_WRITE
        if 'x' in m.perms:
            permissions |= UC_PROT_EXEC

        uc.mem_map(m.start, len(m), permissions)

        self._should_be_mapped[m.start] = (len(m), permissions)

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
            self._cpu.write_int(address, value, size*8)

        # If client code is attempting to read a value, we need to bring it
        # in from Manticore state. If we try to mem_write it here, Unicorn
        # will segfault. We add the value to a list of things that need to
        # be written, and ask to restart the emulation.
        elif access == UC_MEM_READ:
            value = self._cpu.read_bytes(address, size)

            if address in self._should_be_written:
                return True

            self._should_be_written[address] = value

            self._should_try_again = True
            return False

        return True


    def _hook_unmapped(self, uc, access, address, size, value, data):
        '''
        We hit an unmapped region; map it into unicorn.
        '''

        try:
            m = self._create_emulated_mapping(uc, address)
        except MemoryException as e:
            self._to_raise = e
            self._should_try_again = False
            return False

        self._should_try_again = True
        return False

    def _interrupt(self, uc, number, data):
        '''
        Handle software interrupt (SVC/INT)
        '''

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
            return globals()['UC_X86_REG_' + reg_name]
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

            self.reset()

            # Establish Manticore state, potentially from past emulation
            # attempts
            for base in self._should_be_mapped:
                size, perms = self._should_be_mapped[base]
                self._emu.mem_map(base, size, perms)

            for address, values in self._should_be_written.items():
                for offset, byte in enumerate(values, start=address):
                    if issymbolic(byte):
                        from ..core.cpu.abstractcpu import ConcretizeMemory
                        raise ConcretizeMemory(offset, 8,
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

        registers = set(self._cpu.canonical_registers)

        # Refer to EFLAGS instead of individual flags for x86
        if self._cpu.arch == CS_ARCH_X86:
            # The last 8 canonical registers of x86 are individual flags; replace
            # with the eflags
            registers -= set(['CF','PF','AF','ZF','SF','IF','DF','OF'])
            registers.add('EFLAGS')

            # TODO(mark): Unicorn 1.0.1 does not support reading YMM registers,
            # and simply returns back zero. If a unicorn emulated instruction writes to an
            # XMM reg, we will read back the corresponding YMM register, resulting in an
            # incorrect zero value being actually written to the XMM register. This is
            # fixed in Unicorn PR #819, so when that is included in a release, delete
            # these two lines.
            registers -= set(['YMM0', 'YMM1', 'YMM2', 'YMM3', 'YMM4', 'YMM5', 'YMM6', 'YMM7', 'YMM8', 'YMM9', 'YMM10', 'YMM11', 'YMM12', 'YMM13', 'YMM14', 'YMM15'])
            registers |= set(['XMM0', 'XMM1', 'XMM2', 'XMM3', 'XMM4', 'XMM5', 'XMM6', 'XMM7', 'XMM8', 'XMM9', 'XMM10', 'XMM11', 'XMM12', 'XMM13', 'XMM14', 'XMM15'])

        # XXX(yan): This concretizes the entire register state. This is overly
        # aggressive. Once capstone adds consistent support for accessing 
        # referred registers, make this only concretize those registers being
        # read from.
        for reg in registers:
            val = self._cpu.read_register(reg)
            if issymbolic(val):
                from ..core.cpu.abstractcpu import ConcretizeRegister
                raise ConcretizeRegister(reg, "Concretizing for emulation.",
                                         policy='ONE') 
            self._emu.reg_write(self._to_unicorn_id(reg), val)

        # Bring in the instruction itself
        text_bytes = self._cpu.read_bytes(self._cpu.PC, instruction.size)
        self._emu.mem_write(self._cpu.PC, ''.join(text_bytes))

        self._emu.hook_add(UC_HOOK_MEM_READ_UNMAPPED,  self._hook_unmapped)
        self._emu.hook_add(UC_HOOK_MEM_WRITE_UNMAPPED, self._hook_unmapped)
        self._emu.hook_add(UC_HOOK_MEM_FETCH_UNMAPPED, self._hook_unmapped)
        self._emu.hook_add(UC_HOOK_MEM_READ,           self._hook_xfer_mem)
        self._emu.hook_add(UC_HOOK_MEM_WRITE,          self._hook_xfer_mem)
        self._emu.hook_add(UC_HOOK_INTR,               self._interrupt)

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
        for reg in registers:
            val = self._emu.reg_read(self._to_unicorn_id(reg))
            self._cpu.write_register(reg, val)

        #Unicorn hack. On single step unicorn wont advance the PC register
        mu_pc = self.get_unicorn_pc()
        if saved_PC == mu_pc:
            self._cpu.PC = saved_PC + instruction.size

        # Raise the exception from a hook that Unicorn would have eaten
        if self._to_raise:
            raise self._to_raise

        return

