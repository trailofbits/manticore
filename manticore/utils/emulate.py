
import logging

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
        self._emu = self._unicorn()
        self._undo_list = []
        self._mapped = []
        self._to_raise = None
        #self._should_try_again = False

    def _unicorn(self):
        if self._cpu.arch == CS_ARCH_ARM:
            return Uc(UC_ARCH_ARM, UC_MODE_ARM)
        elif self._cpu.arch == CS_ARCH_X86:
            if self._cpu.mode == CS_MODE_32:
                return Uc(UC_ARCH_X86, UC_MODE_32)
            elif self._cpu.mode == CS_MODE_64:
                return Uc(UC_ARCH_X86, UC_MODE_64)
        
        raise RuntimeError("Unsupported architecture")


    def _create_emulated_mapping(self, uc, address, size=None):
        m = self._cpu.memory.map_containing(address)

        if m.start in self._mapped:
            return m

        # We might be modifying memory (even read-only), set all permissions
        permissions = UC_PROT_WRITE | UC_PROT_READ | UC_PROT_EXEC

        uc.mem_map(m.start, len(m), permissions)
        self._mapped.append(m.start)
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

        # Make sure the memory we're reading or writing is mapped
        m = self._create_emulated_mapping(uc, address, size)

        if access == UC_MEM_WRITE:
            self._cpu.write_int(address, value, size*8)
        elif access == UC_MEM_READ:
            value = self._cpu.read_bytes(address, size)
            uc.mem_write(address, ''.join(value))
        else:
            # XXX(yan): Does this need handling?
            pass

        return True


    def _hook_read_unmapped(self, uc, access, address, size, value, data):
        '''
        We hit an unmapped region; map it into unicorn. If we tried to 
        execute from a set of addresses to handle Linux intrinsics, raise
        the appropriate exception.

        '''

        if not self._cpu.memory.access_ok(slice(address, address+size), 'r'):
            # TODO(yan): handle this in a different place
            if self._cpu.arch == CS_ARCH_ARM:
                from ..models.linux import Linux
                special_addrs = (Linux.ARM_GET_TLS, Linux.ARM_CMPXCHG, Linux.ARM_MEM_BARRIER)
                if address in special_addrs:
                    # We are trying to execute from a special ARM value;
                    # map it so we don't keep hitting this hook
                    uc.mem_map(address & ~0xFFF, 0x1000)

                    from ..core.cpu.abstractcpu import InvalidPCException
                    self._to_raise = InvalidPCException(address)
                else:
                    self._to_raise = MemoryException("Can't read at", address)

            self._should_try_again = False
            return False

        # XXX(yan): handle if this points to an incorrect mapping
        self._create_emulated_mapping(uc, address, size)

        read_bytes = self._cpu.read_bytes(address, size)
        for address, byte in enumerate(read_bytes, start=address):
            if issymbolic(byte):
                # TODO(yan): This raises an exception for each byte of symbolic
                # memory; we should be batching
                from ..core.cpu.abstractcpu import ConcretizeMemory
                self._to_raise = ConcretizeMemory(address, 8,
                                                  "Concretizing for emulation")
                self._should_try_again = False
                return False

        # XXX(yan): This might need to be uncommented.
        #uc.mem_write(address, ''.join(read_bytes))

        self._should_try_again = True
        return True

    def _hook_write_unmapped(self, uc, access, address, size, value, data):
        '''
        If we're about to write to unmapped memory, map it in and try again.
        '''
        m = self._create_emulated_mapping(uc, address, size)
        self._should_try_again = True
        return True


    def _interrupt(self, uc, number, data):
        '''
        Handle software interrupt
        '''
        from ..core.cpu.abstractcpu import Interruption
        self._to_raise = Interruption(number)
        return True

    def emulate(self, instruction):
        def _to_unicorn_id(reg_name):
            # TODO(felipe, yan): Register naming is broken in current unicorn
            # packages, but works on unicorn git's master. We leave this hack
            # in until unicorn gets updated.
            if unicorn.__version__ <= '1.0.0' and reg_name == 'APSR':
                reg_name = 'CPSR'
            if self._cpu.arch == CS_ARCH_ARM:
                return globals()['UC_ARM_REG_' + reg_name]
            elif self._cpu.arch == CS_ARCH_X86:
                # TODO(yan): This needs to handle AF regiseter
                return globals()['UC_X86_REG_' + reg_name]
            else:
                # TODO(yan): raise a more appropriate exception
                raise TypeError

        self._emu = self._unicorn()

        registers = set(self._cpu.canonical_registers)

        # Refer to EFLAGS instead of individual flags for x86
        if self._cpu.arch == CS_ARCH_X86:
            # The last 8 canonical registers of x86 are individual flags; replace
            # with the eflags
            registers -= set(['CF','PF','AF','ZF','SF','IF','DF','OF'])
            registers.add('EFLAGS')

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
            self._emu.reg_write(_to_unicorn_id(reg), val)


        m = self._create_emulated_mapping(self._emu, self._cpu.PC, instruction.size)
        text_bytes = self._cpu.read_bytes(self._cpu.PC, instruction.size)
        self._emu.mem_write(self._cpu.PC, ''.join(text_bytes))

        self._emu.hook_add(UC_HOOK_MEM_UNMAPPED,       self._hook_read_unmapped)
        self._emu.hook_add(UC_HOOK_MEM_WRITE,          self._hook_xfer_mem)
        self._emu.hook_add(UC_HOOK_MEM_WRITE_UNMAPPED, self._hook_write_unmapped)
        self._emu.hook_add(UC_HOOK_MEM_READ,           self._hook_xfer_mem)
        self._emu.hook_add(UC_HOOK_INTR,               self._interrupt)

        saved_PC = self._cpu.PC

        try:
            while True:
                ctx = self._emu.context_save()
                self._should_try_again = False
                # If one of the hooks triggers an error, it might signal that we
                # should attempt to re-execute the instruction. This can happen
                # if memory needs to be mapped into Unicorn state.
                self._emu.emu_start(self._cpu.PC, self._cpu.PC+instruction.size, count=1)

                if not self._should_try_again:
                    break

                # If we are trying again, restore context
                self._emu.emu_stop()
                self._emu.context_restore(ctx)

        except UcError as e:
            if e.errno == UC_ERR_WRITE_UNMAPPED:
                raise MemoryException(repr(e), 0)
            else:
                # XXX(yan): We might need to raise here
                pass

        if logger.getEffectiveLevel() == logging.DEBUG:
            logger.debug("="*10)
            for register in self._cpu.canonical_registers:
                logger.debug("Register % 3s  Manticore: %08x, Unicorn %08x",
                        register, self._cpu.read_register(register),
                        self._emu.reg_read(_to_unicorn_id(register)) )
            logger.debug(">"*10)

        # Bring back Unicorn registers to Manticore
        for reg in registers:
            val = self._emu.reg_read(_to_unicorn_id(reg))
            self._cpu.write_register(reg, val)

        #Unicorn hack. On single step unicorn wont advance the PC register
        mu_pc = self.get_unicorn_pc()
        if saved_PC == mu_pc:
            self._cpu.PC += instruction.size

        if self._to_raise:
            raise self._to_raise

        return

