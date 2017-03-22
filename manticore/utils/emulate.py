
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
    def __init__(self, cpu):
        self._cpu = cpu
        self._emu = self._unicorn()
        self._undo_list = []
        self._written = []
        self._mapped = []
        self._to_raise = None
        self._should_try_again = False

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

        # We might be modifying memory, set all permissions
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
        

    def emulate(self, instruction):
        def _reg_id(reg_name):
            #FIXME FIXME FIXME
            #assert unicorn.__version__ <= '1.0.0', "If we are using unicorn greater than 1.0.0 we have ARM.APSR support
            #if unicorn.__version__ <= '1.0.0' and reg_name == 'APSR':
                #reg_name = 'CPSR'
            if self._cpu.arch == CS_ARCH_ARM:
                return globals()['UC_ARM_REG_' + reg_name]
            elif self._cpu.arch == CS_ARCH_X86:
                # TODO(yan): This needs to handle AF regiseter
                return globals()['UC_X86_REG_' + reg_name]
            else:
                # TODO(yan): raise a more appropriate exception
                raise TypeError

        self._emu = self._unicorn()

        # Copy in the concrete values of all needed registers.
        registers = set(self._cpu.canonical_registers)
        if self._cpu.arch == CS_ARCH_X86:
            # The last 8 canonical registers of x86 are individual flags; replace
            # with the eflags
            registers -= set(['CF','PF','AF','ZF','SF','IF','DF','OF'])

        for reg in registers:
            val = self._cpu.read_register(reg)
            if issymbolic(val):
                raise ConcretizeRegister(reg, "Concretizing register for emulation.") 
            self._emu.reg_write(_reg_id(reg), val)


        #Unicorn hack. On single step unicorn wont advance the PC register
        PC = self._cpu.PC

        m = self._create_emulated_mapping(self._emu, self._cpu.PC, instruction.size)
        self._emu.mem_write(PC, ''.join(m[PC:PC+instruction.size]))
        

        def _xfer_mem(uc, access, address, size, value, self):
            # XXX(yan): record memory writes to our own state and undo them if
            # we have to re-execute
            #print("_xfer_mem: access({}) address({:x}) size({}) value({})"
                    #.format(['write', 'read'][access == UC_MEM_READ], address, size, repr(value))

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

        def _read_unmapped(uc, access, address, size, value, self):
            '''
            We hit an unmapped region; map it into unicorn
            '''

            if not self._cpu.memory.access_ok(slice(address, address+size), 'r'):
                if self._cpu.arch == CS_ARCH_ARM:
                    from ..models.linux import Linux
                    if address in (Linux.ARM_GET_TLS, Linux.ARM_CMPXCHG,
                            Linux.ARM_MEM_BARRIER):
                        # We are trying to execute from a special ARM value;
                        # map it so we don't keep hitting this hook
                        uc.mem_map(address & ~0xFFF, 0x1000)

                        from ..core.cpu.abstractcpu import InvalidPCException
                        self._to_raise = InvalidPCException(address)
                        self._should_try_again = False

                        return False
                self._to_raise = MemoryException("Can't read at", address)
                self._should_try_again = False
                return False

            # XXX(yan): handle if this points to an incorrect mapping
            self._create_emulated_mapping(uc, address, size)

            bytes = self._cpu.read_bytes(address, size)
            uc.mem_write(address, ''.join(bytes))

            self._should_try_again = True
            return True

        def _write_unmapped(uc, access, address, size, value, self):
            print "unmapped ({}, {}, {:x}, {}, {}, {})\n\n\n".format(repr(uc), repr(access), (address), repr(size), repr(value), repr(self))
            m = self._create_emulated_mapping(uc, address, size)
            self._written.append((address, size*8, value))
            self._should_try_again = True
            return True

        def _invalid_write(uc, access, address, size, value, self):
            print "invalid write"
            self._should_try_again = False
            return False


        def _interrupt(uc, number, self):
            from ..core.cpu.abstractcpu import Interruption
            self._to_raise = Interruption(number)
            return True

        def _generic_hook(*args):
            print "generic hook: ", args
            return True

        self._emu.hook_add(UC_HOOK_MEM_UNMAPPED,       _read_unmapped, self)
        self._emu.hook_add(UC_HOOK_MEM_WRITE,          _xfer_mem, self)
        self._emu.hook_add(UC_HOOK_MEM_WRITE_UNMAPPED, _write_unmapped, self)
        self._emu.hook_add(UC_HOOK_MEM_READ,           _xfer_mem, self)
        self._emu.hook_add(UC_HOOK_INTR,               _interrupt, self)

        ctx = self._emu.context_save()

        while True:
            try:
                self._should_try_again = False
                self._emu.emu_start(self._cpu.PC, self._cpu.PC+instruction.size, count=1)
                if not self._should_try_again:
                    break
                self._emu.emu_stop()
                self._emu.context_restore(ctx)

            except UcError as e:
                if e.errno == UC_ERR_WRITE_UNMAPPED:
                    raise MemoryException(repr(e), 0)
                else:
                    "got error: ", e

        #sys.exit(0)

        if logger.getEffectiveLevel() == logging.DEBUG:
            logger.debug("="*10)
            for register in self._cpu.canonical_registers:
                logger.debug("Register % 3s  Manticore: %08x, Unicorn %08x", register, self._cpu.read_register(register), self._emu.reg_read(_reg_id(register)) )
            logger.debug(">"*10)

        

        # Bring back Unicorn registers to Manticore
        for reg in registers:
            val = self._emu.reg_read(_reg_id(reg))
            self._cpu.write_register(reg, val)
        

        #Unicorn hack. On single step unicorn wont advance the PC register
        mu_pc = self.get_unicorn_pc()
        if PC == mu_pc:
            #PC should have been updated by emulator :(
            self._cpu.PC = self._cpu.PC+instruction.size
        #else:
            #print 'not bumping {:x} {:x}'.format(mu_pc, PC)
            #self._cpu.PC = mu_pc

        if self._to_raise:
            raise self._to_raise

        return


## Tucked away here for later debugging  help
##        if PC == 0x4008b0:
##            def _generic_hook(*args):
##                print "generic: ", args
##                return True
##            self._emu.hook_add(UC_HOOK_INTR,               _generic_hook, 0)
##            self._emu.hook_add(UC_HOOK_INSN,               _generic_hook, 1)
##            self._emu.hook_add(UC_HOOK_INSN,               _generic_hook, 1)
##            self._emu.hook_add(UC_HOOK_CODE,               _generic_hook, 2)
##            self._emu.hook_add(UC_HOOK_BLOCK,              _generic_hook, 3)
##            self._emu.hook_add(UC_HOOK_MEM_READ_UNMAPPED,  _generic_hook, 4)
##            self._emu.hook_add(UC_HOOK_MEM_WRITE_UNMAPPED, _generic_hook, 5)
##            self._emu.hook_add(UC_HOOK_MEM_READ_PROT,      _generic_hook, 7)
##            self._emu.hook_add(UC_HOOK_MEM_WRITE_PROT,     _generic_hook, 8)
##            self._emu.hook_add(UC_HOOK_MEM_FETCH_PROT,     _generic_hook, 9)
##            self._emu.hook_add(UC_HOOK_MEM_WRITE,          _generic_hook, 11)
##            self._emu.hook_add(UC_HOOK_MEM_FETCH,          _generic_hook, 12)
##            self._emu.hook_add(UC_HOOK_MEM_READ_AFTER,     _generic_hook, 13)
##            self._emu.hook_add(UC_HOOK_MEM_UNMAPPED,       _generic_hook, 14)
##            self._emu.hook_add(UC_HOOK_MEM_PROT,           _generic_hook, 15)
##            self._emu.hook_add(UC_HOOK_MEM_READ_INVALID,   _generic_hook, 16)
##            self._emu.hook_add(UC_HOOK_MEM_WRITE_INVALID,  _generic_hook, 17)
##            self._emu.hook_add(UC_HOOK_MEM_FETCH_INVALID,  _generic_hook, 18)
##            self._emu.hook_add(UC_HOOK_MEM_INVALID,        _generic_hook, 19)
##            self._emu.hook_add(UC_HOOK_MEM_VALID,          _generic_hook, 20)
##            
