
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
        self._read = []
        self._undo_list = []
        self._written = []
        self._mapped = []

    def _unicorn(self):
        if self._cpu.arch == CS_ARCH_ARM:
            return Uc(UC_ARCH_ARM, UC_MODE_ARM)
        elif self._cpu.arch == CS_ARCH_X86:
            if self._cpu.mode == CS_MODE_32:
                return Uc(UC_ARCH_X86, UC_MODE_32)
            elif self._cpu.mode == CS_MODE_64:
                return Uc(UC_ARCH_X86, UC_MODE_64)
        
        raise RuntimeError("Unsupported architecture")

    def _mem_used(self, instruction):
        used = set()
        # operands of the instruction. 
        for op in instruction.operands:
            if op.type not in (ARM_OP_MEM, X86_OP_MEM):
                continue
            self._cpu.PC += instruction.size
            #FIXME maybe add a kwarg parameter to operand.address() with the current pc?
            addr = op.address()
            self._cpu.PC -= instruction.size
            #address can not be symbolis as all registers in the operands where concretized before. Right?
            assert not issymbolic(addr)
            if self._cpu.arch == CS_ARCH_ARM:  #FIXME normalize insterface
                num_bytes = op.size()
            else:
                num_bytes = op.size/8
            used.update(range(addr, addr + num_bytes))
        # Request the bytes of the instruction.
        used.update(range(self._cpu.PC, self._cpu.PC + instruction.size))
        return used


    def _regs_used(self, instruction):
        if False and hasattr(instruction, 'regs_access') and instruction.regs_access is not None:
            (regs_read, regs_write) = instruction.regs_access()
            regs = [ instruction.reg_name(r).upper() for r in regs_write ] 
            if self._cpu.arch == CS_ARCH_X86:
                if self._cpu.mode == CS_MODE_64:
                    #fix buggy capstone regs for amd64
                    pass
                else:
                    #fix buggy capstone regs for i386
                    pass

            elif self._cpu.arch == CS_ARCH_ARM: 
                #fix buggy capstone regs for arm
                pass
        else:
            regs = self._cpu.canonical_registers
        return regs

    def _regs_modif(self, instruction):
        if False and hasattr(instruction, 'regs_access') and instruction.regs_access is not None:
            (regs_read, regs_write) = instruction.regs_access()
            regs = [ instruction.reg_name(r).upper() for r in regs_write ] 
            if self._cpu.arch == CS_ARCH_X86:
                if self._cpu.mode == CS_MODE_64:
                    #fix buggy capstone regs for amd64
                    pass
                else:
                    #fix buggy capstone regs for i386
                    pass
            elif self._cpu.arch == CS_ARCH_ARM: 
                #fix buggy capstone regs for arm 
                pass
        else:
            regs = self._cpu.canonical_registers
        return regs

    def emulate(self, instruction):
        def _reg_id(reg_name):
            #FIXME FIXME FIXME
            #assert unicorn.__version__ <= '1.0.0', "If we are using unicorn greater than 1.0.0 we have ARM.APSR support
            #if unicorn.__version__ <= '1.0.0' and reg_name == 'APSR':
                #reg_name = 'CPSR'
            stem = {CS_ARCH_ARM: 'UC_ARM_REG_', CS_ARCH_X86: 'UC_X86_REG_'}[self._cpu.arch]
            return globals()[stem+reg_name]
        #Fix Taint propagation
        pages = set() #list of page addresses we need to pass tothe emulator


        #registers = {}
        #memory = {}

        '''
        for reg in self._cpu._regs_used(instruction):
            value = self._cpu.read_register(reg)
            if issymbolic(value):
                #this will restart the emulation with a concrete register reg
                raise ConcretizeRegister(reg, "Prepare register for concrete emulator") 
            registers[reg] = value

        # Concretizes the bytes of memory potentially needed by the instruction.
        for addr in self._cpu._mem_used(instruction):
            pages.add(addr & (~0xFFF))
            if self._cpu.memory.access_ok(addr, 'r'):
                val = self._cpu.read_int(addr, 8)
                if issymbolic(val):
                    raise ConcretizeMemory(addr, 8, "Prepare memory for concrete emulation", 'SAMPLED')
                memory[addr] = val

        '''
        #The emulator
        mu = self._unicorn()

        # touched = set()

        ### def hook_mem_access(uc, access, address, size, value, user_data):
        ###     ''' Auxiliar hook to process unicorn memory accesses.
        ###             Reads must be initialized.
        ###             Writes must by updated to manticore SE.
        ###      ''' 
        ###     if access & UC_MEM_WRITE:
        ###         for i in range(address, address+size):
        ###             user_data.add(i)
        ###     if access & UC_MEM_READ:
        ###         for i in range(address, address+size):
        ###             if i not in memory.keys():
        ###                 logger.error("Emulator is using not initalized memory at %x", address)
        try:
            # Copy in the concrete values of all needed registers.
            #for register, value in registers.items():
            #    print "writing: "
            #    mu.reg_write(_reg_id(register), value)
            for reg in self._cpu.canonical_registers:
                val = self._cpu.read_register(reg)
                if issymbolic(val):
                    raise ConcretizeRegister(reg, "Prepare register for concrete emulator") 
                mu.reg_write(_reg_id(reg), val)
                #print "Written {} to {:x}".format(reg, val)


            #Map needed pages
            ## for page in pages:
            ##     pages.add(page)
            ##     #FIXME We should replicate same permissions in the emulator
            ##     mu.mem_map(page, 0x1000, UC_PROT_ALL)

            ## # Copy in memory bytes needed by instruction.
            ## for addr, value in memory.items():
            ##     mu.mem_write(addr, Operators.CHR(value))


            ## if logger.getEffectiveLevel() == logging.DEBUG:
            ##     logger.debug("="*10)
            ##     for register in self._cpu.canonical_registers:
            ##         logger.debug("Register % 3s  Manticore: %08x, Unicorn %08x", register, self._cpu.read_register(register), mu.reg_read(_reg_id(register)) )

            def _create_emulated_mapping(uc, address, size=None):
                m = self._cpu.memory.map_containing(address)
                print "m is ", m
                if m.start in self._mapped:
                    return m
                permissions = UC_PROT_NONE
                if 'r' in m.perms: permissions |= UC_PROT_READ
                if 'w' in m.perms: permissions |= UC_PROT_WRITE
                if 'x' in m.perms: permissions |= UC_PROT_EXEC
                print "Mapping: ", (m.start, len(m), permissions)
                uc.mem_map(m.start, len(m), permissions)
                self._mapped.append(m.start)
                return m

            #Unicorn hack. On single step unicorn wont advance the PC register
            PC = self._cpu.PC

            m = _create_emulated_mapping(mu, self._cpu.PC, instruction.size)
            mu.mem_write(PC, ''.join(m[PC:PC+instruction.size]))
            
            actions = []

            # Run the instruction.
            #hook_id = mu.hook_add(UC_HOOK_MEM_WRITE | UC_HOOK_MEM_READ, hook_mem_access, touched)
            ##def _step_back(uc):
            ##    pc = uc.reg_read(_reg_id('PC'))
            ##    uc.reg_write(_reg_id('PC'), pc - instruction.size)
            ##    #raise ReExecute


            def _generic_hook(*args, **kwargs):
                print "_generic_hook, args: {}, kwargs: {}".format(repr(args), repr(kwargs))
                print "   hex: {}".format([hex(x) for x in args if isinstance(x, (int,long))])
                #sys.exit(1)
                return True

            def _xfer_mem(uc, access, address, size, value, self):
                # XXX(yan): record memory writes to our own state and undo them if
                # we have to re-execute
                print "_xfer_mem: access({}) address({:x}) size({}) value({})".format(['write', 'read'][access == UC_MEM_READ], address, size, repr(value))
                #print _create_emulated_mapping(uc, address)

                assert access in (UC_MEM_WRITE, UC_MEM_READ)

                # Make sure the memory we're reading or writing is mapped
                m = _create_emulated_mapping(uc, address, size)

                '''
                #try:
                if access == UC_MEM_WRITE:
                    print "Writing"
                    self._cpu.write_int(address, value, size*8)
                else:
                    #val = self._cpu.read(address, size)
                    actions.append(('read', address, size))
                    print "Reading: Added"
                    self._cpu.should_try_again = True
                    #print "Reading ({:x}: {})".format(address, repr(val))
                    #mu.mem_write(address, ''.join(val))
                    #print "Done"
                    return False
                print "Returning.."
                '''
                return True
                #except Exception as e:
                    #print "FAILED: ",e
                    #return False
                #_step_back(uc)

            def _read_unmapped(uc, access, address, size, value, self):
                '''
                We hit an unmapped region; map it into unicorn
                '''
                print "_read_unmapped (acc:{}, addr:{:x}, sz:{}, val:{})".format(access, address, size, repr(value))

                if not self._cpu.memory.access_ok(slice(address, address+size), 'r'):
                    self._cpu.should_try_again = False
                    return False

                # XXX(yan): handle if this points to an incorrect mapping
                _create_emulated_mapping(uc, address, size)
                bytes = self._cpu.read_bytes(address, size)
                uc.mem_write(address, ''.join(bytes))

                self._cpu.should_try_again = True
                return False

            def _write_unmapped(uc, access, address, size, value, self):
                print "unmapped ({}, {}, {:x}, {}, {}, {})\n\n\n".format(repr(uc), repr(access), (address), repr(size), repr(value), repr(self))
                m = _create_emulated_mapping(uc, address, size)
                self._written.append((address, size*8, value))
                # _step_back(uc)
                # uc.emu_stop()
                self._cpu.should_try_again = True
                return False

            def _read_after(uc, access, address, size, value, self):
                info = (address, size)
                if info not in self._read:
                    print "Adding {} to read events (len: {})".format(info, len(self._read))
                    self._read.append(info)
                    self._cpu.should_try_again = True
                    return False
                else:
                    print "Not adding"
                    return True

            def _invalid_write(uc, access, address, size, value, self):
                print "invalid write"
                self._cpu.should_try_again = False
                return False

            def _about_to_run_code(uc, address, size, self):
                print "!!!! _about_to_run_code: ", args

                #PC = self._cpu.PC
                #m = _create_emulated_mapping(mu, address, size)
                #mu.mem_write(address, ''.join(m[address:address+size]))
                return True



            #mu.hook_add(UC_HOOK_MEM_FETCH_UNMAPPED, _read_unmapped, self)
            mu.hook_add(UC_HOOK_MEM_UNMAPPED,       _read_unmapped, self)
            mu.hook_add(UC_HOOK_MEM_WRITE,          _xfer_mem, self)
            mu.hook_add(UC_HOOK_MEM_WRITE_UNMAPPED, _write_unmapped, self)
            #mu.hook_add(UC_HOOK_MEM_READ_UNMAPPED,  _read_unmapped, self)
            #mu.hook_add(UC_HOOK_MEM_INVALID,        _invalid_write, self)
            # mu.hook_add(UC_HOOK_CODE,               _about_to_run_code, self)
            #mu.hook_add(UC_HOOK_MEM_READ,           _xfer_mem, self)
            mu.hook_add(UC_HOOK_MEM_READ_AFTER,     _read_after, self)

            #mu.hook_add(UC_HOOK_INTR,               _generic_hook, 0)
            #mu.hook_add(UC_HOOK_INSN,               _generic_hook, 1)
            #mu.hook_add(UC_HOOK_CODE,               _generic_hook, 2)
            #mu.hook_add(UC_HOOK_BLOCK,              _generic_hook, 3)
            ## mu.hook_add(UC_HOOK_MEM_READ_UNMAPPED,  _generic_hook, 4)
            ## mu.hook_add(UC_HOOK_MEM_WRITE_UNMAPPED, _generic_hook, 5)
            ## mu.hook_add(UC_HOOK_MEM_READ_PROT,      _generic_hook, 7)
            ## mu.hook_add(UC_HOOK_MEM_WRITE_PROT,     _generic_hook, 8)
            ## mu.hook_add(UC_HOOK_MEM_FETCH_PROT,     _generic_hook, 9)
            ## mu.hook_add(UC_HOOK_MEM_WRITE,          _generic_hook, 11)
            ## mu.hook_add(UC_HOOK_MEM_FETCH,          _generic_hook, 12)
            ## mu.hook_add(UC_HOOK_MEM_READ_AFTER,     _generic_hook, 13)
            #mu.hook_add(UC_HOOK_MEM_UNMAPPED,       _generic_hook, 14)
            ## mu.hook_add(UC_HOOK_MEM_PROT,           _generic_hook, 15)
            ## mu.hook_add(UC_HOOK_MEM_READ_INVALID,   _generic_hook, 16)
            ## mu.hook_add(UC_HOOK_MEM_WRITE_INVALID,  _generic_hook, 17)
            ## mu.hook_add(UC_HOOK_MEM_FETCH_INVALID,  _generic_hook, 18)
            ## mu.hook_add(UC_HOOK_MEM_INVALID,        _generic_hook, 19)
            ## mu.hook_add(UC_HOOK_MEM_VALID,          _generic_hook, 20)

            ctx = mu.context_save()

            while True:
                try:
                    self._cpu.should_try_again = False
                    mu.emu_start(self._cpu.PC, self._cpu.PC+instruction.size, count=1)
                    if not self._cpu.should_try_again:
                        break
                    mu.emu_stop()
                    #print "after stop"
                    

                    for read_action in self._read:
                        address, size = read_action
                        mcore_mem = self._cpu.read_bytes(address, size)

                        assert not any(map(issymbolic, mcore_mem))

                        mu.mem_write(address, ''.join(mcore_mem))

                    #while actions:
                    #    action = actions.pop()
                    #    #print 'Action:', action
                    #    if action[0] == 'read':
                    #        #print "Reading: ", action
                    #        val = self._cpu.read(action[1], action[2])
                    #        #actions.append(('read', address, size))
                    #        #print "Reading ({:x}: {})".format(address, repr(val))
                    #        mu.mem_write(action[1], ''.join(val))
                    mu.context_restore(ctx)
                    #print "after restore"

                except UcError as e:
                    #print "Exception: ", e
                    if e.errno == UC_ERR_WRITE_UNMAPPED:
                        raise MemoryException(repr(e), 0)
                #except Exception as e:
                    #print "Raised: ", e

                    #print "!!!!", e, e.errno, UC_ERR_WRITE_UNMAPPED
                    #sys.exit(1)
                #finally:
                    #print "Finally"
            #mu.hook_del(hook_id)
            # mu.emu_stop()

            while self._written:
                address, size, value = self._written.pop()
                
                # Read previous value
                #previous_value = self._cpu.read_int(address, value, size)
                #self._undo_list.append((address, size, previous_value))

                #assert size == self._cpu.address_bit_size
                self._cpu.write_int(address, value, size)

            print "Done."
            #sys.exit(0)

            if logger.getEffectiveLevel() == logging.DEBUG:
                logger.debug("="*10)
                for register in self._cpu.canonical_registers:
                    logger.debug("Register % 3s  Manticore: %08x, Unicorn %08x", register, self._cpu.read_register(register), mu.reg_read(_reg_id(register)) )
                logger.debug(">"*10)


            # Copy back the memory modified by the unicorn emulation.
            #for addr in touched:
            #    try:
            #        self._cpu.write_int(addr, ord(mu.mem_read(addr, 1)), 8)
            #    except MemoryException as e:
            #        pass

            # Copy back the new values of all registers.
            #for register in self._cpu._regs_modif(instruction):
            #    new_value = mu.reg_read(_reg_id(register))
            #    self._cpu.write_register(register, new_value)
            

            for reg in self._cpu.canonical_registers:
                val = mu.reg_read(_reg_id(reg))
                #if issymbolic(val):
                    #raise ConcretizeRegister(reg, "Prepare register for concrete emulator") 
                self._cpu.write_register(reg, val)
                #mu.reg_write(_reg_id(reg), val)
                #print "Written {} to {:x}".format(reg, val)
            

            #Unicorn hack. On single step unicorn wont advance the PC register
            mu_pc = mu.reg_read(_reg_id('R15'))
            
            if PC == mu_pc:
                #PC should have been updated by emulator :(
                self._cpu.PC = self._cpu.PC+instruction.size
                print "bumping"
            else:
                print 'not bumping {:x} {:x}'.format(mu_pc, PC)
                #self._cpu.PC = mu_pc

            return

        except Exception as e:
            logger.error('Exception in emulating code:')
            logger.error(e, exc_info=True)
        finally:
            for i in pages:
                mu.mem_unmap(i, 0x1000)
