import logging

from ..native.memory import MemoryException

from ..core.smtlib import issymbolic

######################################################################
# Abstract classes for capstone/unicorn based cpus
# no emulator by default
from unicorn import *
from unicorn.x86_const import *
from unicorn.arm_const import *
from unicorn.arm64_const import *

from capstone import *

logger = logging.getLogger(__name__)


class EmulatorException(Exception):
    """
    Emulator exception
    """

    pass


class UnicornEmulator:
    """
    Helper class to emulate a single instruction via Unicorn.
    """

    def __init__(self, cpu):
        self._cpu = cpu

        text = cpu.memory.map_containing(cpu.PC)
        # Keep track of all memory mappings. We start with just the text section
        self._should_be_mapped = {text.start: (len(text), UC_PROT_READ | UC_PROT_EXEC)}

        # Keep track of all the memory Unicorn needs while executing this
        # instruction
        self._should_be_written = {}

        if self._cpu.arch == CS_ARCH_ARM:
            self._uc_arch = UC_ARCH_ARM
            self._uc_mode = {CS_MODE_ARM: UC_MODE_ARM, CS_MODE_THUMB: UC_MODE_THUMB}[self._cpu.mode]

        elif self._cpu.arch == CS_ARCH_ARM64:
            self._uc_arch = UC_ARCH_ARM64
            self._uc_mode = UC_MODE_ARM
            if self._cpu.mode != UC_MODE_ARM:
                raise EmulatorException("Aarch64/Arm64 cannot have different uc mode than ARM.")

        elif self._cpu.arch == CS_ARCH_X86:
            self._uc_arch = UC_ARCH_X86
            self._uc_mode = {CS_MODE_32: UC_MODE_32, CS_MODE_64: UC_MODE_64}[self._cpu.mode]

        else:
            raise NotImplementedError(f"Unsupported architecture: {self._cpu.arch}")

    def reset(self):
        self._emu = Uc(self._uc_arch, self._uc_mode)
        self._to_raise = None

    def _create_emulated_mapping(self, uc, address):
        """
        Create a mapping in Unicorn and note that we'll need it if we retry.
        :param uc: The Unicorn instance.
        :param address: The address which is contained by the mapping.
        :rtype Map
        """

        m = self._cpu.memory.map_containing(address)

        permissions = UC_PROT_NONE
        if "r" in m.perms:
            permissions |= UC_PROT_READ
        if "w" in m.perms:
            permissions |= UC_PROT_WRITE
        if "x" in m.perms:
            permissions |= UC_PROT_EXEC

        uc.mem_map(m.start, len(m), permissions)

        self._should_be_mapped[m.start] = (len(m), permissions)

        return m

    def get_unicorn_pc(self):
        if self._cpu.arch == CS_ARCH_ARM:
            return self._emu.reg_read(UC_ARM_REG_R15)
        elif self._cpu.arch == CS_ARCH_ARM64:
            return self._emu.reg_read(UC_ARM64_REG_PC)
        elif self._cpu.arch == CS_ARCH_X86:
            if self._cpu.mode == CS_MODE_32:
                return self._emu.reg_read(UC_X86_REG_EIP)
            elif self._cpu.mode == CS_MODE_64:
                return self._emu.reg_read(UC_X86_REG_RIP)
        else:
            raise EmulatorException(
                f"Getting PC after unicorn emulation for {self._cpu.arch} architecture is not implemented"
            )

    def _hook_xfer_mem(self, uc, access, address, size, value, data):
        """
        Handle memory operations from unicorn.
        """
        assert access in (UC_MEM_WRITE, UC_MEM_READ, UC_MEM_FETCH)

        if access == UC_MEM_WRITE:
            self._cpu.write_int(address, value, size * 8)

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
        """
        We hit an unmapped region; map it into unicorn.
        """

        try:
            m = self._create_emulated_mapping(uc, address)
        except MemoryException as e:
            self._to_raise = e
            self._should_try_again = False
            return False

        self._should_try_again = True
        return False

    def _interrupt(self, uc, number, data):
        """
        Handle software interrupt (SVC/INT)
        """

        from ..native.cpu.abstractcpu import Interruption  # prevent circular imports

        self._to_raise = Interruption(number)
        return True

    def _to_unicorn_id(self, reg_name):
        if self._cpu.arch == CS_ARCH_ARM:
            return globals()["UC_ARM_REG_" + reg_name]
        elif self._cpu.arch == CS_ARCH_ARM64:
            return globals()["UC_ARM64_REG_" + reg_name]
        elif self._cpu.arch == CS_ARCH_X86:
            # TODO(yan): This needs to handle AF register
            return globals()["UC_X86_REG_" + reg_name]
        else:
            # TODO(yan): raise a more appropriate exception
            raise TypeError(f"Cannot convert {reg_name} to unicorn register id")

    def emulate(self, instruction, reset=True):
        """
        Emulate a single instruction.
        """

        # The emulation might restart if Unicorn needs to bring in a memory map
        # or bring a value from Manticore state.
        while True:
            # XXX: Unicorn doesn't allow to write to and read from system
            # registers directly (see 'arm64_reg_write' and 'arm64_reg_read').
            # The only way to propagate this information is via the MSR
            # (register) and MRS instructions, without resetting the emulator
            # state in between.
            # Note: in HEAD, this is fixed for some system registers, so revise
            # this after upgrading from 1.0.1.
            if reset:
                self.reset()

                # Establish Manticore state, potentially from past emulation
                # attempts
                for base in self._should_be_mapped:
                    size, perms = self._should_be_mapped[base]
                    self._emu.mem_map(base, size, perms)

            for address, values in self._should_be_written.items():
                for offset, byte in enumerate(values, start=address):
                    if issymbolic(byte):
                        from ..native.cpu.abstractcpu import ConcretizeMemory

                        raise ConcretizeMemory(
                            self._cpu.memory, offset, 8, "Concretizing for emulation"
                        )

                self._emu.mem_write(address, b"".join(values))

            # Try emulation
            self._should_try_again = False

            self._step(instruction)

            if not self._should_try_again:
                break

    def _step(self, instruction):
        """
        A single attempt at executing an instruction.
        """
        logger.debug(
            "0x%x:\t%s\t%s" % (instruction.address, instruction.mnemonic, instruction.op_str)
        )

        registers = set(self._cpu.canonical_registers)

        # Refer to EFLAGS instead of individual flags for x86
        if self._cpu.arch == CS_ARCH_X86:
            # The last 8 canonical registers of x86 are individual flags; replace
            # with the eflags
            registers -= set(["CF", "PF", "AF", "ZF", "SF", "IF", "DF", "OF"])
            registers.add("EFLAGS")

            # TODO(eric_k): unicorn@1.0.2rc1 doesn't like writing to
            # the FS register, and it will segfault or hang.
            registers -= {"FS"}

        # XXX(yan): This concretizes the entire register state. This is overly
        # aggressive. Once capstone adds consistent support for accessing
        # referred registers, make this only concretize those registers being
        # read from.
        for reg in registers:
            val = self._cpu.read_register(reg)
            if issymbolic(val):
                from ..native.cpu.abstractcpu import ConcretizeRegister

                raise ConcretizeRegister(
                    self._cpu, reg, "Concretizing for emulation.", policy="ONE"
                )
            self._emu.reg_write(self._to_unicorn_id(reg), val)

        # Bring in the instruction itself
        instruction = self._cpu.decode_instruction(self._cpu.PC)
        text_bytes = self._cpu.read_bytes(self._cpu.PC, instruction.size)
        self._emu.mem_write(self._cpu.PC, b"".join(text_bytes))

        self._emu.hook_add(UC_HOOK_MEM_READ_UNMAPPED, self._hook_unmapped)
        self._emu.hook_add(UC_HOOK_MEM_WRITE_UNMAPPED, self._hook_unmapped)
        self._emu.hook_add(UC_HOOK_MEM_FETCH_UNMAPPED, self._hook_unmapped)
        self._emu.hook_add(UC_HOOK_MEM_READ, self._hook_xfer_mem)
        self._emu.hook_add(UC_HOOK_MEM_WRITE, self._hook_xfer_mem)
        self._emu.hook_add(UC_HOOK_INTR, self._interrupt)

        saved_PC = self._cpu.PC

        try:
            pc = self._cpu.PC
            if self._cpu.arch == CS_ARCH_ARM and self._uc_mode == UC_MODE_THUMB:
                pc |= 1
            # XXX: 'timeout' is needed to avoid hanging:
            # https://github.com/unicorn-engine/unicorn/issues/1061
            # Unfortunately, this may lead to race conditions if the value is
            # too small.  Tests that work fine without 'timeout' start to fail
            # because registers are not being written to.
            self._emu.emu_start(
                pc, self._cpu.PC + instruction.size, count=1, timeout=1000000
            )  # microseconds
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
                logger.debug(
                    f"Register {register:3s}  "
                    f"Manticore: {self._cpu.read_register(register):08x}, "
                    f"Unicorn {self._emu.reg_read(self._to_unicorn_id(register)):08x}"
                )
            logger.debug(">" * 10)

        # Bring back Unicorn registers to Manticore
        for reg in registers:
            val = self._emu.reg_read(self._to_unicorn_id(reg))
            self._cpu.write_register(reg, val)

        # Unicorn hack. On single step, unicorn wont advance the PC register
        mu_pc = self.get_unicorn_pc()
        if saved_PC == mu_pc:
            self._cpu.PC = saved_PC + instruction.size

        else:
            self._cpu.PC = mu_pc

        # Raise the exception from a hook that Unicorn would have eaten
        if self._to_raise:
            raise self._to_raise

        return
