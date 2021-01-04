import logging
import time

from capstone import *

######################################################################
# Abstract classes for capstone/unicorn based cpus
# no emulator by default
from unicorn import *
from unicorn.arm_const import *
from unicorn.x86_const import *

from ..core.smtlib import Operators, SelectedSolver, issymbolic
from ..native.memory import MemoryException

logger = logging.getLogger(__name__)


def convert_permissions(m_perms):
    """
    Converts a Manticore permission string into a Unicorn permission
    :param m_perms: Manticore perm string ('rwx')
    :return: Unicorn Permissions
    """
    permissions = UC_PROT_NONE
    if "r" in m_perms:
        permissions |= UC_PROT_READ
    if "w" in m_perms:
        permissions |= UC_PROT_WRITE
    if "x" in m_perms:
        permissions |= UC_PROT_EXEC
    return permissions


def hr_size(num, suffix="B") -> str:
    """
    Human-readable data size
    From https://stackoverflow.com/a/1094933
    :param num: number of bytes
    :param suffix: Optional size specifier
    :return: Formatted string
    """
    for unit in " KMGTPEZ":
        if abs(num) < 1024.0:
            return "%3.1f%s%s" % (num, unit if unit != " " else "", suffix)
        num /= 1024.0
    return "%.1f%s%s" % (num, "Y", suffix)


class ConcreteUnicornEmulator:
    """
    Helper class to emulate instructions in bulk via Unicorn.
    ---
    The regular Unicorn Emulator is used as a fallback for emulating single instructions that don't have their own
    implementations in Manticore. This Emulator is instead intended to completely replace Manticore's executor when
    operating on purely concrete data.

    To use the emulator, register a callback for the will_run event that calls `state.cpu.emulate_until` with an
    address at which it should switch back from Unicorn to Manticore. Passing 0 will result in the entire target being
    executed concretely.

    As a result of the concrete data requirement, this emulator is good for preloading concrete state, but typically
    should not be used once symbolic data is introduced. At time of writing, if you try emulate under Unicorn up until
    the point where symbolic data is introduced, switch to Manticore, fork states, then switch back, it *definitely*
    won't work.

    Only supports X86_64 for now.
    """

    def __init__(self, cpu):
        self._cpu = cpu
        self._mem_delta = {}
        self.flag_registers = {"CF", "PF", "AF", "ZF", "SF", "IF", "DF", "OF"}
        self.write_backs_disabled = False
        self._stop_at = None

        cpu.subscribe("did_write_memory", self.write_back_memory)
        cpu.subscribe("did_write_register", self.write_back_register)
        cpu.subscribe("did_set_descriptor", self.update_segment)
        cpu.subscribe("did_map_memory", self.map_memory_callback)
        cpu.subscribe("did_unmap_memory", self.unmap_memory_callback)
        cpu.subscribe("did_protect_memory", self.protect_memory_callback)

        if self._cpu.arch == CS_ARCH_X86:
            self._uc_arch = UC_ARCH_X86
            self._uc_mode = {CS_MODE_32: UC_MODE_32, CS_MODE_64: UC_MODE_64}[self._cpu.mode]
        else:
            raise NotImplementedError(f"Unsupported architecture: {self._cpu.arch}")

        self.reset()

        self._emu.hook_add(UC_HOOK_MEM_READ_UNMAPPED, self._hook_unmapped)
        self._emu.hook_add(UC_HOOK_MEM_WRITE_UNMAPPED, self._hook_unmapped)
        self._emu.hook_add(UC_HOOK_MEM_FETCH_UNMAPPED, self._hook_unmapped)
        self._emu.hook_add(UC_HOOK_MEM_WRITE, self._hook_write_mem)
        self._emu.hook_add(UC_HOOK_INTR, self._interrupt)
        self._emu.hook_add(UC_HOOK_INSN, self._hook_syscall, arg1=UC_X86_INS_SYSCALL)

        self.registers = set(self._cpu.canonical_registers)
        # The last 8 canonical registers of x86 are individual flags; replace with the eflags
        self.registers -= self.flag_registers
        # TODO(eric_k): unicorn@1.0.2rc1 doesn't like writing to
        # the FS register, and it will segfault or hang.
        self.registers -= {"FS"}
        self.registers.add("EFLAGS")

        for reg in self.registers:
            val = self._cpu.read_register(reg)

            if reg in {"FS", "GS"}:
                self.msr_write(reg, val)
                continue

            if issymbolic(val):
                from ..native.cpu.abstractcpu import ConcretizeRegister

                raise ConcretizeRegister(
                    self._cpu, reg, "Concretizing for emulation.", policy="ONE"
                )
            logger.debug("Writing %s into %s", val, reg)
            self._emu.reg_write(self._to_unicorn_id(reg), val)

        for m in cpu.memory.maps:
            self.map_memory_callback(m.start, len(m), m.perms, m.name, 0, m.start)

    def reset(self):
        self._emu = Uc(self._uc_arch, self._uc_mode)
        self._to_raise = None

    def copy_memory(self, address, size):
        """
        Copy the bytes from address to address+size into Unicorn
        Used primarily for copying memory maps
        :param address: start of buffer to copy
        :param size: How many bytes to copy
        """
        start_time = time.time()
        map_bytes = self._cpu._raw_read(address, size)
        self._emu.mem_write(address, map_bytes)
        if time.time() - start_time > 3:
            logger.info(
                f"Copying {hr_size(size)} map at {hex(address)} took {time.time() - start_time} seconds"
            )

    def map_memory_callback(self, address, size, perms, name, offset, result):
        """
        Catches did_map_memory and copies the mapping into Manticore
        """
        logger.info(
            " ".join(
                (
                    "Mapping Memory @",
                    hex(address) if type(address) is int else "0x??",
                    hr_size(size),
                    "-",
                    perms,
                    "-",
                    f"{name}:{hex(offset) if name else ''}",
                    "->",
                    hex(result),
                )
            )
        )
        self._emu.mem_map(address, size, convert_permissions(perms))
        self.copy_memory(address, size)

    def unmap_memory_callback(self, start, size):
        """Unmap Unicorn maps when Manticore unmaps them"""
        logger.info(f"Unmapping memory from {hex(start)} to {hex(start + size)}")

        mask = (1 << 12) - 1
        if (start & mask) != 0:
            logger.error("Memory to be unmapped is not aligned to a page")

        if (size & mask) != 0:
            size = ((size >> 12) + 1) << 12
            logger.warning("Forcing unmap size to align to a page")

        self._emu.mem_unmap(start, size)

    def protect_memory_callback(self, start, size, perms):
        """ Set memory protections in Unicorn correctly """
        logger.info(f"Changing permissions on {hex(start)}:{hex(start + size)} to {perms}")
        self._emu.mem_protect(start, size, convert_permissions(perms))

    def get_unicorn_pc(self):
        """Get the program counter from Unicorn regardless of architecture.
        Legacy method, since this module only works on x86."""
        if self._cpu.arch == CS_ARCH_ARM:
            return self._emu.reg_read(UC_ARM_REG_R15)
        elif self._cpu.arch == CS_ARCH_X86:
            if self._cpu.mode == CS_MODE_32:
                return self._emu.reg_read(UC_X86_REG_EIP)
            elif self._cpu.mode == CS_MODE_64:
                return self._emu.reg_read(UC_X86_REG_RIP)

    def _hook_syscall(self, uc, data):
        """
        Unicorn hook that transfers control to Manticore so it can execute the syscall
        """
        logger.debug(
            f"Stopping emulation at {hex(uc.reg_read(self._to_unicorn_id('RIP')))} to perform syscall"
        )
        self.sync_unicorn_to_manticore()
        from ..native.cpu.abstractcpu import Syscall

        self._to_raise = Syscall()
        uc.emu_stop()

    def _hook_write_mem(self, uc, access, address, size, value, data):
        """
        Captures memory written by Unicorn
        """
        self._mem_delta[address] = (value, size)
        return True

    def _hook_unmapped(self, uc, access, address, size, value, data):
        """
        We hit an unmapped region; map it into unicorn.
        """
        try:
            self.sync_unicorn_to_manticore()
            logger.warning(f"Encountered an operation on unmapped memory at {hex(address)}")
            m = self._cpu.memory.map_containing(address)
            self.copy_memory(m.start, m.end - m.start)
        except MemoryException as e:
            logger.error(
                "Failed to map memory {}-{}, ({}): {}".format(
                    hex(address), hex(address + size), access, e
                )
            )
            self._to_raise = e
            self._should_try_again = False
            return False

        self._should_try_again = True
        return False

    def _interrupt(self, uc, number, data):
        """
        Handle software interrupt (SVC/INT)
        """
        logger.info("Caught interrupt: %s" % number)
        from ..native.cpu.abstractcpu import Interruption  # prevent circular imports

        self._to_raise = Interruption(number)
        return True

    def _to_unicorn_id(self, reg_name):
        if self._cpu.arch == CS_ARCH_ARM:
            return globals()["UC_ARM_REG_" + reg_name]
        elif self._cpu.arch == CS_ARCH_X86:
            # TODO(yan): This needs to handle AF register
            custom_mapping = {"PC": "RIP", "STACK": "RSP", "FRAME": "RBP"}
            try:
                return globals()["UC_X86_REG_" + custom_mapping.get(reg_name, reg_name)]
            except KeyError:
                logger.error("Can't find register UC_X86_REG_%s", str(reg_name))
                raise

        else:
            # TODO(yan): raise a more appropriate exception
            raise TypeError

    def emulate(self, instruction):
        """
        Wrapper that runs the _step function in a loop while handling exceptions
        """

        # The emulation might restart if Unicorn needs to bring in a memory map
        # or bring a value from Manticore state.
        while True:

            # Try emulation
            self._should_try_again = False
            self._to_raise = None

            self._step(instruction)

            if not self._should_try_again:
                break

    def _step(self, instruction, chunksize=0):
        """
        Execute a chunk fo instructions starting from instruction
        :param instruction: Where to start
        :param chunksize: max number of instructions to execute. Defaults to infinite.
        """

        try:
            pc = self._cpu.PC
            m = self._cpu.memory.map_containing(pc)
            if self._stop_at:
                logger.info(f"Emulating from {hex(pc)} to  {hex(self._stop_at)}")
            self._emu.emu_start(pc, m.end if not self._stop_at else self._stop_at, count=chunksize)
        except UcError:
            # We request re-execution by signaling error; if we we didn't set
            # _should_try_again, it was likely an actual error
            if not self._should_try_again:
                raise

        if self._should_try_again:
            return

        # self.sync_unicorn_to_manticore()
        self._cpu.PC = self.get_unicorn_pc()
        if self._cpu.PC == self._stop_at:
            logger.info("Reached emulation target, switching to Manticore mode")
            self.sync_unicorn_to_manticore()
            self._stop_at = None

        # Raise the exception from a hook that Unicorn would have eaten
        if self._to_raise:
            from ..native.cpu.abstractcpu import Syscall

            if type(self._to_raise) is not Syscall:
                logger.info("Raising %s", self._to_raise)
            raise self._to_raise

        logger.info(f"Exiting Unicorn Mode at {hex(self._cpu.PC)}")
        return

    def sync_unicorn_to_manticore(self):
        """
        Copy registers and written memory back into Manticore
        """
        self.write_backs_disabled = True
        for reg in self.registers:
            val = self._emu.reg_read(self._to_unicorn_id(reg))
            self._cpu.write_register(reg, val)
        if len(self._mem_delta) > 0:
            logger.debug(f"Syncing {len(self._mem_delta)} writes back into Manticore")
        for location in self._mem_delta:
            value, size = self._mem_delta[location]
            self._cpu.write_int(location, value, size * 8)
        self.write_backs_disabled = False
        self._mem_delta = {}

    def write_back_memory(self, where, expr, size):
        """ Copy memory writes from Manticore back into Unicorn in real-time """
        if self.write_backs_disabled:
            return
        if type(expr) is bytes:
            self._emu.mem_write(where, expr)
        else:
            if issymbolic(expr):
                data = [
                    Operators.CHR(Operators.EXTRACT(expr, offset, 8))
                    for offset in range(0, size, 8)
                ]
                concrete_data = []
                for c in data:
                    if issymbolic(c):
                        c = chr(
                            SelectedSolver.instance().get_value(self._cpu.memory.constraints, c)
                        )
                    concrete_data.append(c)
                data = concrete_data
            else:
                data = [
                    Operators.CHR(Operators.EXTRACT(expr, offset, 8))
                    for offset in range(0, size, 8)
                ]
            logger.debug(f"Writing back {hr_size(size // 8)} to {hex(where)}: {data}")
            # TODO - the extra encoding is to handle null bytes output as strings when we concretize. That's probably a bug.
            self._emu.mem_write(
                where, b"".join(b.encode("utf-8") if type(b) is str else b for b in data)
            )

    def write_back_register(self, reg, val):
        """ Sync register state from Manticore -> Unicorn"""
        if self.write_backs_disabled:
            return
        if issymbolic(val):
            logger.warning("Skipping Symbolic write-back")
            return
        if reg in self.flag_registers:
            self._emu.reg_write(self._to_unicorn_id("EFLAGS"), self._cpu.read_register("EFLAGS"))
            return
        # TODO(eric_k): unicorn@1.0.2rc1 doesn't like writing to
        # the FS register, and it will segfault or hang.
        if reg in {"FS"}:
            logger.warning(f"Skipping {reg} write. Unicorn unsupported register write.")
            return
        self._emu.reg_write(self._to_unicorn_id(reg), val)

    def update_segment(self, selector, base, size, perms):
        """ Only useful for setting FS right now. """
        logger.info("Updating selector %s to 0x%02x (%s bytes) (%s)", selector, base, size, perms)
        if selector == 99:
            self.msr_write("FS", base)
        else:
            logger.error("No way to write segment: %d", selector)

    def msr_write(self, reg, data):
        """
        set the hidden descriptor-register fields to the given address.
        This enables referencing the fs segment on x86-64.
        """
        magic = {"FS": 0xC0000100, "GS": 0xC0000101}
        return self._emu.msr_write(magic[reg], data)
