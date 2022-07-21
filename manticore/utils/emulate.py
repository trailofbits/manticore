import logging
import time
from typing import Any, Tuple, Dict

from capstone import CS_ARCH_ARM, CS_ARCH_X86, CS_MODE_32, CS_MODE_64

######################################################################
# Abstract classes for capstone/unicorn based cpus
# no emulator by default
from intervaltree import IntervalTree, Interval
from unicorn.unicorn_const import (
    UC_ARCH_X86,
    UC_MODE_64,
    UC_MODE_32,
    UC_PROT_NONE,
    UC_PROT_READ,
    UC_PROT_WRITE,
    UC_PROT_EXEC,
    UC_HOOK_MEM_READ_UNMAPPED,
    UC_HOOK_MEM_WRITE_UNMAPPED,
    UC_HOOK_MEM_FETCH_UNMAPPED,
    UC_HOOK_MEM_WRITE,
    UC_HOOK_INTR,
    UC_HOOK_INSN,
)
from unicorn import Uc, UcError
from unicorn.arm_const import *
from unicorn.x86_const import *

from ..core.smtlib import Operators, SelectedSolver, issymbolic
from ..native.memory import MemoryException

logger = logging.getLogger(__name__)


def convert_permissions(m_perms: str):
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
        # Registers to ignore when translating manticore context to unicorn
        self.ignore_registers = {"MXCSR_MASK"}
        self.write_backs_disabled = False
        self._stop_at = None
        # Holds key of range (addr, addr + size) and value of permissions
        # Key doesn't include permissions because unmap doesn't care about permissions
        self.already_mapped: IntervalTree = IntervalTree()

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
        self._emu.hook_add(UC_HOOK_INSN, self._hook_cpuid, arg1=UC_X86_INS_CPUID)

        self.registers = set(self._cpu.canonical_registers)
        # The last 8 canonical registers of x86 are individual flags; replace with the eflags
        self.registers -= self.flag_registers
        self.registers.add("EFLAGS")

        self.load_state_from_manticore()

    def reset(self):
        self._emu = Uc(self._uc_arch, self._uc_mode)
        self._to_raise = None

    def copy_memory(self, address: int, size: int):
        """
        Copy the bytes from address to address+size into Unicorn
        Used primarily for copying memory maps
        :param address: start of buffer to copy
        :param size: How many bytes to copy
        """
        start_time = time.time()
        map_bytes = self._cpu._raw_read(address, size, force=True)
        self._emu.mem_write(address, map_bytes)
        if time.time() - start_time > 3:
            logger.info(
                f"Copying {hr_size(size)} map at {address:#x} took {time.time() - start_time} seconds"
            )

    def load_state_from_manticore(self) -> None:
        for reg in self.registers:
            # Ignore registers that aren't supported by unicorn
            if reg in self.ignore_registers:
                continue
            val = self._cpu.read_register(reg)
            if issymbolic(val):
                from ..native.cpu.abstractcpu import ConcretizeRegister

                raise ConcretizeRegister(
                    self._cpu, reg, "Concretizing for emulation.", policy="ONE"
                )

            if reg in {"FS", "GS"}:
                if reg == "FS" and val in self._cpu._segments:
                    base, limit, perms = self._cpu._segments[val]
                    self.update_segment(val, base, limit, perms)
                    continue
                logger.debug("Writing {val} into {reg}")
                self.msr_write(reg, val)
                continue

            logger.debug("Writing {val} into {reg}")
            self._emu.reg_write(self._to_unicorn_id(reg), val)

        for m in self._cpu.memory.maps:
            self.map_memory_callback(m.start, len(m), m.perms, m.name, 0, m.start)

    def map_memory_callback(
        self, address: int, size: int, perms: str, name: str, offset: int, result: int
    ) -> None:
        """
        Catches did_map_memory and copies the mapping into Manticore
        """
        begin = address
        end = address + size
        perms_value = convert_permissions(perms)
        # Check for exact match
        # Overlap match
        if (
            Interval(begin, end, perms_value) not in self.already_mapped
            and not self.already_mapped.overlaps(begin, end)
            and not self.already_mapped.envelop(begin, end)
        ):
            logger.info(
                " ".join(
                    (
                        "Mapping Memory @",
                        hex(address),
                        ":",
                        hex(address + size),
                        hr_size(size),
                        "-",
                        perms,
                        "-",
                        f"{name}:{offset:#x}" if name else "",
                        "->",
                        hex(result),
                    )
                )
            )
            self._emu.mem_map(begin, size, perms_value)
            self.already_mapped[begin:end] = perms_value
        logger.debug(
            " ".join(
                (
                    "Copying Memory @",
                    hex(address),
                    hr_size(size),
                    "-",
                    perms,
                    "-",
                    f"{name}:{offset:#x}" if name else "",
                    "->",
                    hex(result),
                )
            )
        )
        self.copy_memory(address, size)
        self.protect_memory_callback(address, size, perms)

    def unmap_memory_callback(self, start, size):
        """Unmap Unicorn maps when Manticore unmaps them"""

        # Need this check because our memory events are leaky to internal implementation details
        end = start + size
        parent_map = self.already_mapped.overlap(start, end)
        # Only unmap whole original maps
        if (
            len(parent_map) == 1
            and list(parent_map)[0].begin == start
            and list(parent_map)[0].end == end
        ):
            mask = (1 << 12) - 1
            if (start & mask) != 0:
                logger.error("Memory to be unmapped is not aligned to a page")

            if (size & mask) != 0:
                size = ((size >> 12) + 1) << 12
                logger.warning("Forcing unmap size to align to a page")

            logger.info(f"Unmapping memory from {start:#x} to {start+size:#x}")

            self._emu.mem_unmap(start, size)
            self.already_mapped.remove_overlap(start, start + size)
        else:
            logger.debug(
                f"Not unmapping because bounds ({start:#x} - {start+size:#x}) are enveloped in existing map:"
            )
            logger.debug(f"\tParent map(s) {parent_map}")

    def protect_memory_callback(self, start, size, perms):
        """Set memory protections in Unicorn correctly"""
        logger.debug(f"Changing permissions on {start:#x}:{start+size:#x} to '{perms}'")
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
            f"Stopping emulation at {uc.reg_read(self._to_unicorn_id('RIP')):#x} to perform syscall"
        )
        self.sync_unicorn_to_manticore()
        from ..native.cpu.abstractcpu import Syscall

        self._to_raise = Syscall()
        uc.emu_stop()

    def _hook_cpuid(self, uc, data):
        """
        Unicorn hook that uses Manticore's semantics for cpuid
        """
        logger.debug(f"Hooking CPUID instruction {uc.reg_read(self._to_unicorn_id('RIP')):#x}")
        if self._cpu.mode == CS_MODE_32:
            pc = uc.reg_read(UC_X86_REG_EIP)
        elif self._cpu.mode == CS_MODE_64:
            pc = uc.reg_read(UC_X86_REG_RIP)
        eax = uc.reg_read(UC_X86_REG_EAX)
        ecx = uc.reg_read(UC_X86_REG_ECX)

        from ..native.cpu.x86 import X86Cpu

        eax, ebx, ecx, edx = X86Cpu.CPUID_helper(pc, eax, ecx)

        uc.reg_write(UC_X86_REG_EAX, eax)
        uc.reg_write(UC_X86_REG_EBX, ebx)
        uc.reg_write(UC_X86_REG_ECX, ecx)
        uc.reg_write(UC_X86_REG_EDX, edx)

        return 1

    def _hook_write_mem(self, uc, _access, address: int, size: int, value: int, _data) -> bool:
        """
        Captures memory written by Unicorn
        """
        self._mem_delta[address] = (value, size)
        return True

    def _hook_unmapped(self, uc, access, address, size, value, _data) -> bool:
        """
        We hit an unmapped region; map it into unicorn.
        """
        try:
            self.sync_unicorn_to_manticore()
            logger.warning(f"Encountered an operation on unmapped memory at {address:#x}")
            m = self._cpu.memory.map_containing(address)
            self.copy_memory(m.start, m.end - m.start)
        except MemoryException as e:
            logger.error(f"Failed to map memory {address:#x}-{address+size:#x}, ({access}): {e}")
            self._to_raise = e
            self._should_try_again = False
            return False

        self._should_try_again = True
        return False

    def _interrupt(self, uc, number: int, _data) -> bool:
        """
        Handle software interrupt (SVC/INT)
        """
        logger.info(f"Caught interrupt: {number}")
        from ..native.cpu.abstractcpu import Interruption  # prevent circular imports

        self._to_raise = Interruption(number)
        return True

    def _to_unicorn_id(self, reg_name: str) -> int:
        if self._cpu.arch == CS_ARCH_ARM:
            return globals()["UC_ARM_REG_" + reg_name]
        elif self._cpu.arch == CS_ARCH_X86:
            # TODO(yan): This needs to handle AF register
            custom_mapping = {"PC": "RIP", "STACK": "RSP", "FRAME": "RBP", "FS_BASE": "FS_BASE"}
            try:
                return globals()["UC_X86_REG_" + custom_mapping.get(reg_name, reg_name)]
            except KeyError:
                logger.error("Can't find register UC_X86_REG_%s", str(reg_name))
                raise

        else:
            # TODO(yan): raise a more appropriate exception
            raise TypeError

    def emulate(self, instruction) -> None:
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

    def _step(self, instruction, chunksize: int = 0) -> None:
        """
        Execute a chunk fo instructions starting from instruction
        :param instruction: Where to start
        :param chunksize: max number of instructions to execute. Defaults to infinite.
        """

        try:
            pc = self._cpu.PC
            m = self._cpu.memory.map_containing(pc)
            if self._stop_at:
                logger.info(f"Emulating from {pc:#x} to  {self._stop_at:#x}")
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
            self.write_backs_disabled = True

        # Raise the exception from a hook that Unicorn would have eaten
        if self._to_raise:
            from ..native.cpu.abstractcpu import Syscall

            if type(self._to_raise) is Syscall:
                # NOTE: raises Syscall within sem_SYSCALL
                # NOTE: Need to call syscall semantic function due to
                # @instruction around SYSCALL
                self._cpu.sem_SYSCALL()
            logger.info(f"Raising {self._to_raise}")
            raise self._to_raise

        logger.info(f"Exiting Unicorn Mode at {self._cpu.PC:#x}")
        return

    def sync_unicorn_to_manticore(self):
        """
        Copy registers and written memory back into Manticore
        """
        self.write_backs_disabled = True
        for reg in self.registers:
            # Ignore registers that aren't supported by unicorn
            if reg in self.ignore_registers:
                continue
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
        """Copy memory writes from Manticore back into Unicorn in real-time"""
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
        """Sync register state from Manticore -> Unicorn"""
        # Ignore registers that aren't supported by unicorn
        if reg in self.ignore_registers:
            return
        if self.write_backs_disabled:
            return
        if issymbolic(val):
            logger.warning("Skipping Symbolic write-back")
            return
        if reg in self.flag_registers:
            self._emu.reg_write(self._to_unicorn_id("EFLAGS"), self._cpu.read_register("EFLAGS"))
            return
        self._emu.reg_write(self._to_unicorn_id(reg), val)

    def update_segment(self, selector, base, size, perms):
        """Only useful for setting FS right now."""
        logger.debug("Updating selector %s to 0x%02x (%s bytes) (%s)", selector, base, size, perms)
        self.write_back_register("FS", selector)
        self.write_back_register("FS_BASE", base)
        self.msr_write("FS", base)

    def msr_write(self, reg, data):
        """
        set the hidden descriptor-register fields to the given address.
        This enables referencing the fs segment on x86-64.

        https://wiki.osdev.org/SWAPGS
        """
        magic = {"FS": 0xC0000100, "GS": 0xC0000101}
        return self._emu.msr_write(magic[reg], data)
