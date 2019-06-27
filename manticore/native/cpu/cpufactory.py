from .aarch64 import Aarch64Cpu, Aarch64CdeclAbi, Aarch64LinuxSyscallAbi
from .arm import Armv7Cpu, Armv7CdeclAbi, Armv7LinuxSyscallAbi
from .x86 import (
    AMD64Cpu,
    I386Cpu,
    AMD64LinuxSyscallAbi,
    I386LinuxSyscallAbi,
    I386CdeclAbi,
    SystemVAbi,
)


class CpuFactory:
    _cpus = {"i386": I386Cpu, "amd64": AMD64Cpu, "armv7": Armv7Cpu, "aarch64": Aarch64Cpu}

    _linux_abis = {
        "i386": I386CdeclAbi,
        "amd64": SystemVAbi,
        "armv7": Armv7CdeclAbi,
        "aarch64": Aarch64CdeclAbi,
    }

    _linux_syscalls_abis = {
        "i386": I386LinuxSyscallAbi,
        "amd64": AMD64LinuxSyscallAbi,
        "armv7": Armv7LinuxSyscallAbi,
        "aarch64": Aarch64LinuxSyscallAbi,
    }

    @staticmethod
    def get_cpu(mem, machine):
        cpu = CpuFactory._cpus[machine](mem)
        mem.cpu = cpu
        return cpu

    @staticmethod
    def get_function_abi(cpu, os, machine):
        if os != "linux" or machine not in CpuFactory._linux_abis:
            raise NotImplementedError(f"OS and machine combination not supported: {os}/{machine}")

        return CpuFactory._linux_abis[machine](cpu)

    @staticmethod
    def get_syscall_abi(cpu, os, machine):
        if os != "linux" or machine not in CpuFactory._linux_syscalls_abis:
            raise NotImplementedError(f"OS and machine combination not supported: {os}/{machine}")

        return CpuFactory._linux_syscalls_abis[machine](cpu)
