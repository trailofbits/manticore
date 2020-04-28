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
from .abstractcpu import Abi, Cpu, SyscallAbi


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
    def get_cpu(mem, machine: str) -> Cpu:
        cpu = CpuFactory._cpus[machine](mem)
        mem.cpu = cpu
        return cpu

    @staticmethod
    def get_function_abi(cpu: Cpu, os: str, machine: str) -> Abi:
        if os != "linux" or machine not in CpuFactory._linux_abis:
            raise NotImplementedError(f"OS and machine combination not supported: {os}/{machine}")

        return CpuFactory._linux_abis[machine](cpu)

    @staticmethod
    def get_syscall_abi(cpu: Cpu, os: str, machine: str) -> SyscallAbi:
        if os != "linux" or machine not in CpuFactory._linux_syscalls_abis:
            raise NotImplementedError(f"OS and machine combination not supported: {os}/{machine}")

        return CpuFactory._linux_syscalls_abis[machine](cpu)
