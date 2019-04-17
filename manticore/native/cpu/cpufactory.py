from manticore.native.cpu.arm import Armv7Cpu, Armv7CdeclAbi, Armv7LinuxSyscallAbi
from manticore.native.cpu.x86 import (AMD64Cpu, I386Cpu, AMD64LinuxSyscallAbi, I386LinuxSyscallAbi, I386CdeclAbi,
    SystemVAbi)


class CpuFactory:
    _cpus = {
        'i386': I386Cpu,
        'amd64': AMD64Cpu,
        'armv7': Armv7Cpu,
    }

    @staticmethod
    def get_cpu(mem, machine):
        cpu = CpuFactory._cpus[machine](mem)
        mem.cpu = cpu
        return cpu

    @staticmethod
    def get_function_abi(cpu, os, machine):
        if os == 'linux' and machine == 'i386':
            return I386CdeclAbi(cpu)
        elif os == 'linux' and machine == 'amd64':
            return SystemVAbi(cpu)
        elif os == 'linux' and machine == 'armv7':
            return Armv7CdeclAbi(cpu)
        else:
            return NotImplementedError(f"OS and machine combination not supported: {os}/{machine}")

    @staticmethod
    def get_syscall_abi(cpu, os, machine):
        if os == 'linux' and machine == 'i386':
            return I386LinuxSyscallAbi(cpu)
        elif os == 'linux' and machine == 'amd64':
            return AMD64LinuxSyscallAbi(cpu)
        elif os == 'linux' and machine == 'armv7':
            return Armv7LinuxSyscallAbi(cpu)
        else:
            return NotImplementedError(f"OS and machine combination not supported: {os}/{machine}")
