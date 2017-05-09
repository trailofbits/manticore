from .x86 import AMD64Cpu, I386Cpu, AMD64LinuxSyscallAbi, I386LinuxSyscallAbi, I386CdeclAbi, SystemVAbi
from .arm import Armv7Cpu, Armv7CdeclAbi, Armv7LinuxSyscallAbi

class CpuFactory(object):
    _cpus = {
        'i386': I386Cpu,
        'amd64': AMD64Cpu,
        'armv7': Armv7Cpu
    }

    @staticmethod
    def get_cpu(mem, machine):
        return CpuFactory._cpus[machine](mem)

    @staticmethod
    def get_function_abi(cpu, os, machine):
        if os == 'linux' and machine == 'i386':
            return I386CdeclAbi(cpu)
        elif os == 'linux' and machine == 'amd64':
            return SystemVAbi(cpu)
        elif os == 'linux' and machine == 'armv7':
            return Armv7CdeclAbi(cpu)
        else:
            return NotImplementedError("OS and machine combination not supported: {}/{}".format(os, machine))

    @staticmethod
    def get_syscall_abi(cpu, os, machine):
        if os == 'linux' and machine == 'i386':
            return I386LinuxSyscallAbi(cpu)
        elif os == 'linux' and machine == 'amd64':
            return AMD64LinuxSyscallAbi(cpu)
        elif os == 'linux' and machine == 'armv7':
            return Armv7LinuxSyscallAbi(cpu)
        else:
            return NotImplementedError("OS and machine combination not supported: {}/{}".format(os, machine))


