from .x86 import AMD64Cpu, I386Cpu
from .arm import Armv7Cpu

class CpuFactory(object):
    _cpus = {
        'i386': I386Cpu,
        'amd64': AMD64Cpu,
        'armv7': Armv7Cpu
    }

    @staticmethod
    def get_cpu(mem, machine):
        return CpuFactory._cpus[machine](mem)

