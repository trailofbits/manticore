# -*- coding: utf-8 -*-
"""
Aarch64 aka arm64 CPU implementation.
"""
from __future__ import absolute_import
from __future__ import division
from __future__ import print_function
from __future__ import unicode_literals

import warnings

from manticore.core.cpu.abstractcpu import Cpu, RegisterFile, Abi, SyscallAbi

import capstone as cs

from manticore.core.cpu.register import Register


class Aarch64RegisterFile(RegisterFile):
    _R_REGS = tuple('R%d' % i for i in range(31))
    _V_REGS = tuple('V%d' % i for i in range(31))

    def __init__(self):
        # TODO / FIXME: This is probably valid only for 'aarch32 state'
        alias_regs = {
            # 'SB': 'R9',
            # 'SL': 'R10',
            # 'FP': 'R11',
            # 'IP': 'R12',
            'STACK': 'R13',
            # 'SP': 'R13',
            # 'LR': 'R14',
            'PC': 'R15',
        }

        # Via ARM® Architecture Reference Manual - ARMv8, for ARMv8-A architecture profile
        # B1.2.1 Registers in AArch64 state
        # In the AArch64 application level view, an ARM processing element has:
        # R0-R30 31 general-purpose registers, R0 to R30. Each register can be accessed as:
        # • A 64-bit general-purpose register named X0 to X30.
        # • A 32-bit general-purpose register named W0 to W30.
        alias_regs.update(
            ((r, r.replace('R', 'X')) for r in self._R_REGS)
        )

        # V0-V31 32 SIMD&FP registers, V0 to V31
        # each of those can be accessed as 128-bit registers named Q0 to Q31
        alias_regs.update(
            ((v, v.replace('V', 'Q')) for v in self._V_REGS)
        )

        super(Aarch64RegisterFile, self).__init__(alias_regs)

        self._regs = {}

        # 64 bit registers
        for reg_name in self._R_REGS:
            self._regs[reg_name] = Register(64)

        # 128 bit SIMD registers
        for reg_name in self._V_REGS:
            self._regs[reg_name] = Register(128)

    def read(self, register):
        register = self._alias(register)
        return self._regs[register].read()

    def write(self, register, value):
        register = self._alias(register)
        self._regs[register].write(value)

    @property
    def canonical_registers(self):
        return self._R_REGS

    @property
    def all_registers(self):
        return super(Aarch64RegisterFile, self).all_registers + self._R_REGS + self._V_REGS


class Aarch64Cpu(Cpu):
    """
    Cpu specialization handling the ARM64 architecture.
    """
    address_bit_size = 64
    max_instr_width = 4
    machine = 'armv8'
    arch = cs.CS_ARCH_ARM64
    mode = cs.CS_MODE_ARM

    def __init__(self, memory):
        warnings.warn('Aarch64 support is experimental; it might not work well yet; feel free to help with that')
        super(Aarch64Cpu, self).__init__(Aarch64RegisterFile(), memory)


class Aarch64CdeclAbi(Abi):
    """Aarch64/arm64 cdecl function call ABI"""

    def get_arguments(self):
        # TODO / FIXME: Is this valid? As this might be just lower part of X0-X7 = W0-W7

        # First eight arguments are passed via X0-X7 (or W0-W7 if they are 32bit), then on stack
        for reg in ('X0', 'X1', 'X2', 'X3', 'X4', 'X5', 'X6', 'X7'):
            yield reg

        for address in self.values_from(self._cpu.STACK):
            yield address

    def write_result(self, result):
        self._cpu.W0 = result

    def ret(self):
        self._cpu.PC = self._cpu.LR


class Aarch64LinuxSyscallAbi(SyscallAbi):
    """Aarch64/arm64 Linux system call ABI"""

    # EABI standards:
    #  syscall # is in X8
    #  arguments are passed in X0-R5
    #  retval is passed in R0
    def syscall_number(self):
        return self._cpu.X8

    def get_arguments(self):
        return ('X{}'.format(i) for i in range(6))

    def write_result(self, result):
        self._cpu.R0 = result
