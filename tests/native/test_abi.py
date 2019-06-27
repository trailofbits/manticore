#!/usr/bin/env python
# -*- coding: utf-8 -*-

import unittest

from manticore.native.cpu.abstractcpu import (
    ConcretizeArgument,
    ConcretizeRegister,
    ConcretizeMemory,
)
from manticore.native.cpu.arm import Armv7Cpu, Armv7LinuxSyscallAbi, Armv7CdeclAbi
from manticore.native.cpu.aarch64 import Aarch64Cpu, Aarch64LinuxSyscallAbi, Aarch64CdeclAbi
from manticore.native.cpu.x86 import (
    I386Cpu,
    AMD64Cpu,
    I386LinuxSyscallAbi,
    I386StdcallAbi,
    I386CdeclAbi,
    AMD64LinuxSyscallAbi,
    SystemVAbi,
)
from manticore.native.memory import SMemory32, SMemory64
from manticore.core.smtlib import ConstraintSet, Operators
from manticore.native.models import variadic


class ABITest(unittest.TestCase):
    _multiprocess_can_split_ = True

    def setUp(self):
        mem32 = SMemory32(ConstraintSet())
        mem32.mmap(0x1000, 0x1000, "rw ")
        mem64 = SMemory64(ConstraintSet())
        mem64.mmap(0x1000, 0x1000, "rw ")

        self._cpu_aarch64 = Aarch64Cpu(mem64)
        self._cpu_aarch64.SP = 0x1080
        self._cpu_aarch64.func_abi = Aarch64CdeclAbi(self._cpu_aarch64)
        self._cpu_aarch64.syscall_abi = Aarch64LinuxSyscallAbi(self._cpu_aarch64)

        self._cpu_arm = Armv7Cpu(mem32)
        self._cpu_arm.SP = 0x1080
        self._cpu_arm.func_abi = Armv7CdeclAbi(self._cpu_arm)
        self._cpu_arm.syscall_abi = Armv7LinuxSyscallAbi(self._cpu_arm)

        self._cpu_x86 = I386Cpu(mem32)
        self._cpu_x86.ESP = 0x1080
        self._cpu_x86.func_abi = I386CdeclAbi(self._cpu_x86)
        self._cpu_x86.syscall_abi = I386LinuxSyscallAbi(self._cpu_x86)

        self._cpu_x64 = AMD64Cpu(mem64)
        self._cpu_x64.RSP = 0x1080
        self._cpu_x64.func_abi = SystemVAbi(self._cpu_x64)
        self._cpu_x64.syscall_abi = AMD64LinuxSyscallAbi(self._cpu_x64)

        def write(mem, where, val, size):
            mem[where : where + size // 8] = [
                Operators.CHR(Operators.EXTRACT(val, offset, 8)) for offset in range(0, size, 8)
            ]

        for val in range(0, 0x100, 4):
            write(mem32, 0x1000 + val, val, 32)
        for val in range(0, 0x100, 8):
            write(mem64, 0x1000 + val, val, 64)

    def test_executor(self):
        pass

    def test_aarch64_abi(self):
        cpu = self._cpu_aarch64

        for i in range(8):
            cpu.write_register(f"X{i}", i)

        cpu.LR = 0x1234

        self.assertEqual(cpu.read_int(cpu.SP), 0x80)

        # First 8 arguments in registers, then on stack.
        def test(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10):
            self.assertEqual(a0, 0)
            self.assertEqual(a1, 1)
            self.assertEqual(a2, 2)
            self.assertEqual(a3, 3)
            self.assertEqual(a4, 4)
            self.assertEqual(a5, 5)
            self.assertEqual(a6, 6)
            self.assertEqual(a7, 7)
            self.assertEqual(a8, 0x80)
            self.assertEqual(a9, 0x88)
            self.assertEqual(a10, 0x90)

            self.assertEqual(cpu.SP, 0x1080)
            return 42

        cpu.func_abi.invoke(test)

        # Result is correctly captured.
        self.assertEqual(cpu.X0, 42)
        # SP is unchanged.
        self.assertEqual(cpu.SP, 0x1080)
        # Returned correctly.
        self.assertEqual(cpu.PC, cpu.LR)

    def test_aarch64_syscall(self):
        cpu = self._cpu_aarch64

        cpu.X8 = 6
        for i in range(6):
            cpu.write_register(f"X{i}", i)

        def test(a0, a1, a2, a3, a4, a5):
            self.assertEqual(a0, 0)
            self.assertEqual(a1, 1)
            self.assertEqual(a2, 2)
            self.assertEqual(a3, 3)
            self.assertEqual(a4, 4)
            self.assertEqual(a5, 5)
            return 42

        self.assertEqual(cpu.syscall_abi.syscall_number(), 6)

        cpu.syscall_abi.invoke(test)

        self.assertEqual(cpu.X0, 42)

    def test_arm_abi_simple(self):
        cpu = self._cpu_arm

        for i in range(4):
            cpu.write_register(f"R{i}", i)

        cpu.LR = 0x1234

        def test(a0, a1, a2, a3):
            self.assertEqual(a0, 0)
            self.assertEqual(a1, 1)
            self.assertEqual(a2, 2)
            self.assertEqual(a3, 3)
            return 34

        cpu.func_abi.invoke(test)

        # result is correctly captured
        self.assertEqual(cpu.R0, 34)
        # sp is unchanged
        self.assertEqual(cpu.SP, 0x1080)
        # returned correctly
        self.assertEqual(cpu.PC, cpu.LR)

    def test_arm_abi(self):
        cpu = self._cpu_arm

        for i in range(4):
            cpu.write_register(f"R{i}", i)

        cpu.LR = 0x1234

        self.assertEqual(cpu.read_int(cpu.SP), 0x80)

        def test(a0, a1, a2, a3, a4, a5, a6):
            self.assertEqual(a0, 0)
            self.assertEqual(a1, 1)
            self.assertEqual(a2, 2)
            self.assertEqual(a3, 3)
            self.assertEqual(a4, 0x80)
            self.assertEqual(a5, 0x84)
            self.assertEqual(a6, 0x88)

            self.assertEqual(cpu.SP, 0x1080)
            return 34

        cpu.func_abi.invoke(test)

        # result is correctly captured
        self.assertEqual(cpu.R0, 34)
        # sp is unchanged
        self.assertEqual(cpu.SP, 0x1080)
        # returned correctly
        self.assertEqual(cpu.PC, cpu.LR)

    def test_arm_abi_concretize_register(self):
        cpu = self._cpu_arm

        for i in range(4):
            cpu.write_register(f"R{i}", i)

        previous_r0 = cpu.R0
        self.assertEqual(cpu.read_int(cpu.SP), 0x80)

        def test(a0, a1, a2, a3, a4, a5):
            raise ConcretizeArgument(cpu, 0)

        with self.assertRaises(ConcretizeRegister) as cr:
            cpu.func_abi.invoke(test)

        self.assertEqual(cpu.R0, previous_r0)
        self.assertEqual(cr.exception.reg_name, "R0")
        self.assertEqual(cpu.SP, 0x1080)

    def test_arm_abi_concretize_memory(self):
        cpu = self._cpu_arm

        for i in range(4):
            cpu.write_register(f"R{i}", i)

        previous_r0 = cpu.R0
        self.assertEqual(cpu.read_int(cpu.SP), 0x80)

        def test(a0, a1, a2, a3, a4):
            raise ConcretizeArgument(cpu, 4)

        with self.assertRaises(ConcretizeMemory) as cr:
            cpu.func_abi.invoke(test)

        self.assertEqual(cpu.R0, previous_r0)
        self.assertEqual(cr.exception.address, cpu.SP)
        self.assertEqual(cpu.SP, 0x1080)

    def test_i386_cdecl(self):
        cpu = self._cpu_x86

        base = cpu.ESP

        self.assertEqual(cpu.read_int(cpu.ESP), 0x80)
        cpu.push(0x1234, cpu.address_bit_size)

        def test(a0, a1, a2, a3, a4):
            self.assertEqual(a0, 0x80)
            self.assertEqual(a1, 0x84)
            self.assertEqual(a2, 0x88)
            self.assertEqual(a3, 0x8C)
            self.assertEqual(a4, 0x90)
            return 3

        cpu.func_abi.invoke(test)

        self.assertEqual(cpu.EAX, 3)
        self.assertEqual(base, cpu.ESP)
        self.assertEqual(cpu.EIP, 0x1234)

    def test_i386_stdcall(self):
        cpu = self._cpu_x86

        base = cpu.ESP

        bwidth = cpu.address_bit_size // 8
        self.assertEqual(cpu.read_int(cpu.ESP), 0x80)

        cpu.push(0x1234, cpu.address_bit_size)

        def test(a0, a1, a2, a3, a4):
            self.assertEqual(a0, 0x80)
            self.assertEqual(a1, 0x84)
            self.assertEqual(a2, 0x88)
            self.assertEqual(a3, 0x8C)
            self.assertEqual(a4, 0x90)
            return 3

        abi = I386StdcallAbi(cpu)
        abi.invoke(test)

        self.assertEqual(cpu.EAX, 3)
        self.assertEqual(base + bwidth * 5, cpu.ESP)
        self.assertEqual(cpu.EIP, 0x1234)

    def test_i386_stdcall_concretize(self):
        cpu = self._cpu_x86

        bwidth = cpu.address_bit_size // 8
        self.assertEqual(cpu.read_int(cpu.ESP), 0x80)

        cpu.push(0x1234, cpu.address_bit_size)

        eip = 0xDEADBEEF
        base = cpu.ESP
        cpu.EIP = eip

        def test(a0, a1, a2, a3, a4):
            raise ConcretizeArgument(cpu, 2)

        abi = I386StdcallAbi(cpu)
        with self.assertRaises(ConcretizeMemory) as cr:
            abi.invoke(test)

        # Make sure ESP hasn't changed if exception was raised
        self.assertEqual(base, cpu.ESP)
        # Make sure EIP hasn't changed (i.e. return value wasn't popped)
        self.assertEqual(cpu.EIP, eip)

    def test_i386_cdecl_concretize(self):
        cpu = self._cpu_x86

        base = cpu.ESP
        prev_eax = 0xCC
        cpu.EAX = prev_eax

        self.assertEqual(cpu.read_int(cpu.ESP), 0x80)
        cpu.push(0x1234, cpu.address_bit_size)

        def test(a0, a1, a2, a3, a4):
            raise ConcretizeArgument(cpu, 0)  # 0x1068
            return 3

        with self.assertRaises(ConcretizeMemory) as cr:
            cpu.func_abi.invoke(test)

        # Make sure we're concretizing
        self.assertEqual(cr.exception.address, 0x1080)
        # Make sure eax is unchanged
        self.assertEqual(cpu.EAX, prev_eax)
        # Make sure EIP wasn't popped
        self.assertEqual(base, cpu.ESP + 4)
        self.assertNotEqual(cpu.EIP, 0x1234)

    def test_i386_vararg(self):
        cpu = self._cpu_x86

        cpu.push(3, cpu.address_bit_size)
        cpu.push(2, cpu.address_bit_size)
        cpu.push(1, cpu.address_bit_size)

        # save return
        cpu.push(0x1234, cpu.address_bit_size)

        @variadic
        def test(params):
            for val, idx in zip(params, range(1, 4)):
                self.assertEqual(val, idx)

        cpu.func_abi.invoke(test)
        self.assertEqual(cpu.EIP, 0x1234)

    def test_amd64_basic_funcall(self):
        cpu = self._cpu_x64

        cpu.RDI = 1
        cpu.RSI = 2
        cpu.RDX = 3
        cpu.RCX = 4
        cpu.R8 = 5
        cpu.R9 = 6

        cpu.push(0x1234, cpu.address_bit_size)

        def test(a0, a1, a2, a3, a4, a5):
            self.assertEqual(a0, 1)
            self.assertEqual(a1, 2)
            self.assertEqual(a2, 3)
            self.assertEqual(a3, 4)
            self.assertEqual(a4, 5)
            self.assertEqual(a5, 6)

        cpu.func_abi.invoke(test)

        self.assertEqual(cpu.RIP, 0x1234)

    def test_amd64_reg_mem_funcall(self):
        cpu = self._cpu_x64

        cpu.RDI = 1
        cpu.RSI = 2
        cpu.RDX = 3
        cpu.RCX = 4
        cpu.R8 = 5
        cpu.R9 = 6

        cpu.push(0x1234, cpu.address_bit_size)

        def test(a0, a1, a2, a3, a4, a5, a6, a7):
            self.assertEqual(a0, 1)
            self.assertEqual(a1, 2)
            self.assertEqual(a2, 3)
            self.assertEqual(a3, 4)
            self.assertEqual(a4, 5)
            self.assertEqual(a5, 6)
            self.assertEqual(a6, 0x80)
            self.assertEqual(a7, 0x88)

        cpu.func_abi.invoke(test)

        self.assertEqual(cpu.RIP, 0x1234)

    def test_amd64_basic_funcall_concretize(self):
        cpu = self._cpu_x64

        cpu.push(0x1234, cpu.address_bit_size)

        def test(a0, a1, a2, a3, a4, a5):
            raise ConcretizeArgument(cpu, 0)

        with self.assertRaises(ConcretizeRegister) as cr:
            cpu.func_abi.invoke(test)

        # Should not update RIP
        self.assertNotEqual(cpu.RIP, 0x1234)
        self.assertEqual(cr.exception.reg_name, "RDI")

    def test_amd64_vararg(self):
        cpu = self._cpu_x64

        cpu.RDI = 0
        cpu.RSI = 1
        cpu.RDX = 2

        # save return
        cpu.push(0x1234, cpu.address_bit_size)

        @variadic
        def test(params):
            for val, idx in zip(params, list(range(3))):
                self.assertEqual(val, idx)

        cpu.func_abi.invoke(test)

        self.assertEqual(cpu.RIP, 0x1234)

    def test_i386_syscall(self):
        cpu = self._cpu_x86

        cpu.EAX = 5
        for idx, reg in enumerate(["EBX", "ECX", "EDX", "ESI", "EDI", "EBP"]):
            cpu.write_register(reg, idx)

        def test(a0, a1, a2, a3, a4, a5):
            self.assertEqual(a0, 0)
            self.assertEqual(a1, 1)
            self.assertEqual(a2, 2)
            self.assertEqual(a3, 3)
            self.assertEqual(a4, 4)
            self.assertEqual(a5, 5)
            return 34

        self.assertEqual(cpu.syscall_abi.syscall_number(), 5)

        cpu.syscall_abi.invoke(test)

        self.assertEqual(cpu.EAX, 34)

    def test_amd64_syscall(self):
        cpu = self._cpu_x64

        cpu.RAX = 5
        for idx, reg in enumerate(["RDI", "RSI", "RDX", "R10", "R8", "R9"]):
            cpu.write_register(reg, idx)

        def test(a0, a1, a2, a3, a4, a5):
            self.assertEqual(a0, 0)
            self.assertEqual(a1, 1)
            self.assertEqual(a2, 2)
            self.assertEqual(a3, 3)
            self.assertEqual(a4, 4)
            self.assertEqual(a5, 5)
            return 34

        self.assertEqual(cpu.syscall_abi.syscall_number(), 5)

        cpu.syscall_abi.invoke(test)

        self.assertEqual(cpu.RAX, 34)

    def test_test_prefix(self):
        cpu = self._cpu_x86

        cpu.push(2, cpu.address_bit_size)
        cpu.push(0x1234, cpu.address_bit_size)

        def test(prefix, extracted):
            self.assertEqual(prefix, 1)
            self.assertEqual(extracted, 2)

        cpu.func_abi.invoke(test, prefix_args=(1,))

        self.assertEqual(cpu.EIP, 0x1234)

    def test_fail_concretize_prefix_arg(self):
        cpu = self._cpu_x86

        def test(prefix, extracted):
            raise ConcretizeArgument(cpu, 0)

        if __debug__:
            with self.assertRaises(AssertionError) as cr:
                cpu.func_abi.invoke(test, prefix_args=(1,))

    def test_funcall_method(self):
        cpu = self._cpu_x86

        cpu.push(2, cpu.address_bit_size)
        cpu.push(1, cpu.address_bit_size)
        cpu.push(0x1234, cpu.address_bit_size)

        class Kls:
            def method(self, a, b):
                return a + b

        obj = Kls()
        result = cpu.func_abi.invoke(obj.method)

        self.assertEqual(result, 3)
