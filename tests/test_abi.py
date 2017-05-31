#!/usr/bin/env python
# -*- coding: utf-8 -*-

import unittest
import sys
import shutil
import tempfile
import os
import hashlib
import subprocess
import collections
import time

from manticore import Manticore, issymbolic
from manticore import variadic
from manticore.core.smtlib import BitVecVariable
from manticore.core.cpu.abstractcpu import ConcretizeArgument, ConcretizeRegister, ConcretizeMemory
from manticore.core.cpu.arm import Armv7Cpu, Armv7LinuxSyscallAbi, Armv7CdeclAbi
from manticore.core.cpu.x86 import I386Cpu, AMD64Cpu, I386LinuxSyscallAbi, I386StdcallAbi, I386CdeclAbi, AMD64LinuxSyscallAbi, SystemVAbi
from manticore.core.memory import SMemory32, Memory32, SMemory64
from manticore.core.smtlib import ConstraintSet, Operators

class ABITests(unittest.TestCase):
    def setUp(self):
        mem32 = SMemory32(ConstraintSet())
        mem32.mmap(0x1000, 0x1000, 'rw ')
        mem64 = SMemory64(ConstraintSet())
        mem64.mmap(0x1000, 0x1000, 'rw ')

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
            mem[where:where+size/8] = [Operators.CHR(Operators.EXTRACT(val, offset, 8)) for offset in xrange(0, size, 8)]
        for val in range(0, 0x100, 4):
            write(mem32, 0x1000+val, val, 32)
        for val in range(0, 0x100, 8):
            write(mem64, 0x1000+val, val, 64)

    def test_executor(self):
        pass
    
    def test_arm_abi_simple(self):
        cpu = self._cpu_arm

        for i in range(4):
            cpu.write_register('R{}'.format(i), i)

        cpu.LR = 0x1234

        def test(one, two, three, four):
            self.assertEqual(one,   0)
            self.assertEqual(two,   1)
            self.assertEqual(three, 2)
            self.assertEqual(four,  3)
            return 34

        cpu.func_abi.invoke(test)

        # result is correctly captured
        self.assertEquals(cpu.R0, 34)
        # sp is unchanged
        self.assertEquals(cpu.SP, 0x1080)
        # returned correctly
        self.assertEquals(cpu.PC, cpu.LR)

    def test_arm_abi(self):
        cpu = self._cpu_arm

        for i in range(4):
            cpu.write_register('R{}'.format(i), i)

        cpu.LR = 0x1234

        self.assertEqual(cpu.read_int(cpu.SP), 0x80)

        def test(one, two, three, four, five, six, seven):
            self.assertEqual(one,     0)
            self.assertEqual(two,     1)
            self.assertEqual(three,   2)
            self.assertEqual(four,    3)
            self.assertEqual(five,    0x80)
            self.assertEqual(six,     0x84)
            self.assertEqual(seven,   0x88)

            self.assertEqual(cpu.SP,  0x1080)
            return 34

        cpu.func_abi.invoke(test)

        # result is correctly captured
        self.assertEquals(cpu.R0, 34)
        # sp is unchanged
        self.assertEquals(cpu.SP, 0x1080)
        # returned correctly
        self.assertEquals(cpu.PC, cpu.LR)

    def test_arm_abi_concretize_register(self):
        cpu = self._cpu_arm

        for i in range(4):
            cpu.write_register('R{}'.format(i), i)

        previous_r0 = cpu.R0
        self.assertEqual(cpu.read_int(cpu.SP), 0x80)

        def test(one, two, three, four, five, six):
            raise ConcretizeArgument(0)

        with self.assertRaises(ConcretizeRegister) as cr:
            cpu.func_abi.invoke(test)

        self.assertEquals(cpu.R0, previous_r0)
        self.assertEquals(cr.exception.reg_name, 'R0')
        self.assertEquals(cpu.SP, 0x1080)

    def test_arm_abi_concretize_memory(self):
        cpu = self._cpu_arm

        for i in range(4):
            cpu.write_register('R{}'.format(i), i)

        previous_r0 = cpu.R0
        self.assertEqual(cpu.read_int(cpu.SP), 0x80)

        def test(one, two, three, four, five):
            raise ConcretizeArgument(4)

        with self.assertRaises(ConcretizeMemory) as cr:
            cpu.func_abi.invoke(test)

        self.assertEquals(cpu.R0, previous_r0)
        self.assertEquals(cr.exception.address, cpu.SP)
        self.assertEquals(cpu.SP, 0x1080)

    def test_i386_cdecl(self):
        cpu = self._cpu_x86

        base = cpu.ESP 

        self.assertEqual(cpu.read_int(cpu.ESP), 0x80)
        cpu.push(0x1234, cpu.address_bit_size)

        def test(one, two, three, four, five):
            self.assertEqual(one,   0x80)
            self.assertEqual(two,   0x84)
            self.assertEqual(three, 0x88)
            self.assertEqual(four,  0x8c)
            self.assertEqual(five,  0x90)
            return 3

        cpu.func_abi.invoke(test)

        self.assertEquals(cpu.EAX, 3)
        self.assertEquals(base, cpu.ESP)
        self.assertEquals(cpu.EIP, 0x1234)

    def test_i386_stdcall(self):
        cpu = self._cpu_x86

        base = cpu.ESP 

        bwidth = cpu.address_bit_size / 8
        self.assertEqual(cpu.read_int(cpu.ESP), 0x80)

        cpu.push(0x1234, cpu.address_bit_size)

        def test(one, two, three, four, five):
            self.assertEqual(one,   0x80)
            self.assertEqual(two,   0x84)
            self.assertEqual(three, 0x88)
            self.assertEqual(four,  0x8c)
            self.assertEqual(five,  0x90)
            return 3

        abi = I386StdcallAbi(cpu)
        abi.invoke(test)

        self.assertEquals(cpu.EAX, 3)
        self.assertEquals(base + bwidth * 5, cpu.ESP)
        self.assertEquals(cpu.EIP, 0x1234)

    def test_i386_stdcall_concretize(self):
        cpu = self._cpu_x86

        bwidth = cpu.address_bit_size / 8
        self.assertEqual(cpu.read_int(cpu.ESP), 0x80)

        cpu.push(0x1234, cpu.address_bit_size)

        eip = 0xDEADBEEF
        base = cpu.ESP 
        cpu.EIP = eip
        def test(one, two, three, four, five):
            raise ConcretizeArgument(2)

        abi = I386StdcallAbi(cpu)
        with self.assertRaises(ConcretizeMemory) as cr:
            abi.invoke(test)

        # Make sure ESP hasn't changed if exception was raised
        self.assertEquals(base, cpu.ESP)
        # Make sure EIP hasn't changed (i.e. return value wasn't popped)
        self.assertEquals(cpu.EIP, eip)

    def test_i386_cdecl_concretize(self):
        cpu = self._cpu_x86

        base = cpu.ESP 
        prev_eax = 0xcc
        cpu.EAX = prev_eax
        
        self.assertEqual(cpu.read_int(cpu.ESP), 0x80)
        cpu.push(0x1234, cpu.address_bit_size)

        def test(one, two, three, four, five):
            raise ConcretizeArgument(0) # 0x1068
            return 3

        with self.assertRaises(ConcretizeMemory) as cr:
            cpu.func_abi.invoke(test)

        # Make sure we're concretizing
        self.assertEquals(cr.exception.address, 0x1080)
        # Make sure eax is unchanged
        self.assertEquals(cpu.EAX, prev_eax)
        # Make sure EIP wasn't popped
        self.assertEquals(base, cpu.ESP+4)
        self.assertNotEquals(cpu.EIP, 0x1234)


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
        self.assertEquals(cpu.EIP, 0x1234)


    def test_amd64_basic_funcall(self):
        cpu = self._cpu_x64

        cpu.RDI = 1
        cpu.RSI = 2
        cpu.RDX = 3
        cpu.RCX = 4
        cpu.R8 = 5
        cpu.R9 = 6

        cpu.push(0x1234, cpu.address_bit_size)

        def test(one, two, three, four, five, six):
            self.assertEqual(one, 1)
            self.assertEqual(two, 2)
            self.assertEqual(three, 3)
            self.assertEqual(four, 4)
            self.assertEqual(five, 5)
            self.assertEqual(six, 6)

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

        def test(one, two, three, four, five, six, seven, eight):
            self.assertEqual(one, 1)
            self.assertEqual(two, 2)
            self.assertEqual(three, 3)
            self.assertEqual(four, 4)
            self.assertEqual(five, 5)
            self.assertEqual(six, 6)
            self.assertEqual(seven, 0x80)
            self.assertEqual(eight, 0x88)

        cpu.func_abi.invoke(test)

        self.assertEqual(cpu.RIP, 0x1234)

    def test_amd64_basic_funcall_concretize(self):
        cpu = self._cpu_x64

        cpu.push(0x1234, cpu.address_bit_size)

        def test(one, two, three, four, five, six):
            raise ConcretizeArgument(0)

        with self.assertRaises(ConcretizeRegister) as cr:
            cpu.func_abi.invoke(test)

        # Should not update RIP
        self.assertNotEqual(cpu.RIP, 0x1234)
        self.assertEquals(cr.exception.reg_name, 'RDI')

    def test_amd64_vararg(self):
        cpu = self._cpu_x64

        cpu.RDI = 0
        cpu.RSI = 1
        cpu.RDX = 2

        # save return
        cpu.push(0x1234, cpu.address_bit_size)

        @variadic
        def test(params):
            for val, idx in zip(params, range(3)):
                self.assertEqual(val, idx)

        cpu.func_abi.invoke(test)

        self.assertEquals(cpu.RIP, 0x1234)

    def test_i386_syscall(self):
        cpu = self._cpu_x86

        cpu.EAX = 5
        for idx, reg in enumerate(['EBX', 'ECX', 'EDX', 'ESI', 'EDI', 'EBP']):
            cpu.write_register(reg, idx)

        def test(one, two, three, four, five, six):
            self.assertEqual(one, 0)
            self.assertEqual(two, 1)
            self.assertEqual(three, 2)
            self.assertEqual(four, 3)
            self.assertEqual(five, 4)
            self.assertEqual(six, 5)
            return 34

        self.assertEqual(cpu.syscall_abi.syscall_number(), 5)

        cpu.syscall_abi.invoke(test)

        self.assertEqual(cpu.EAX, 34)

    def test_amd64_syscall(self):
        cpu = self._cpu_x64

        cpu.RAX = 5
        for idx, reg in enumerate(['RDI', 'RSI', 'RDX', 'R10', 'R8', 'R9']):
            cpu.write_register(reg, idx)

        def test(one, two, three, four, five, six):
            self.assertEqual(one, 0)
            self.assertEqual(two, 1)
            self.assertEqual(three, 2)
            self.assertEqual(four, 3)
            self.assertEqual(five, 4)
            self.assertEqual(six, 5)
            return 34

        self.assertEqual(cpu.syscall_abi.syscall_number(), 5)

        cpu.syscall_abi.invoke(test)

        self.assertEqual(cpu.RAX, 34)

    def test_test_prefix(self):
        cpu = self._cpu_x86

        cpu.push(2, cpu.address_bit_size)
        cpu.push(0x1234, cpu.address_bit_size)
        
        def test(prefix, extracted):
            self.assertEquals(prefix, 1)
            self.assertEquals(extracted, 2)

        cpu.func_abi.invoke(test, prefix_args=(1,))

        self.assertEquals(cpu.EIP, 0x1234)

    def test_fail_concretize_prefix_arg(self):
        cpu = self._cpu_x86

        def test(prefix, extracted):
            raise ConcretizeArgument(0)

        with self.assertRaises(AssertionError) as cr:
            cpu.func_abi.invoke(test, prefix_args=(1,))

    def test_funcall_method(self):
        cpu = self._cpu_x86

        cpu.push(2, cpu.address_bit_size)
        cpu.push(1, cpu.address_bit_size)
        cpu.push(0x1234, cpu.address_bit_size)

        class Kls(object):
            def method(self, a, b):
                return a+b

        obj = Kls()
        result = cpu.func_abi.invoke(obj.method)

        self.assertEquals(result, 3)

