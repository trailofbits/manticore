from __future__ import print_function
import copy
import traceback
import os
import sys
import time
import subprocess
from capstone import *
from capstone.x86 import *
from flags import flags

flags_maks = {
    "CF": 0x00001,
    "PF": 0x00004,
    "AF": 0x00010,
    "ZF": 0x00040,
    "SF": 0x00080,
    "DF": 0x00400,
    "OF": 0x00800,
    "IF": 0x00200,
}

count = 0

# log = file('gdb.log','a')
class Gdb(subprocess.Popen):
    def __init__(self, prg, prompt="(gdb) "):
        """Construct interactive Popen."""
        self.prompt = prompt
        subprocess.Popen.__init__(
            self,
            ["gdb", prg],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )

    def correspond(self, text):
        """Communicate with the child process without closing stdin."""
        self.stdin.write(text)
        self.stdin.flush()
        str_buffer = ""
        while not str_buffer.endswith(self.prompt):
            str_buffer += self.stdout.read(1)
        # log.write(f">{text}\n")
        # log.write(f"<{str_buffer}\n")
        return str_buffer

    def getR(self, reg):
        reg = f"${reg}"
        if "XMM" in reg:
            reg = f"{reg}.uint128"
            val = self.correspond(f"p {reg.lower()}\n").split("=")[-1].split("\n")[0]
            if "0x" in val:
                return int(val.split("0x")[-1], 16)
            else:
                return int(val)
        if "FLAG" in reg:
            reg = f"(unsigned) {reg}"
        if reg in [f"$R{i}B" for i in range(16)]:
            reg = reg[:-1] + "&0xff"
        if reg in [f"$R{i}W" for i in range(16)]:
            reg = reg[:-1] + "&0xffff"
        val = self.correspond(f"p /x {reg.lower()}\n")
        val = val.split("0x")[-1]
        return long(val.split("\n")[0], 16)

    def setR(reg, value):
        self.correspond(f"set ${reg.lower()} = {value}\n")

    def setByte(self, m, value):
        self.correspond(f"set *(char*)({m}) = {value}\n")

    def stepi(self):
        # print self.correspond("x/i $pc\n")
        self.correspond("stepi\n")

    def getM(self, m):
        try:
            return long(
                self.correspond(f"x/xg {m}\n").split("\t")[-1].split("0x")[-1].split("\n")[0], 16
            )
        except Exception as e:
            raise e
            return 0

    def get_pid(self):
        return int(self.correspond("info proc\n").split("\n")[0].split(" ")[-1])

    def getStack(self):
        procid = self.correspond("info proc\n").split("\n")[0].split(" ")[-1]
        maps = file(f"/proc/{procid}/maps").read().split("\n")
        i, o = [int(x, 16) for x in maps[-3].split(" ")[0].split("-")]

    def getByte(self, m):
        arch = self.get_arch()
        mask = {"i386": 0xFFFFFFFF, "amd64": 0xFFFFFFFFFFFFFFFF}[arch]
        return int(self.correspond(f"x/1bx {m & mask}\n").split("\t")[-1].split("\n")[0][2:], 16)

    def get_entry(self):
        a = self.correspond("info target\n")
        return int(a[a.find("Entry point:") :].split("\n")[0].split(" ")[-1][2:], 16)

    def get_maps(self):
        pid = self.get_pid()
        return file(f"/proc/{pid}/maps", "rb").read()

    _arch = None

    def get_arch(self):
        if self._arch is not None:
            return self._arch
        infotarget = self.correspond("info target\n")
        if "elf32-i386" in infotarget:
            self._arch = "i386"
            return "i386"
        elif "elf64-x86-64" in infotarget:
            self._arch = "amd64"
            return "amd64"
        else:
            print(infotarget)
            raise NotImplementedError()


gdb = Gdb(sys.argv[1])
gdb.correspond("")
# guess arch
arch = gdb.get_arch()
# guess architecture from file
entry = gdb.get_entry()
gdb.correspond("b *0\n")
gdb.correspond("run arg1 arg2 < /dev/urandom > /dev/null\n")
# gdb.correspond("run arg1 arg2 arg3 < input > /dev/null\n")
gdb.correspond("d 1\n")
# print gdb.get_maps()
"""
# Simulate no vdso (As when analyzed with symbemu)
found = 0
for i in range(75,120):
    if gdb.getM('$sp+sizeof(void*)*%d'%i) ==0x19 and gdb.getM('$sp+%d'%(i+2))==0x1f:
        found = i
if found !=0:
    gdb.setByte('$sp+sizeof(void*)*%d'%found,1)
    gdb.setByte('$sp+sizeof(void*)*%d'%(found+2),1)

vdso = gdb.getM('$sp+sizeof(void*)*%d'%(found+1))
for i in range(75,120):
    val = gdb.getM('$sp+sizeof(void*)*%d'%i)
    if val > vdso-0x10000 and val <= vdso+0x10000:
        if (gdb.getM('$sp+sizeof(void*)*%d'%(i-1))) != 1:
            gdb.setByte('$sp+sizeof(void*)*%d'%(i-1),1)
"""


def read_operand(o):
    if o.type == X86_OP_IMM:
        return o.value
    elif o.type == X86_OP_REG:
        reg_name = str(instruction.reg_name(o.reg).upper())
        return gdb.getR(reg_name)
    raise NotImplementedError(f"Unknown operand typ: {o.type}")


STACK_INSTRUCTIONS = [
    "BOUND",
    "CALL",
    "CALLF",
    "ENTER",
    "INT",
    "INT1",
    "INTO",
    "IRET",
    "IRETD",
    "LEAVE",
    "POP",
    "POPA",
    "POPAD",
    "POPF",
    "POPFD",
    "PUSH",
    "PUSHA",
    "PUSHAD",
    "PUSHF",
    "PUSHFD",
    "RETF",
    "RETN",
    "RET",
]
while True:
    try:
        stepped = False
        pc = gdb.getR({"i386": "EIP", "amd64": "RIP"}[arch])
        SP = {"i386": "ESP", "amd64": "RSP"}[arch]
        BP = {"i386": "EBP", "amd64": "RBP"}[arch]
        DI = {"i386": "EDI", "amd64": "RDI"}[arch]
        SI = {"i386": "ESI", "amd64": "RSI"}[arch]
        A = {"i386": "EAX", "amd64": "RAX"}[arch]
        D = {"i386": "EDX", "amd64": "RDX"}[arch]

        COUNTER = {"i386": "ECX", "amd64": "RCX"}[arch]
        wordsize = {"i386": 4, "amd64": 8}[arch]
        text = "".join([chr(gdb.getByte(pc + i)) for i in range(16)])

        cap_arch = {"i386": CS_ARCH_X86, "amd64": CS_ARCH_X86}[arch]
        cap_mode = {"i386": CS_MODE_32, "amd64": CS_MODE_64}[arch]
        md = Cs(cap_arch, cap_mode)
        md.detail = True
        md.syntax = 0

        instruction = next(md.disasm(text, pc))

        if instruction.insn_name().upper() in [
            "CPUID",
            "RDTSC",
            "NOP",
            "SYSCALL",
            "INT",
            "SYSENTER",
        ]:
            print("#Skiping:, ", instruction.insn_name().upper())
            stepped = True
            gdb.stepi()
            continue

        # print instruction
        disassembly = f"0x{instruction.address:x}:\t{instruction.mnemonic}\t{instruction.op_str}"
        print("#INSTRUCTION:", disassembly)
        groups = map(instruction.group_name, instruction.groups)

        PC = {"i386": "EIP", "amd64": "RIP"}[arch]
        registers = {PC: gdb.getR(PC)}
        memory = {}

        # save the encoded instruction
        for i in range(instruction.size):
            memory[pc + i] = text[i]

        if instruction.insn_name().upper() in ["MUL", "IMUL"]:
            registers[A] = gdb.getR(A)
            registers[D] = gdb.getR(D)

        if instruction.insn_name().upper() in ["AAA", "AAS", "AAD", "AAM"]:
            registers["AH"] = gdb.getR("AH")
            registers["AL"] = gdb.getR("AL")

        if instruction.insn_name().upper() in ["PUSHF", "PUSHFD"]:
            registers["EFLAGS"] = gdb.getR("EFLAGS")

        if instruction.insn_name().upper() in ["XLAT", "XLATB"]:
            registers["AL"] = gdb.getR("AL")
            registers[B] = gdb.getR(B)
            address = registers[B] + registers["AL"]
            memory[address] = chr(gdb.getByte(address))

        if instruction.insn_name().upper() in ["BTC", "BTR", "BTS", "BT"]:
            if instruction.operands[0].type == X86_OP_MEM:
                o = instruction.operands[0]
                address = 0
                address += o.mem.disp
                if o.mem.base != 0:
                    base = str(instruction.reg_name(o.mem.base).upper())
                    registers[base] = gdb.getR(base)
                    address += registers[base]
                    if base == "RIP":
                        address += instruction.size
                if o.mem.index != 0:
                    reg_name = str(instruction.reg_name(o.mem.index).upper())
                    registers[reg_name] = gdb.getR(reg_name)
                    address += o.mem.scale * registers[reg_name]
                address = address & ({"i386": 0xFFFFFFFF, "amd64": 0xFFFFFFFFFFFFFFFF}[arch])
                if instruction.operands[1].type == X86_OP_IMM:
                    address += instruction.operands.value
                elif instruction.operands[1].type == X86_OP_REG:
                    reg_name = str(instruction.reg_name(o.reg).upper())
                    address + gdb.getR(reg_name) // 8
                memory[address] = chr(gdb.getByte(address))

        if instruction.insn_name().upper() in STACK_INSTRUCTIONS:
            registers[SP] = gdb.getR(SP)
            registers[BP] = gdb.getR(BP)

            # save a bunch of stack
            pointer = registers[SP]
            for i in range(-wordsize, wordsize + 1):
                memory[pointer + i] = chr(gdb.getByte(pointer + i))

        if instruction.insn_name().upper() in ["ENTER", "LEAVE"]:
            pointer = registers[BP]
            for i in range(-wordsize, wordsize + 1):
                memory[pointer + i] = chr(gdb.getByte(pointer + i))

        if instruction.mnemonic.startswith("rep"):
            registers[DI] = gdb.getR(DI)
            registers[SI] = gdb.getR(SI)
            registers[COUNTER] = gdb.getR(COUNTER)
            pointer = registers[DI]
            for i in range(wordsize):
                memory[pointer + i] = chr(gdb.getByte(pointer + i))
            pointer = registers[SI]
            for i in range(wordsize):
                memory[pointer + i] = chr(gdb.getByte(pointer + i))

        # implicit registers
        # if not instruction.mnemonic.startswith('rep'):
        #    for ri in range(0xff):
        #        if instruction.reg_read(ri) or instruction.reg_write(ri):
        #            reg_name = str(instruction.reg_name(ri).upper())
        #            if 'FLAGS' in reg_name :
        #                continue
        #            registers[reg_name] = gdb.getR(reg_name)

        reg_sizes = {
            X86_REG_AH: X86_REG_AX,
            X86_REG_AL: X86_REG_AX,
            X86_REG_AX: X86_REG_EAX,
            X86_REG_EAX: X86_REG_RAX,
            X86_REG_RAX: X86_REG_INVALID,
            X86_REG_BH: X86_REG_BX,
            X86_REG_BL: X86_REG_BX,
            X86_REG_BX: X86_REG_EBX,
            X86_REG_EBX: X86_REG_RBX,
            X86_REG_RBX: X86_REG_INVALID,
            X86_REG_CH: X86_REG_CX,
            X86_REG_CL: X86_REG_CX,
            X86_REG_CX: X86_REG_ECX,
            X86_REG_ECX: X86_REG_RCX,
            X86_REG_RCX: X86_REG_INVALID,
            X86_REG_DH: X86_REG_DX,
            X86_REG_DL: X86_REG_DX,
            X86_REG_DX: X86_REG_EDX,
            X86_REG_EDX: X86_REG_RDX,
            X86_REG_RDX: X86_REG_INVALID,
            X86_REG_DIL: X86_REG_EDI,
            X86_REG_DI: X86_REG_EDI,
            X86_REG_EDI: X86_REG_RDI,
            X86_REG_RDI: X86_REG_INVALID,
            X86_REG_SIL: X86_REG_ESI,
            X86_REG_SI: X86_REG_ESI,
            X86_REG_ESI: X86_REG_RSI,
            X86_REG_RSI: X86_REG_INVALID,
        }
        # There is a capstone branch that should fix all these annoyances... soon
        # https://github.com/aquynh/capstone/tree/next
        used = set()
        for ri in reg_sizes.keys():
            if instruction.reg_read(ri) or instruction.reg_write(ri):
                if not (
                    instruction.reg_read(reg_sizes[ri]) or instruction.reg_write(reg_sizes[ri])
                ):
                    if str(instruction.reg_name(reg_sizes[ri]).upper()) not in registers.keys():
                        used.add(ri)

        for ri in used:
            reg_name = str(instruction.reg_name(ri).upper())
            registers[reg_name] = gdb.getR(reg_name)

        # special case for flags...
        if instruction.mnemonic.upper() in flags.keys():
            EFLAGS = gdb.getR("EFLAGS")
            for fl in flags[instruction.mnemonic.upper()]["tested"]:
                registers[fl] = (EFLAGS & flags_maks[fl]) != 0
            for fl in flags[instruction.mnemonic.upper()]["defined"]:
                registers[fl] = (EFLAGS & flags_maks[fl]) != 0
            if "regs" in flags[instruction.mnemonic.upper()]:
                for rg in flags[instruction.mnemonic.upper()]["regs"]:
                    registers[rg] = gdb.getR(rg)

        # operands
        for o in instruction.operands:
            if o.type == X86_OP_IMM:
                pass  # ignore, already encoded in instruction
            elif o.type == X86_OP_REG:
                reg_name = str(instruction.reg_name(o.reg).upper())
                registers[reg_name] = gdb.getR(reg_name)
            elif o.type == X86_OP_MEM:
                # save register involved and memory values
                address = 0
                address += o.mem.disp
                if o.mem.base != 0:
                    base = str(instruction.reg_name(o.mem.base).upper())
                    registers[base] = gdb.getR(base)
                    address += registers[base]
                    if base == "RIP":
                        address += instruction.size
                if o.mem.index != 0:
                    reg_name = str(instruction.reg_name(o.mem.index).upper())
                    registers[reg_name] = gdb.getR(reg_name)
                    address += o.mem.scale * registers[reg_name]
                address = address & ({"i386": 0xFFFFFFFF, "amd64": 0xFFFFFFFFFFFFFFFF}[arch])
                for i in xrange(address, address + o.size):
                    memory[i] = chr(gdb.getByte(i))

        # gather PRE info
        test = {
            "mnemonic": instruction.insn_name().upper(),
            "disassembly": disassembly,
            "groups": groups,
            "text": text[: instruction.size],
            "arch": arch,
        }

        test["pre"] = {}
        test["pre"]["memory"] = memory
        test["pre"]["registers"] = registers

        # STEP !
        gdb.stepi()
        stepped = True

        # gather POS info
        registers = dict(registers)
        memory = dict(memory)

        # special case for flags...
        if instruction.mnemonic.upper() in flags:
            for fl in flags[instruction.mnemonic.upper()]["tested"]:
                del registers[fl]
            for fl in flags[instruction.mnemonic.upper()]["defined"]:
                del registers[fl]

        # update registers
        for i in registers.keys():
            registers[i] = gdb.getR(i)

        # special case for flags...
        EFLAGS = gdb.getR("EFLAGS")
        if instruction.mnemonic.upper() in flags:
            for fl in flags[instruction.mnemonic.upper()]["defined"]:
                if "OF" in registers and instruction.insn_name().upper() in [
                    "ROL",
                    "RCL",
                    "ROR",
                    "RCR",
                ]:
                    print(instruction.insn_name().upper(), read_operand(instruction.operands[1]))
                    del registers["OF"]
                    continue
                registers[fl] = (EFLAGS & flags_maks[fl]) != 0

        # update memory
        for i in memory.keys():
            memory[i] = chr(gdb.getByte(i))

        test["pos"] = {}
        test["pos"]["memory"] = memory
        test["pos"]["registers"] = registers

        if "int" not in groups:
            print(test)

        count += 1

        # check if exit
        if instruction.insn_name().upper() in ["SYSCALL", "INT", "SYSENTER"]:
            if "The program has no registers now." in gdb.correspond("info registers \n"):
                print("done")
                break
    except Exception as e:
        if "The program has no registers now." in gdb.correspond("info registers\n"):
            break
        # print '-'*60
        # traceback.print_exc(file=sys.stdout)
        # print '-'*60
        # import pdb
        # pdb.set_trace()
        print("# Exception", e)
        if not stepped:
            gdb.stepi()

print(f"# Processed {count} instructions.")
