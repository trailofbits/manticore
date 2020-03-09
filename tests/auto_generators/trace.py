from __future__ import print_function
import copy
import sys
import sys
import time
import subprocess
from distorm3 import Decompose, Decode16Bits, Decode32Bits, Decode64Bits, Mnemonics, Registers

count = 0


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
        return str_buffer

    def getR(self, reg):
        reg = "$" + reg
        if "XMM" in reg:
            reg = reg + ".uint128"
            val = self.correspond("p %s\n" % reg.lower()).split("=")[-1].split("\n")[0]
            if "0x" in val:
                return int(val.split("0x")[-1], 16)
            else:
                return int(val)
        if "FLAG" in reg:
            reg = "(unsigned) " + reg
        if reg in ["$R%dB" % i for i in range(16)]:
            reg = reg[:-1] + "&0xff"
        if reg in ["$R%dW" % i for i in range(16)]:
            reg = reg[:-1] + "&0xffff"
        val = self.correspond("p /x %s\n" % reg.lower()).split("0x")[-1]
        return long(val.split("\n")[0], 16)

    def setR(self, reg, value):
        self.correspond("set $%s = %s\n" % (reg.lower(), int(value)))

    def setByte(self, m, value):
        self.correspond("set *(char*)(%s) = %s\n" % (m, value))

    def stepi(self):
        # print self.correspond("x/i $pc\n")
        self.correspond("stepi\n")

    def getM(self, m):
        try:
            return long(
                self.correspond("x/xg %s\n" % m).split("\t")[-1].split("0x")[-1].split("\n")[0], 16
            )
        except Exception as e:
            print("x/xg %s\n" % m)
            print(self.correspond("x/xg %s\n" % m))
            raise e
            return 0

    def getPid(self):
        return int(self.correspond("info proc\n").split("\n")[0].split(" ")[-1])

    def getStack(self):
        maps = (
            file("/proc/%s/maps" % self.correspond("info proc\n").split("\n")[0].split(" ")[-1])
            .read()
            .split("\n")
        )
        i, o = [int(x, 16) for x in maps[-3].split(" ")[0].split("-")]
        print(self.correspond("dump mem lala 0x%x 0x%x\n" % (i, o)))

    def getByte(self, m):
        arch = self.get_arch()
        mask = {"i386": 0xFFFFFFFF, "amd64": 0xFFFFFFFFFFFFFFFF}[arch]
        return int(
            self.correspond("x/1bx %d\n" % (m & mask)).split("\t")[-1].split("\n")[0][2:], 16
        )

    def get_entry(self):
        a = self.correspond("info target\n")
        return int(a[a.find("Entry point:") :].split("\n")[0].split(" ")[-1][2:], 16)

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
arch = gdb.correspond("")

# guess arch
arch = gdb.get_arch()

# guess architecture from file
entry = gdb.get_entry()
gdb.correspond("b *0\n")
gdb.correspond("run arg1 arg2 arg3 < /dev/urandom > /dev/null\n")
gdb.correspond("d 1\n")

# Simulate no vdso (As when analyzed with symbemu)
found = 0
for i in range(75, 120):
    if gdb.getM("$sp+sizeof(void*)*%d" % i) == 0x19 and gdb.getM("$sp+%d" % (i + 2)) == 0x1F:
        found = i
if found != 0:
    gdb.setByte("$sp+sizeof(void*)*%d" % found, 1)
    gdb.setByte("$sp+sizeof(void*)*%d" % (found + 2), 1)

vdso = gdb.getM("$sp+sizeof(void*)*%d" % (found + 1))
for i in range(75, 120):
    val = gdb.getM("$sp+sizeof(void*)*%d" % i)
    if val > vdso - 0x10000 and val <= vdso + 0x10000:
        if (gdb.getM("$sp+sizeof(void*)*%d" % (i - 1))) != 1:
            gdb.setByte("$sp+sizeof(void*)*%d" % (i - 1), 1)

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
        print(hex(pc))
        gdb.stepi()
        print(gdb.correspond("info registers\n"))
    except Exception as e:
        print(e)
print("# Processed %d instructions." % count)
