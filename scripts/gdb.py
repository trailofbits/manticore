from __future__ import print_function
import copy
import traceback
import os
import sys
import time
import subprocess

count = 0

prompt = ''
subproc = None
_arch = None

def drain():
    str_buffer = ''
    while not str_buffer.endswith(prompt):
        c = subproc.stdout.read(1)
        str_buffer += c
    return str_buffer[:-len(prompt)]

def start(arch, argv, port=1234,  _prompt='(gdb) '):
    global prompt, subproc
    prompt = _prompt
    gdb = 'gdb-multiarch'
    try:
        subproc = subprocess.Popen([gdb, argv[0]],
                                 stdin=subprocess.PIPE,
                                 stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT)
    except OSError:
        msg = "'{}' binary not found in PATH (needed for tracing)".format(gdb)
        raise RuntimeError(msg)

    drain()
    #correspond('set architecture {}\n'.format(arch))
    correspond('file {}\n'.format(argv[0]))
    correspond('target remote :{}\n'.format(port))
    correspond('set pagination off\n')

def correspond(text):
    """Communicate with the child process without closing stdin."""
    subproc.stdin.write(text)
    subproc.stdin.flush()
    return drain()

def getInstruction():
    return correspond('x/i $pc\n').split('\n')[0]

def getR(reg):
    reg = "$"+reg
    if "XMM" in reg:
        reg = reg+".uint128"
        val = correspond('p %s\n'%reg.lower()).split("=")[-1].split("\n")[0]
        if "0x" in val:
            return long(val.split("0x")[-1],16)
        else:
            return long(val)
    if "FLAG" in reg:
        reg = "(unsigned) "+reg
    if reg in ['$R%dB'%i for i in range(16)] :
        reg = reg[:-1] + "&0xff"
    if reg in ['$R%dW'%i for i in range(16)] :
        reg = reg[:-1] + "&0xffff"
    val = correspond('p /x %s\n'%reg.lower())
    val = val.split("0x")[-1]
    return long(val.split("\n")[0],16)

def getCanonicalRegisters():
    reg_output = correspond('info reg\n')
    registers = {}
    for line in reg_output.split("\n"):
        line = line.strip()
        if not line:
            continue
        name, hex_val = line.split()[:2]
        if name != 'cpsr':
            registers[name] = long(hex_val, 0)
        else:
            # We just want the NZCV flags
            registers[name] = int(hex_val, 0) & 0xF0000000
    return registers

def setR(reg, value):
    correspond('set $%s = %s\n'%(reg.lower(), long(value)))

def stepi():
    #print subproc.correspond("x/i $pc\n")
    correspond("stepi\n")
def getM(m):
    try:
        return long(correspond('x/xg %s\n'%m).strip().split('\t')[-1], 0)
    except Exception as e:
        raise e
        return 0
def getPid():
    return int(correspond('info proc\n').split("\n")[0].split(" ")[-1])
def getStack():
    maps = file("/proc/%s/maps"%correspond('info proc\n').split("\n")[0].split(" ")[-1]).read().split("\n")
    i,o = [ int(x,16) for x in maps[-3].split(" ")[0].split('-')]

def setByte(addr, val):
    cmdstr = 'set {{char}}{} = {}'.format(addr, ord(val))
    correspond(cmdstr + '\n')
def getByte(m):
    arch = get_arch()
    mask = {'i386':  0xffffffff,
            'armv7': 0xffffffff,
            'amd64': 0xffffffffffffffff}[arch]
    return int(correspond("x/1bx %d\n"%(m&mask)).split("\t")[-1].split("\n")[0][2:],16)
def get_entry():
    a=correspond('info target\n')
    return long(a[a.find("Entry point:"):].split('\n')[0].split(' ')[-1][2:],16)

def get_arch():
    global _arch
    if _arch is not None:
        return _arch
    infotarget = correspond('info target\n')
    if 'elf32-i386' in infotarget:
        _arch = 'i386'
    elif 'elf64-x86-64' in infotarget:
        _arch = 'amd64'
    elif 'elf32-littlearm' in infotarget:
        _arch = 'armv7'
    else:
        print(infotarget)
        raise NotImplemented
    return _arch
