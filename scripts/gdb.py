import subprocess

count = 0

prompt = ""
subproc = None
_arch = None


def drain():
    str_buffer = ""
    while not str_buffer.endswith(prompt):
        c = subproc.stdout.read(1)
        str_buffer += c
    return str_buffer[: -len(prompt)]


def start(arch, argv, port=1234, _prompt="(gdb) "):
    global prompt, subproc
    prompt = _prompt
    gdb = "gdb-multiarch"
    try:
        subproc = subprocess.Popen(
            [gdb, argv[0]], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT
        )
    except OSError:
        msg = f"'{gdb}' binary not found in PATH (needed for tracing)"
        raise RuntimeError(msg)

    drain()
    # correspond(f'set architecture {arch}\n')
    correspond(f"file {argv[0]}\n")
    correspond(f"target remote :{port}\n")
    correspond("set pagination off\n")


def correspond(text):
    """Communicate with the child process without closing stdin."""
    subproc.stdin.write(text)
    subproc.stdin.flush()
    return drain()


def getInstruction():
    return correspond("x/i $pc\n").split("\n")[0]


def getR(reg):
    reg = "$" + reg
    if "XMM" in reg:
        reg = reg + ".uint128"
        val = correspond(f"p {reg.lower()}\n").split("=")[-1].split("\n")[0]
        if "0x" in val:
            return int(val.split("0x")[-1], 16)
        else:
            return int(val)
    if "FLAG" in reg:
        reg = "(unsigned) " + reg
    if reg in [f"$R{i}B" for i in range(16)]:
        reg = reg[:-1] + "&0xff"
    if reg in [f"$R{i}W" for i in range(16)]:
        reg = reg[:-1] + "&0xffff"
    val = correspond(f"p /x {reg.lower()}\n")
    val = val.split("0x")[-1]
    return int(val.split("\n")[0], 16)


def getCanonicalRegisters():
    reg_output = correspond("info reg\n")
    registers = {}
    for line in reg_output.split("\n"):
        line = line.strip()
        if not line:
            continue
        name, hex_val = line.split()[:2]
        if name != "cpsr":
            registers[name] = int(hex_val, 0)
        else:
            # We just want the NZCV flags
            registers[name] = int(hex_val, 0) & 0xF0000000
    return registers


def setR(reg, value):
    correspond(f"set ${reg.lower()} = {int(value)}\n")


def stepi():
    # print subproc.correspond("x/i $pc\n")
    correspond("stepi\n")


def getM(m):
    try:
        return int(correspond(f"x/xg {m}\n").strip().split("\t")[-1], 0)
    except Exception as e:
        raise e


def getPid():
    return int(correspond("info proc\n").split("\n")[0].split(" ")[-1])


def getStack():
    p = correspond("info proc\n").split("\n")[0].split(" ")[-1]
    with open(f"/proc/{p}/maps") as f:
        maps = f.read().split("\n")
    i, o = [int(x, 16) for x in maps[-3].split(" ")[0].split("-")]


def setByte(addr, val):
    cmdstr = f"set {{char}}{addr} = {ord(val)}"
    correspond(cmdstr + "\n")


def getByte(m):
    arch = get_arch()
    mask = {"i386": 0xFFFFFFFF, "armv7": 0xFFFFFFFF, "amd64": 0xFFFFFFFFFFFFFFFF}[arch]
    return int(correspond(f"x/1bx {m & mask}\n").split("\t")[-1].split("\n")[0][2:], 16)


def get_entry():
    a = correspond("info target\n")
    return int(a[a.find("Entry point:") :].split("\n")[0].split(" ")[-1][2:], 16)


def get_arch():
    global _arch
    if _arch is not None:
        return _arch
    infotarget = correspond("info target\n")
    if "elf32-i386" in infotarget:
        _arch = "i386"
    elif "elf64-x86-64" in infotarget:
        _arch = "amd64"
    elif "elf32-littlearm" in infotarget:
        _arch = "armv7"
    else:
        print(infotarget)
        raise NotImplementedError
    return _arch
