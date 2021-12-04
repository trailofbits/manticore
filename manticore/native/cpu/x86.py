import collections
import logging

from functools import wraps

import capstone as cs

from .abstractcpu import (
    Abi,
    SyscallAbi,
    Cpu,
    CpuException,
    RegisterFile,
    Operand,
    instruction,
    ConcretizeRegister,
    Interruption,
    Syscall,
    DivideByZeroError,
)


from ...core.smtlib import Operators, BitVec, Bool, BitVecConstant, operator, visitors, issymbolic
from ..memory import Memory, ConcretizeMemory
from functools import reduce

from typing import Any, Dict

logger = logging.getLogger(__name__)

OP_NAME_MAP = {
    "JNE": "JNZ",
    "JE": "JZ",
    "CMOVE": "CMOVZ",
    "CMOVNE": "CMOVNZ",
    "MOVUPS": "MOV",
    "MOVABS": "MOV",
    "MOVSB": "MOVS",
    "MOVSW": "MOVS",
    "MOVSQ": "MOVS",
    "SETNE": "SETNZ",
    "SETE": "SETZ",
    "LODSB": "LODS",
    "LODSW": "LODS",
    "LODSD": "LODS",
    "LODSQ": "LODS",
    "STOSB": "STOS",
    "STOSW": "STOS",
    "STOSD": "STOS",
    "STOSQ": "STOS",
    "SCASB": "SCAS",
    "SCASW": "SCAS",
    "SCASD": "SCAS",
    "SCASQ": "SCAS",
    "CMPSB": "CMPS",
    "CMPSW": "CMPS",
    "CMPSD": "CMPS",
    "VMOVSD": "MOVSD",
    "FUCOMPI": "FUCOMIP",
}


###############################################################################
# Auxiliary decorators...
def rep(old_method):
    # This decorates REP instructions (STOS, LODS, MOVS, INS, OUTS)
    @wraps(old_method)
    def new_method(cpu, *args, **kw_args):
        prefix = cpu.instruction.prefix
        if cs.x86.X86_PREFIX_REP in prefix:
            counter_name = {16: "CX", 32: "ECX", 64: "RCX"}[cpu.instruction.addr_size * 8]
            count = cpu.read_register(counter_name)
            if issymbolic(count):
                raise ConcretizeRegister(
                    cpu,
                    counter_name,
                    f"Concretizing {counter_name} on REP instruction",
                    policy="SAMPLED",
                )

            FLAG = count != 0

            # Repeat!
            if FLAG:
                old_method(cpu, *args, **kw_args)
                count = cpu.write_register(counter_name, count - 1)
                FLAG = count != 0  # true FLAG means loop

            if not FLAG:
                cpu.PC += cpu.instruction.size

        else:
            cpu.PC += cpu.instruction.size
            old_method(cpu, *args, **kw_args)

    return new_method


def repe(old_method):
    # This decorates REPE enabled instructions (SCAS, CMPS)
    @wraps(old_method)
    def new_method(cpu, *args, **kw_args):
        prefix = cpu.instruction.prefix
        if (cs.x86.X86_PREFIX_REP in prefix) or (cs.x86.X86_PREFIX_REPNE in prefix):
            counter_name = {16: "CX", 32: "ECX", 64: "RCX"}[cpu.instruction.addr_size * 8]
            count = cpu.read_register(counter_name)
            if issymbolic(count):
                raise ConcretizeRegister(
                    cpu,
                    counter_name,
                    f"Concretizing {counter_name} on REP instruction",
                    policy="SAMPLED",
                )

            FLAG = count != 0

            # Repeat!
            if FLAG:
                old_method(cpu, *args, **kw_args)
                count = cpu.write_register(counter_name, count - 1)

                # REPE
                if cs.x86.X86_PREFIX_REP in prefix:
                    FLAG = Operators.AND(cpu.ZF == True, count != 0)  # true FLAG means loop
                # REPNE
                elif cs.x86.X86_PREFIX_REPNE in prefix:
                    FLAG = Operators.AND(cpu.ZF == False, count != 0)  # true FLAG means loop

            # if issymbolic(FLAG):
            #    raise ConcretizeRegister(cpu, 'ZF', "Concretizing ZF on REP instruction", policy='ALL')

            # if not FLAG:
            cpu.PC += Operators.ITEBV(cpu.address_bit_size, FLAG, 0, cpu.instruction.size)

        else:
            cpu.PC += cpu.instruction.size
            old_method(cpu, *args, **kw_args)

    return new_method


###############################################################################
# register/flag descriptors


class AMD64RegFile(RegisterFile):
    Regspec = collections.namedtuple("Regspec", "register_id ty offset size reset")
    _flags = {"CF": 0, "PF": 2, "AF": 4, "ZF": 6, "SF": 7, "IF": 9, "DF": 10, "OF": 11}
    _table = {
        "CS": Regspec("CS", int, 0, 16, False),
        "DS": Regspec("DS", int, 0, 16, False),
        "ES": Regspec("ES", int, 0, 16, False),
        "SS": Regspec("SS", int, 0, 16, False),
        "FS": Regspec("FS", int, 0, 16, False),
        "GS": Regspec("GS", int, 0, 16, False),
        "RAX": Regspec("RAX", int, 0, 64, True),
        "RBX": Regspec("RBX", int, 0, 64, True),
        "RCX": Regspec("RCX", int, 0, 64, True),
        "RDX": Regspec("RDX", int, 0, 64, True),
        "RSI": Regspec("RSI", int, 0, 64, True),
        "RDI": Regspec("RDI", int, 0, 64, True),
        "RSP": Regspec("RSP", int, 0, 64, True),
        "RBP": Regspec("RBP", int, 0, 64, True),
        "RIP": Regspec("RIP", int, 0, 64, True),
        "R8": Regspec("R8", int, 0, 64, True),
        "R9": Regspec("R9", int, 0, 64, True),
        "R10": Regspec("R10", int, 0, 64, True),
        "R11": Regspec("R11", int, 0, 64, True),
        "R12": Regspec("R12", int, 0, 64, True),
        "R13": Regspec("R13", int, 0, 64, True),
        "R14": Regspec("R14", int, 0, 64, True),
        "R15": Regspec("R15", int, 0, 64, True),
        "EAX": Regspec("RAX", int, 0, 32, True),
        "EBX": Regspec("RBX", int, 0, 32, True),
        "ECX": Regspec("RCX", int, 0, 32, True),
        "EDX": Regspec("RDX", int, 0, 32, True),
        "ESI": Regspec("RSI", int, 0, 32, True),
        "EDI": Regspec("RDI", int, 0, 32, True),
        "ESP": Regspec("RSP", int, 0, 32, True),
        "EBP": Regspec("RBP", int, 0, 32, True),
        "EIP": Regspec("RIP", int, 0, 32, True),
        "R8D": Regspec("R8", int, 0, 32, True),
        "R9D": Regspec("R9", int, 0, 32, True),
        "R10D": Regspec("R10", int, 0, 32, True),
        "R11D": Regspec("R11", int, 0, 32, True),
        "R12D": Regspec("R12", int, 0, 32, True),
        "R13D": Regspec("R13", int, 0, 32, True),
        "R14D": Regspec("R14", int, 0, 32, True),
        "R15D": Regspec("R15", int, 0, 32, True),
        "AX": Regspec("RAX", int, 0, 16, False),
        "BX": Regspec("RBX", int, 0, 16, False),
        "CX": Regspec("RCX", int, 0, 16, False),
        "DX": Regspec("RDX", int, 0, 16, False),
        "SI": Regspec("RSI", int, 0, 16, False),
        "DI": Regspec("RDI", int, 0, 16, False),
        "SP": Regspec("RSP", int, 0, 16, False),
        "BP": Regspec("RBP", int, 0, 16, False),
        "IP": Regspec("RIP", int, 0, 16, False),
        "R8W": Regspec("R8", int, 0, 16, False),
        "R9W": Regspec("R9", int, 0, 16, False),
        "R10W": Regspec("R10", int, 0, 16, False),
        "R11W": Regspec("R11", int, 0, 16, False),
        "R12W": Regspec("R12", int, 0, 16, False),
        "R13W": Regspec("R13", int, 0, 16, False),
        "R14W": Regspec("R14", int, 0, 16, False),
        "R15W": Regspec("R15", int, 0, 16, False),
        "AL": Regspec("RAX", int, 0, 8, False),
        "BL": Regspec("RBX", int, 0, 8, False),
        "CL": Regspec("RCX", int, 0, 8, False),
        "DL": Regspec("RDX", int, 0, 8, False),
        "SIL": Regspec("RSI", int, 0, 8, False),
        "DIL": Regspec("RDI", int, 0, 8, False),
        "SPL": Regspec("RSP", int, 0, 8, False),
        "BPL": Regspec("RBP", int, 0, 8, False),
        "R8B": Regspec("R8", int, 0, 8, False),
        "R9B": Regspec("R9", int, 0, 8, False),
        "R10B": Regspec("R10", int, 0, 8, False),
        "R11B": Regspec("R11", int, 0, 8, False),
        "R12B": Regspec("R12", int, 0, 8, False),
        "R13B": Regspec("R13", int, 0, 8, False),
        "R14B": Regspec("R14", int, 0, 8, False),
        "R15B": Regspec("R15", int, 0, 8, False),
        "AH": Regspec("RAX", int, 8, 8, False),
        "BH": Regspec("RBX", int, 8, 8, False),
        "CH": Regspec("RCX", int, 8, 8, False),
        "DH": Regspec("RDX", int, 8, 8, False),
        "SIH": Regspec("RSI", int, 8, 8, False),
        "DIH": Regspec("RDI", int, 8, 8, False),
        "SPH": Regspec("RSP", int, 8, 8, False),
        "BPH": Regspec("RBP", int, 8, 8, False),
        "R8H": Regspec("R8", int, 8, 8, False),
        "R9H": Regspec("R9", int, 8, 8, False),
        "R10H": Regspec("R10", int, 8, 8, False),
        "R11H": Regspec("R11", int, 8, 8, False),
        "R12H": Regspec("R12", int, 8, 8, False),
        "R13H": Regspec("R13", int, 8, 8, False),
        "R14H": Regspec("R14", int, 8, 8, False),
        "R15H": Regspec("R15", int, 8, 8, False),
        "FP0": Regspec("FP0", float, 0, 80, False),
        "FP1": Regspec("FP1", float, 0, 80, False),
        "FP2": Regspec("FP2", float, 0, 80, False),
        "FP3": Regspec("FP3", float, 0, 80, False),
        "FP4": Regspec("FP4", float, 0, 80, False),
        "FP5": Regspec("FP5", float, 0, 80, False),
        "FP6": Regspec("FP6", float, 0, 80, False),
        "FP7": Regspec("FP7", float, 0, 80, False),
        "FPSW": Regspec("FPSW", int, 0, 16, False),
        "TOP": Regspec("FPSW", int, 11, 3, False),
        "FPTAG": Regspec("FPTAG", int, 0, 16, False),
        "FPCW": Regspec("FPCW", int, 0, 16, False),
        "CF": Regspec("CF", bool, 0, 1, False),
        "PF": Regspec("PF", bool, 0, 1, False),
        "AF": Regspec("AF", bool, 0, 1, False),
        "ZF": Regspec("ZF", bool, 0, 1, False),
        "SF": Regspec("SF", bool, 0, 1, False),
        "IF": Regspec("IF", bool, 0, 1, False),
        "DF": Regspec("DF", bool, 0, 1, False),
        "OF": Regspec("OF", bool, 0, 1, False),
        "YMM0": Regspec("YMM0", int, 0, 256, False),
        "YMM1": Regspec("YMM1", int, 0, 256, False),
        "YMM2": Regspec("YMM2", int, 0, 256, False),
        "YMM3": Regspec("YMM3", int, 0, 256, False),
        "YMM4": Regspec("YMM4", int, 0, 256, False),
        "YMM5": Regspec("YMM5", int, 0, 256, False),
        "YMM6": Regspec("YMM6", int, 0, 256, False),
        "YMM7": Regspec("YMM7", int, 0, 256, False),
        "YMM8": Regspec("YMM8", int, 0, 256, False),
        "YMM9": Regspec("YMM9", int, 0, 256, False),
        "YMM10": Regspec("YMM10", int, 0, 256, False),
        "YMM11": Regspec("YMM11", int, 0, 256, False),
        "YMM12": Regspec("YMM12", int, 0, 256, False),
        "YMM13": Regspec("YMM13", int, 0, 256, False),
        "YMM14": Regspec("YMM14", int, 0, 256, False),
        "YMM15": Regspec("YMM15", int, 0, 256, False),
        "XMM0": Regspec("YMM0", int, 0, 128, False),
        "XMM1": Regspec("YMM1", int, 0, 128, False),
        "XMM2": Regspec("YMM2", int, 0, 128, False),
        "XMM3": Regspec("YMM3", int, 0, 128, False),
        "XMM4": Regspec("YMM4", int, 0, 128, False),
        "XMM5": Regspec("YMM5", int, 0, 128, False),
        "XMM6": Regspec("YMM6", int, 0, 128, False),
        "XMM7": Regspec("YMM7", int, 0, 128, False),
        "XMM8": Regspec("YMM8", int, 0, 128, False),
        "XMM9": Regspec("YMM9", int, 0, 128, False),
        "XMM10": Regspec("YMM10", int, 0, 128, False),
        "XMM11": Regspec("YMM11", int, 0, 128, False),
        "XMM12": Regspec("YMM12", int, 0, 128, False),
        "XMM13": Regspec("YMM13", int, 0, 128, False),
        "XMM14": Regspec("YMM14", int, 0, 128, False),
        "XMM15": Regspec("YMM15", int, 0, 128, False),
    }

    # this should be calculated on __import__ using _table
    _affects = {
        "RIP": ("EIP", "IP"),
        "EIP": ("IP", "RIP"),
        "IP": ("EIP", "RIP"),
        "RAX": ("AH", "AL", "AX", "EAX"),
        "EAX": ("AH", "AL", "AX", "RAX"),
        "AX": ("AH", "AL", "EAX", "RAX"),
        "AH": ("AX", "EAX", "RAX"),
        "AL": ("AX", "EAX", "RAX"),
        "RBX": ("BH", "BL", "BX", "EBX"),
        "EBX": ("BH", "BL", "BX", "RBX"),
        "BX": ("BH", "BL", "EBX", "RBX"),
        "BH": ("BX", "EBX", "RBX"),
        "BL": ("BX", "EBX", "RBX"),
        "RCX": ("CH", "CL", "CX", "ECX"),
        "ECX": ("CH", "CL", "CX", "RCX"),
        "CX": ("CH", "CL", "ECX", "RCX"),
        "CH": ("CX", "ECX", "RCX"),
        "CL": ("CX", "ECX", "RCX"),
        "RDX": ("DH", "DL", "DX", "EDX"),
        "EDX": ("DH", "DL", "DX", "RDX"),
        "DX": ("DH", "DL", "EDX", "RDX"),
        "DH": ("DX", "EDX", "RDX"),
        "DL": ("DX", "EDX", "RDX"),
        "RSI": ("ESI", "SI", "SIH", "SIL"),
        "ESI": ("RSI", "SI", "SIH", "SIL"),
        "SI": ("ESI", "RSI", "SIH", "SIL"),
        "SIH": ("ESI", "RSI", "SI"),
        "SIL": ("ESI", "RSI", "SI"),
        "RDI": ("DI", "DIH", "DIL", "EDI"),
        "EDI": ("DI", "DIH", "DIL", "RDI"),
        "DI": ("DIH", "DIL", "EDI", "RDI"),
        "DIH": ("DI", "EDI", "RDI"),
        "DIL": ("DI", "EDI", "RDI"),
        "RSP": ("ESP", "SP", "SPH", "SPL"),
        "ESP": ("RSP", "SP", "SPH", "SPL"),
        "SP": ("ESP", "RSP", "SPH", "SPL"),
        "SPH": ("ESP", "RSP", "SP"),
        "SPL": ("ESP", "RSP", "SP"),
        "RBP": ("BP", "BPH", "BPL", "EBP"),
        "EBP": ("BP", "BPH", "BPL", "RBP"),
        "BP": ("BPH", "BPL", "EBP", "RBP"),
        "BPH": ("BP", "EBP", "RBP"),
        "BPL": ("BP", "EBP", "RBP"),
        "CS": (),
        "DS": (),
        "ES": (),
        "FS": (),
        "GS": (),
        "SS": (),
        "RFLAGS": ("EFLAGS", "AF", "CF", "DF", "IF", "OF", "PF", "SF", "ZF"),
        "EFLAGS": ("RFLAGS", "AF", "CF", "DF", "IF", "OF", "PF", "SF", "ZF"),
        "AF": ("RFLAGS", "EFLAGS"),
        "CF": ("RFLAGS", "EFLAGS"),
        "DF": ("RFLAGS", "EFLAGS"),
        "IF": ("RFLAGS", "EFLAGS"),
        "OF": ("RFLAGS", "EFLAGS"),
        "PF": ("RFLAGS", "EFLAGS"),
        "SF": ("RFLAGS", "EFLAGS"),
        "ZF": ("RFLAGS", "EFLAGS"),
        "FPSW": ("TOP",),
        "TOP": ("FPSW",),
        "FPCW": (),
        "FPTAG": (),
        "FP0": (),
        "FP1": (),
        "FP2": (),
        "FP3": (),
        "FP4": (),
        "FP5": (),
        "FP6": (),
        "FP7": (),
        "R10": ("R10B", "R10D", "R10H", "R10W"),
        "R10B": ("R10", "R10D", "R10W"),
        "R10D": ("R10", "R10B", "R10H", "R10W"),
        "R10H": ("R10", "R10D", "R10W"),
        "R10W": ("R10", "R10B", "R10D", "R10H"),
        "R11": ("R11B", "R11D", "R11H", "R11W"),
        "R11B": ("R11", "R11D", "R11W"),
        "R11D": ("R11", "R11B", "R11H", "R11W"),
        "R11H": ("R11", "R11D", "R11W"),
        "R11W": ("R11", "R11B", "R11D", "R11H"),
        "R12": ("R12B", "R12D", "R12H", "R12W"),
        "R12B": ("R12", "R12D", "R12W"),
        "R12D": ("R12", "R12B", "R12H", "R12W"),
        "R12H": ("R12", "R12D", "R12W"),
        "R12W": ("R12", "R12B", "R12D", "R12H"),
        "R13": ("R13B", "R13D", "R13H", "R13W"),
        "R13B": ("R13", "R13D", "R13W"),
        "R13D": ("R13", "R13B", "R13H", "R13W"),
        "R13H": ("R13", "R13D", "R13W"),
        "R13W": ("R13", "R13B", "R13D", "R13H"),
        "R14": ("R14B", "R14D", "R14H", "R14W"),
        "R14B": ("R14", "R14D", "R14W"),
        "R14D": ("R14", "R14B", "R14H", "R14W"),
        "R14H": ("R14", "R14D", "R14W"),
        "R14W": ("R14", "R14B", "R14D", "R14H"),
        "R15": ("R15B", "R15D", "R15H", "R15W"),
        "R15B": ("R15", "R15D", "R15W"),
        "R15D": ("R15", "R15B", "R15H", "R15W"),
        "R15H": ("R15", "R15D", "R15W"),
        "R15W": ("R15", "R15B", "R15D", "R15H"),
        "R8": ("R8B", "R8D", "R8H", "R8W"),
        "R8B": ("R8", "R8D", "R8W"),
        "R8D": ("R8", "R8B", "R8H", "R8W"),
        "R8H": ("R8", "R8D", "R8W"),
        "R8W": ("R8", "R8B", "R8D", "R8H"),
        "R9": ("R9B", "R9D", "R9H", "R9W"),
        "R9B": ("R9", "R9D", "R9W"),
        "R9D": ("R9", "R9B", "R9H", "R9W"),
        "R9H": ("R9", "R9D", "R9W"),
        "R9W": ("R9", "R9B", "R9D", "R9H"),
        "XMM0": ("YMM0",),
        "XMM1": ("YMM1",),
        "XMM10": ("YMM10",),
        "XMM11": ("YMM11",),
        "XMM12": ("YMM12",),
        "XMM13": ("YMM13",),
        "XMM14": ("YMM14",),
        "XMM15": ("YMM15",),
        "XMM2": ("YMM2",),
        "XMM3": ("YMM3",),
        "XMM4": ("YMM4",),
        "XMM5": ("YMM5",),
        "XMM6": ("YMM6",),
        "XMM7": ("YMM7",),
        "XMM8": ("YMM8",),
        "XMM9": ("YMM9",),
        "YMM0": ("XMM0",),
        "YMM1": ("XMM1",),
        "YMM10": ("XMM10",),
        "YMM11": ("XMM11",),
        "YMM12": ("XMM12",),
        "YMM13": ("XMM13",),
        "YMM14": ("XMM14",),
        "YMM15": ("XMM15",),
        "YMM2": ("XMM2",),
        "YMM3": ("XMM3",),
        "YMM4": ("XMM4",),
        "YMM5": ("XMM5",),
        "YMM6": ("XMM6",),
        "YMM7": ("XMM7",),
        "YMM8": ("XMM8",),
        "YMM9": ("XMM9",),
    }
    _canonical_registers = (
        "RAX",
        "RCX",
        "RDX",
        "RBX",
        "RSP",
        "RBP",
        "RSI",
        "RDI",
        "R8",
        "R9",
        "R10",
        "R11",
        "R12",
        "R13",
        "R14",
        "R15",
        "RIP",
        "YMM0",
        "YMM1",
        "YMM2",
        "YMM3",
        "YMM4",
        "YMM5",
        "YMM6",
        "YMM7",
        "YMM8",
        "YMM9",
        "YMM10",
        "YMM11",
        "YMM12",
        "YMM13",
        "YMM14",
        "YMM15",
        "CS",
        "DS",
        "ES",
        "SS",
        "FS",
        "GS",
        "AF",
        "CF",
        "DF",
        "IF",
        "OF",
        "PF",
        "SF",
        "ZF",
        "FP0",
        "FP1",
        "FP2",
        "FP3",
        "FP4",
        "FP5",
        "FP6",
        "FP7",
        "FPSW",
        "FPCW",
        "FPTAG",
    )

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

        for reg in (
            "RAX",
            "RCX",
            "RDX",
            "RBX",
            "RSP",
            "RBP",
            "RSI",
            "RDI",
            "R8",
            "R9",
            "R10",
            "R11",
            "R12",
            "R13",
            "R14",
            "R15",
            "RIP",
            "YMM0",
            "YMM1",
            "YMM2",
            "YMM3",
            "YMM4",
            "YMM5",
            "YMM6",
            "YMM7",
            "YMM8",
            "YMM9",
            "YMM10",
            "YMM11",
            "YMM12",
            "YMM13",
            "YMM14",
            "YMM15",
            "CS",
            "DS",
            "ES",
            "SS",
            "FS",
            "GS",
            "AF",
            "CF",
            "DF",
            "IF",
            "OF",
            "PF",
            "SF",
            "ZF",
        ):
            self._registers[reg] = 0

        for reg in ("FP0", "FP1", "FP2", "FP3", "FP4", "FP5", "FP6", "FP7"):
            self._registers[reg] = (0, 0)

        for reg in ("FPSW", "FPTAG", "FPCW"):
            self._registers[reg] = 0

        self._cache = {}

        for name in ("AF", "CF", "DF", "IF", "OF", "PF", "SF", "ZF"):
            self.write(name, False)

        self._all_registers = (
            set(self._table.keys())
            | set(["FP0", "FP1", "FP2", "FP3", "FP4", "FP5", "FP6", "FP7", "EFLAGS", "RFLAGS"])
            | set(self._aliases.keys())
        )

    @property
    def all_registers(self):
        return self._all_registers

    @property
    def canonical_registers(self):
        return self._canonical_registers

    def __contains__(self, register):
        return register in self._all_registers

    def _set_bv(self, register_id, register_size, offset, size, reset, value):
        if isinstance(value, int):
            # type error or forgiving?
            # if (value & ~((1<<size)-1)) != 0 :
            #    raise TypeError('Value bigger than register')
            value &= (1 << size) - 1
        elif not isinstance(value, BitVec) or value.size != size:
            raise TypeError
        if not reset:
            if register_size == size:
                new_value = 0
            elif offset == 0:
                new_value = self._registers[register_id] & (~((1 << size) - 1))
            else:
                new_value = self._registers[register_id] & (~(((1 << size) - 1) << offset))
        else:
            new_value = 0
        new_value |= Operators.ZEXTEND(value, register_size) << offset
        self._registers[register_id] = new_value
        return value

    def _get_bv(self, register_id, register_size, offset, size):
        if register_size == size:
            value = self._registers[register_id]
        else:
            value = Operators.EXTRACT(self._registers[register_id], offset, size)
        return value

    def _set_flag(self, register_id, register_size, offset, size, reset, value):
        assert size == 1
        if not isinstance(value, (bool, int, BitVec, Bool)):
            raise TypeError
        if isinstance(value, BitVec):
            if value.size != 1:
                raise TypeError
        if not isinstance(value, (bool, Bool)):
            value = value != 0
        self._registers[register_id] = value
        return value

    def _get_flag(self, register_id, register_size, offset, size):
        assert size == 1
        return self._registers[register_id]

    def _set_float(self, register_id, register_size, offset, size, reset, value):
        assert size == 80
        assert offset == 0
        if not isinstance(value, tuple):  # Add decimal here?
            raise TypeError
        self._registers[register_id] = value
        return value

    def _get_float(self, register_id, register_size, offset, size):
        assert size == 80
        assert offset == 0
        return self._registers[register_id]

    def _get_flags(self, reg):
        """ Build EFLAGS/RFLAGS from flags """

        def make_symbolic(flag_expr):
            register_size = 32 if reg == "EFLAGS" else 64
            value, offset = flag_expr
            return Operators.ITEBV(
                register_size,
                value,
                BitVecConstant(size=register_size, value=1 << offset),
                BitVecConstant(size=register_size, value=0),
            )

        flags = []
        for flag, offset in self._flags.items():
            flags.append((self._registers[flag], offset))

        if any(issymbolic(flag) for flag, offset in flags):
            res = reduce(operator.or_, map(make_symbolic, flags))
        else:
            res = 0
            for flag, offset in flags:
                res += flag << offset
        return res

    def _set_flags(self, reg, res):
        """ Set individual flags from a EFLAGS/RFLAGS value """
        # assert sizeof (res) == 32 if reg == 'EFLAGS' else 64
        for flag, offset in self._flags.items():
            self.write(flag, Operators.EXTRACT(res, offset, 1))

    def write(self, name, value):
        name = self._alias(name)
        if name in ("ST0", "ST1", "ST2", "ST3", "ST4", "ST5", "ST6", "ST7"):
            name = f'FP{((self.read("TOP") + int(name[2])) & 7)}'

        # Special EFLAGS/RFLAGS case
        if "FLAGS" in name:
            self._set_flags(name, value)
            self._update_cache(name, value)
            return value

        register_id, ty, offset, size, reset = self._table[name]
        if register_id != name:
            # FIXME add a column to _table with parent_size so we don't need to access the dict twice
            register_size = self._table[register_id].size
        else:
            register_size = size
        assert register_size >= offset + size
        typed_setter = {int: self._set_bv, bool: self._set_flag, float: self._set_float}[ty]
        value = typed_setter(register_id, register_size, offset, size, reset, value)
        self._update_cache(name, value)
        return value

    def _update_cache(self, name, value):
        self._cache[name] = value
        for affected in self._affects[name]:
            assert affected != name
            self._cache.pop(affected, None)

    def read(self, name):
        name = str(self._alias(name))
        if name in ("ST0", "ST1", "ST2", "ST3", "ST4", "ST5", "ST6", "ST7"):
            name = f'FP{((self.read("TOP") + int(name[2])) & 7)}'
        if name in self._cache:
            return self._cache[name]
        if "FLAGS" in name:
            value = self._get_flags(name)
            self._cache[name] = value
            return value
        register_id, ty, offset, size, reset = self._table[name]
        if register_id != name:
            register_size = self._table[register_id].size
        else:
            register_size = size
        assert register_size >= offset + size
        typed_getter = {int: self._get_bv, bool: self._get_flag, float: self._get_float}[ty]
        value = typed_getter(register_id, register_size, offset, size)
        self._cache[name] = value
        return value

    def sizeof(self, reg):
        return self._table[reg].size

    def __copy__(self):
        cls = self.__class__
        result = cls.__new__(cls)
        result.__dict__.update(self.__dict__)
        result._cache = self._cache.copy()
        result._registers = self._registers.copy()
        return result


# Operand Wrapper
class AMD64Operand(Operand):
    """ This class deals with capstone X86 operands """

    def __init__(self, cpu: Cpu, op):
        super().__init__(cpu, op)

    @property
    def type(self):
        type_map = {
            cs.x86.X86_OP_REG: "register",
            cs.x86.X86_OP_MEM: "memory",
            cs.x86.X86_OP_IMM: "immediate",
        }

        return type_map[self.op.type]

    # Operand access
    def address(self):
        cpu, o = self.cpu, self.op
        address = 0
        if self.mem.segment is not None:
            seg = self.mem.segment
            base, size, ty = cpu.get_descriptor(cpu.read_register(seg))
            address += base  # todo check limits and perms
        else:
            # FIXME inspect operand or cpu.instruction and decide
            # the correct default segment for instruction
            seg = "DS"
            if self.mem.base is not None and self.mem.base in ["SP", "ESP", "EBP"]:
                seg = "SS"
            base, size, ty = cpu.get_descriptor(cpu.read_register(seg))
            address += base  # todo check limits and perms
        if self.mem.base is not None:
            base = self.mem.base
            address += cpu.read_register(base)
        if self.mem.index is not None:
            index = self.mem.index
            address += self.mem.scale * cpu.read_register(index)

        address += self.mem.disp

        return address & ((1 << cpu.address_bit_size) - 1)

    def read(self):
        cpu, o = self.cpu, self.op
        if self.type == "register":
            value = cpu.read_register(self.reg)
            # logger.info("Read from reg %s value: %x",self.reg, value)
            return value
        elif self.type == "immediate":
            # logger.info("Read from immediate value: %x", o.imm)
            return o.imm
        elif self.type == "memory":
            value = cpu.read_int(self.address(), self.size)
            # logger.info("read mem operand from %x value: %x",self.address(), value)
            return value
        else:
            raise NotImplementedError("read_operand unknown type", o.type)

    def write(self, value):
        cpu, o = self.cpu, self.op
        if self.type == "register":
            # logger.info("Write to reg %s value: %x",self.reg, value)
            cpu.write_register(self.reg, value)
        elif self.type == "memory":
            # logger.info("write mem operand to %x value: %x",self.address(), value)
            cpu.write_int(self.address(), value, self.size)
        else:
            raise NotImplementedError("write_operand unknown type", o.type)
        return value & ((1 << self.size) - 1)

    @property
    def size(self):
        return self.op.size * 8

    def __getattr__(self, name):
        return getattr(self.op, name)


class X86Cpu(Cpu):
    """
    A CPU model.
    """

    def __init__(self, regfile: RegisterFile, memory: Memory, *args, **kwargs):
        """
        Builds a CPU model.
        :param regfile: regfile object for this CPU.
        :param memory: memory object for this CPU.
        """
        super().__init__(regfile, memory, *args, **kwargs)
        # Segments ('base', 'limit', 'perms', 'gatetype')
        self._segments: Dict[str, Any] = {}

    def __getstate__(self):
        state = super().__getstate__()
        state["segments"] = self._segments
        return state

    def __setstate__(self, state):
        self._segments = state["segments"]
        super().__setstate__(state)

    # Segments
    def set_descriptor(self, selector, base, limit, perms):
        assert selector >= 0 and selector < 0xFFFF
        assert base >= 0 and base < (1 << self.address_bit_size)
        assert limit >= 0 and limit < 0xFFFF or limit & 0xFFF == 0
        # perms ? not used yet Also is not really perms but rather a bunch of attributes
        self._publish("will_set_descriptor", selector, base, limit, perms)
        self._segments[selector] = (base, limit, perms)
        self._publish("did_set_descriptor", selector, base, limit, perms)

    def get_descriptor(self, selector):
        return self._segments.setdefault(selector, (0, 0xFFFFF000, "rwx"))

    def _wrap_operands(self, operands):
        return [AMD64Operand(self, op) for op in operands]

    # Auxiliary stack access
    def push(cpu, value, size):
        """
        Writes a value in the stack.

        :param value: the value to put in the stack.
        :param size: the size of the value.
        """
        assert size in (8, 16, cpu.address_bit_size)
        cpu.STACK = cpu.STACK - size // 8
        base, _, _ = cpu.get_descriptor(cpu.read_register("SS"))
        address = cpu.STACK + base
        cpu.write_int(address, value, size)

    def pop(cpu, size):
        """
        Gets a value from the stack.

        :rtype: int
        :param size: the size of the value to consume from the stack.
        :return: the value from the stack.
        """
        assert size in (16, cpu.address_bit_size)
        base, _, _ = cpu.get_descriptor(cpu.SS)
        address = cpu.STACK + base
        value = cpu.read_int(address, size)
        cpu.STACK = cpu.STACK + size // 8
        return value

    ################################################
    # This its unused but shouldn't be deleted!!!
    # The instruction cache must be invalidated after an executable
    # page was changed or removed or added
    def invalidate_cache(cpu, address, size):
        """ remove decoded instruction from instruction cache """
        cache = cpu.instruction_cache
        for offset in range(size):
            if address + offset in cache:
                del cache[address + offset]

    def canonicalize_instruction_name(self, instruction):
        # MOVSD
        if instruction.opcode[0] in (0xA4, 0xA5):
            name = "MOVS"
        else:
            name = instruction.insn_name().upper()
        # Check if we already have an implementation...
        name = OP_NAME_MAP.get(name, name)
        return name

    #
    # Instruction Implementations
    #

    def _calculate_CMP_flags(self, size, res, arg0, arg1):
        SIGN_MASK = 1 << (size - 1)
        self.CF = Operators.ULT(arg0, arg1)
        self.AF = ((arg0 ^ arg1) ^ res) & 0x10 != 0
        self.ZF = res == 0
        self.SF = (res & SIGN_MASK) != 0
        sign0 = (arg0 & SIGN_MASK) == SIGN_MASK
        sign1 = (arg1 & SIGN_MASK) == SIGN_MASK
        signr = (res & SIGN_MASK) == SIGN_MASK
        self.OF = Operators.AND(sign0 ^ sign1, sign0 ^ signr)
        self.PF = self._calculate_parity_flag(res)

    def _calculate_parity_flag(self, res):
        return (
            res ^ res >> 1 ^ res >> 2 ^ res >> 3 ^ res >> 4 ^ res >> 5 ^ res >> 6 ^ res >> 7
        ) & 1 == 0

    def _calculate_logic_flags(self, size, res):
        SIGN_MASK = 1 << (size - 1)
        self.CF = False  # cleared
        self.AF = False
        self.ZF = res == 0
        self.SF = (res & SIGN_MASK) != 0
        self.OF = False  # cleared
        self.PF = self._calculate_parity_flag(res)

    #####################################################
    # Instructions
    @instruction
    def CPUID(cpu):
        """
        CPUID instruction.

        The ID flag (bit 21) in the EFLAGS register indicates support for the
        CPUID instruction.  If a software procedure can set and clear this
        flag, the processor executing the procedure supports the CPUID
        instruction. This instruction operates the same in non-64-bit modes and
        64-bit mode.  CPUID returns processor identification and feature
        information in the EAX, EBX, ECX, and EDX registers.

        The instruction's output is dependent on the contents of the EAX
        register upon execution.

        :param cpu: current CPU.
        """
        # FIXME Choose conservative values and consider returning some default when eax not here
        conf = {
            # Taken from comparison against Unicorn@v1.0.2
            0x0: (0x00000004, 0x68747541, 0x444D4163, 0x69746E65),
            # Taken from comparison against Unicorn@v1.0.2
            0x1: (0x663, 0x800, 0x2182200, 0x7088100),
            # TODO: Check against Unicorn
            0x2: (0x76035A01, 0x00F0B5FF, 0x00000000, 0x00C10000),
            0x4: {
                0x0: (0x1C004121, 0x01C0003F, 0x0000003F, 0x00000000),
                0x1: (0x1C004122, 0x01C0003F, 0x0000003F, 0x00000000),
                0x2: (0x1C004143, 0x01C0003F, 0x000001FF, 0x00000000),
                0x3: (0x1C03C163, 0x03C0003F, 0x00000FFF, 0x00000006),
            },
            0x7: (0x00000000, 0x00000000, 0x00000000, 0x00000000),
            0x8: (0x00000000, 0x00000000, 0x00000000, 0x00000000),
            0xB: {
                0x0: (0x00000001, 0x00000002, 0x00000100, 0x00000005),
                0x1: (0x00000004, 0x00000004, 0x00000201, 0x00000003),
            },
            0xD: {
                0x0: (0x00000000, 0x00000000, 0x00000000, 0x00000000),
                0x1: (0x00000000, 0x00000000, 0x00000000, 0x00000000),
            },
            # CPUID with EAX=80000000h returns the highest supported extended function
            # query in EAX. We don't currently support any other than 80000000h itself,
            # so just return it back.
            0x80000000: (0x80000000, 0x00000000, 0x00000000, 0x00000000),
        }

        if cpu.EAX not in conf:
            logger.warning("CPUID with EAX=%x not implemented @ %x", cpu.EAX, cpu.PC)
            cpu.EAX, cpu.EBX, cpu.ECX, cpu.EDX = 0, 0, 0, 0
            return

        if isinstance(conf[cpu.EAX], tuple):
            cpu.EAX, cpu.EBX, cpu.ECX, cpu.EDX = conf[cpu.EAX]
            return

        if cpu.ECX not in conf[cpu.EAX]:
            logger.warning("CPUID with EAX=%x ECX=%x not implemented", cpu.EAX, cpu.ECX)
            cpu.EAX, cpu.EBX, cpu.ECX, cpu.EDX = 0, 0, 0, 0
            return

        cpu.EAX, cpu.EBX, cpu.ECX, cpu.EDX = conf[cpu.EAX][cpu.ECX]

    @instruction
    def XGETBV(cpu):
        """
        XGETBV instruction.

        Reads the contents of the extended cont register (XCR) specified in the ECX register into registers EDX:EAX.
        Implemented only for ECX = 0.

        :param cpu: current CPU.
        """
        # if cpu.ECX != 0:
        # logger.debug("XGETBV ECX=%x not implemented", cpu.ECX)
        cpu.EAX, cpu.EDX = 7, 0

    ########################################################################################
    # Generic Operations
    ########################################################################################
    # Logical: AND, TEST, NOT, XOR, OR
    ########################################################################################
    @instruction
    def AND(cpu, dest, src):
        """
        Logical AND.

        Performs a bitwise AND operation on the destination (first) and source
        (second) operands and stores the result in the destination operand location.
        Each bit of the result is set to 1 if both corresponding bits of the first and
        second operands are 1; otherwise, it is set to 0.

        The OF and CF flags are cleared; the SF, ZF, and PF flags are set according to the result::

            DEST  =  DEST AND SRC;

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        # XXX bypass a capstone bug that incorrectly extends and computes operands sizes
        # the bug has been fixed since capstone 4.0.alpha2 (commit de8dd26)
        if src.size == 64 and src.type == "immediate" and dest.size == 64:
            arg1 = Operators.SEXTEND(src.read(), 32, 64)
        else:
            arg1 = src.read()
        res = dest.write(dest.read() & arg1)
        # Defined Flags: szp
        cpu._calculate_logic_flags(dest.size, res)

    @instruction
    def TEST(cpu, src1, src2):
        """
        Logical compare.

        Computes the bit-wise logical AND of first operand (source 1 operand)
        and the second operand (source 2 operand) and sets the SF, ZF, and PF
        status flags according to the result. The result is then discarded::

            TEMP  =  SRC1 AND SRC2;
            SF  =  MSB(TEMP);
            IF TEMP  =  0
            THEN ZF  =  1;
            ELSE ZF  =  0;
            FI:
            PF  =  BitwiseXNOR(TEMP[0:7]);
            CF  =  0;
            OF  =  0;
            (*AF is Undefined*)

        :param cpu: current CPU.
        :param src1: first operand.
        :param src2: second operand.
        """
        # Defined Flags: szp
        temp = src1.read() & src2.read()
        cpu.SF = (temp & (1 << (src1.size - 1))) != 0
        cpu.ZF = temp == 0
        cpu.PF = cpu._calculate_parity_flag(temp)
        cpu.CF = False
        cpu.OF = False
        cpu.AF = False  # Undefined, but ends up being `0` in emulator

    @instruction
    def NOT(cpu, dest):
        """
        One's complement negation.

        Performs a bitwise NOT operation (each 1 is cleared to 0, and each 0
        is set to 1) on the destination operand and stores the result in the destination
        operand location::

            DEST  =  NOT DEST;

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        res = dest.write(~dest.read())
        # Flags Affected: None.

    @instruction
    def XOR(cpu, dest, src):
        """
        Logical exclusive OR.

        Performs a bitwise exclusive-OR(XOR) operation on the destination (first)
        and source (second) operands and stores the result in the destination
        operand location.

        Each bit of the result is 1 if the corresponding bits of the operands
        are different; each bit is 0 if the corresponding bits are the same.

        The OF and CF flags are cleared; the SF, ZF, and PF flags are set according to the result::

            DEST  =  DEST XOR SRC;

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        if dest == src:
            # if the operands are the same write zero
            res = dest.write(0)
        else:
            res = dest.write(dest.read() ^ src.read())
        # Defined Flags: szp
        cpu._calculate_logic_flags(dest.size, res)

    @instruction
    def OR(cpu, dest, src):
        """
        Logical inclusive OR.

        Performs a bitwise inclusive OR operation between the destination (first)
        and source (second) operands and stores the result in the destination operand location.

        Each bit of the result of the OR instruction is set to 0 if both corresponding
        bits of the first and second operands are 0; otherwise, each bit is set
        to 1.

        The OF and CF flags are cleared; the SF, ZF, and PF flags are set according to the result::

            DEST  =  DEST OR SRC;

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        res = dest.write(dest.read() | src.read())
        # Defined Flags: szp
        cpu._calculate_logic_flags(dest.size, res)

    ########################################################################################
    # Generic Operations
    ########################################################################################
    # Arithmetic: AAA, AAD, AAM, AAS, ADC, ADD, CMP, CMPXCHG
    #             CMPXCHG8B,DAA, DAS, DEC, DIV, IDIV, IMUL, INC, MUL,
    #             NEG, SBB, SUB, XADD
    ########################################################################################
    @instruction
    def AAA(cpu):
        """
        ASCII adjust after addition.

        Adjusts the sum of two unpacked BCD values to create an unpacked BCD
        result. The AL register is the implied source and destination operand
        for this instruction. The AAA instruction is only useful when it follows
        an ADD instruction that adds (binary addition) two unpacked BCD values
        and stores a byte result in the AL register. The AAA instruction then
        adjusts the contents of the AL register to contain the correct 1-digit
        unpacked BCD result.
        If the addition produces a decimal carry, the AH register is incremented
        by 1, and the CF and AF flags are set. If there was no decimal carry,
        the CF and AF flags are cleared and the AH register is unchanged. In either
        case, bits 4 through 7 of the AL register are cleared to 0.

        This instruction executes as described in compatibility mode and legacy mode.
        It is not valid in 64-bit mode.
        ::
                IF ((AL AND 0FH) > 9) Operators.OR(AF  =  1)
                THEN
                    AL  =  (AL + 6);
                    AH  =  AH + 1;
                    AF  =  1;
                    CF  =  1;
                ELSE
                    AF  =  0;
                    CF  =  0;
                FI;
                AL  =  AL AND 0FH;
        :param cpu: current CPU.
        """
        cpu.AF = Operators.OR(cpu.AL & 0x0F > 9, cpu.AF)
        cpu.CF = cpu.AF
        cpu.AH = Operators.ITEBV(8, cpu.AF, cpu.AH + 1, cpu.AH)
        cpu.AL = Operators.ITEBV(8, cpu.AF, cpu.AL + 6, cpu.AL)
        """
        if (cpu.AL & 0x0F > 9) or cpu.AF == 1:
            cpu.AL = cpu.AL + 6
            cpu.AH = cpu.AH + 1
            cpu.AF = True
            cpu.CF = True
        else:
            cpu.AF = False
            cpu.CF = False
        """
        cpu.AL = cpu.AL & 0x0F

    @instruction
    def AAD(cpu, imm=None):
        """
        ASCII adjust AX before division.

        Adjusts two unpacked BCD digits (the least-significant digit in the
        AL register and the most-significant digit in the AH register) so that
        a division operation performed on the result will yield a correct unpacked
        BCD value. The AAD instruction is only useful when it precedes a DIV instruction
        that divides (binary division) the adjusted value in the AX register by
        an unpacked BCD value.
        The AAD instruction sets the value in the AL register to (AL + (10 * AH)), and then
        clears the AH register to 00H. The value in the AX register is then equal to the binary
        equivalent of the original unpacked two-digit (base 10) number in registers AH and AL.

        The SF, ZF, and PF flags are set according to the resulting binary value in the AL register.

        This instruction executes as described in compatibility mode and legacy mode.
        It is not valid in 64-bit mode.::

                tempAL  =  AL;
                tempAH  =  AH;
                AL  =  (tempAL + (tempAH * 10)) AND FFH;
                AH  =  0

        :param cpu: current CPU.
        """
        if imm is None:
            imm = 10
        else:
            imm = imm.read()

        cpu.AL += cpu.AH * imm
        cpu.AH = 0

        # Defined flags: ...sz.p.
        cpu._calculate_logic_flags(8, cpu.AL)

    @instruction
    def AAM(cpu, imm=None):
        """
        ASCII adjust AX after multiply.

        Adjusts the result of the multiplication of two unpacked BCD values
        to create a pair of unpacked (base 10) BCD values. The AX register is
        the implied source and destination operand for this instruction. The AAM
        instruction is only useful when it follows a MUL instruction that multiplies
        (binary multiplication) two unpacked BCD values and stores a word result
        in the AX register. The AAM instruction then adjusts the contents of the
        AX register to contain the correct 2-digit unpacked (base 10) BCD result.

        The SF, ZF, and PF flags are set according to the resulting binary value in the AL register.

        This instruction executes as described in compatibility mode and legacy mode.
        It is not valid in 64-bit mode.::

                tempAL  =  AL;
                AH  =  tempAL / 10;
                AL  =  tempAL MOD 10;

        :param cpu: current CPU.
        """
        if imm is None:
            imm = 10
        else:
            imm = imm.read()

        cpu.AH = Operators.UDIV(cpu.AL, imm)
        cpu.AL = Operators.UREM(cpu.AL, imm)

        # Defined flags: ...sz.p.
        cpu._calculate_logic_flags(8, cpu.AL)

    @instruction
    def AAS(cpu):
        """
        ASCII Adjust AL after subtraction.

        Adjusts the result of the subtraction of two unpacked BCD values to  create a unpacked
        BCD result. The AL register is the implied source and destination operand for this instruction.
        The AAS instruction is only useful when it follows a SUB instruction that subtracts
        (binary subtraction) one unpacked BCD value from another and stores a byte result in the AL
        register. The AAA instruction then adjusts the contents of the AL register to contain the
        correct 1-digit unpacked BCD result. If the subtraction produced a decimal carry, the AH register
        is decremented by 1, and the CF and AF flags are set. If no decimal carry occurred, the CF and AF
        flags are cleared, and the AH register is unchanged. In either case, the AL register is left with
        its top nibble set to 0.

        The AF and CF flags are set to 1 if there is a decimal borrow; otherwise, they are cleared to 0.

        This instruction executes as described in compatibility mode and legacy mode.
        It is not valid in 64-bit mode.::


                IF ((AL AND 0FH) > 9) Operators.OR(AF  =  1)
                THEN
                    AX  =  AX - 6;
                    AH  =  AH - 1;
                    AF  =  1;
                    CF  =  1;
                ELSE
                    CF  =  0;
                    AF  =  0;
                FI;
                AL  =  AL AND 0FH;

        :param cpu: current CPU.
        """
        if (cpu.AL & 0x0F > 9) or cpu.AF == 1:
            cpu.AX = cpu.AX - 6
            cpu.AH = cpu.AH - 1
            cpu.AF = True
            cpu.CF = True
        else:
            cpu.AF = False
            cpu.CF = False
        cpu.AL = cpu.AL & 0x0F

    @instruction
    def ADC(cpu, dest, src):
        """
        Adds with carry.

        Adds the destination operand (first operand), the source operand (second operand),
        and the carry (CF) flag and stores the result in the destination operand. The state
        of the CF flag represents a carry from a previous addition. When an immediate value
        is used as an operand, it is sign-extended to the length of the destination operand
        format. The ADC instruction does not distinguish between signed or unsigned operands.
        Instead, the processor evaluates the result for both data types and sets the OF and CF
        flags to indicate a carry in the signed or unsigned result, respectively. The SF flag
        indicates the sign of the signed result. The ADC instruction is usually executed as
        part of a multibyte or multiword addition in which an ADD instruction is followed by an
        ADC instruction::

                DEST  =  DEST + SRC + CF;

        The OF, SF, ZF, AF, CF, and PF flags are set according to the result.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        cpu._ADD(dest, src, carry=True)

    @instruction
    def ADD(cpu, dest, src):
        """
        Add.

        Adds the first operand (destination operand) and the second operand (source operand)
        and stores the result in the destination operand. When an immediate value is used as
        an operand, it is sign-extended to the length of the destination operand format.
        The ADD instruction does not distinguish between signed or unsigned operands. Instead,
        the processor evaluates the result for both data types and sets the OF and CF flags to
        indicate a carry in the signed or unsigned result, respectively. The SF flag indicates
        the sign of the signed result::

                DEST  =  DEST + SRC;

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        cpu._ADD(dest, src, carry=False)

    def _ADD(cpu, dest, src, carry=False):
        MASK = (1 << dest.size) - 1
        SIGN_MASK = 1 << (dest.size - 1)
        arg0 = dest.read()
        if src.size < dest.size:
            arg1 = Operators.SEXTEND(src.read(), src.size, dest.size)
        else:
            arg1 = src.read()

        to_add = arg1
        if carry:
            cv = Operators.ITEBV(dest.size, cpu.CF, 1, 0)
            to_add = arg1 + cv

        res = dest.write((arg0 + to_add) & MASK)

        # Affected flags: oszapc
        tempCF = Operators.OR(Operators.ULT(res, arg0 & MASK), Operators.ULT(res, arg1 & MASK))
        if carry:
            # case of 0xFFFFFFFF + 0xFFFFFFFF + CF(1)
            tempCF = Operators.OR(tempCF, Operators.AND(res == MASK, cpu.CF))

        cpu.CF = tempCF
        cpu.AF = ((arg0 ^ arg1) ^ res) & 0x10 != 0
        cpu.ZF = res == 0
        cpu.SF = (res & SIGN_MASK) != 0
        cpu.OF = (((arg0 ^ arg1 ^ SIGN_MASK) & (res ^ arg1)) & SIGN_MASK) != 0
        cpu.PF = cpu._calculate_parity_flag(res)

    @instruction
    def CMP(cpu, src1, src2):
        """
        Compares two operands.

        Compares the first source operand with the second source operand and sets the status flags
        in the EFLAGS register according to the results. The comparison is performed by subtracting
        the second operand from the first operand and then setting the status flags in the same manner
        as the SUB instruction. When an immediate value is used as an operand, it is sign-extended to
        the length of the first operand::

                temp  =  SRC1 - SignExtend(SRC2);
                ModifyStatusFlags; (* Modify status flags in the same manner as the SUB instruction*)

        The CF, OF, SF, ZF, AF, and PF flags are set according to the result.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        arg0 = src1.read()
        arg1 = Operators.SEXTEND(src2.read(), src2.size, src1.size)

        # Affected Flags o..szapc
        cpu._calculate_CMP_flags(src1.size, arg0 - arg1, arg0, arg1)

    @instruction
    def CMPXCHG(cpu, dest, src):
        """
        Compares and exchanges.

        Compares the value in the AL, AX, EAX or RAX register (depending on the
        size of the operand) with the first operand (destination operand). If
        the two values are equal, the second operand (source operand) is loaded
        into the destination operand. Otherwise, the destination operand is
        loaded into the AL, AX, EAX or RAX register.

        The ZF flag is set if the values in the destination operand and
        register AL, AX, or EAX are equal; otherwise it is cleared. The CF, PF,
        AF, SF, and OF flags are set according to the results of the comparison
        operation::

        (* accumulator  =  AL, AX, EAX or RAX,  depending on whether *)
        (* a byte, word, a doubleword or a 64bit comparison is being performed*)
        IF accumulator  ==  DEST
        THEN
            ZF  =  1
            DEST  =  SRC
        ELSE
            ZF  =  0
            accumulator  =  DEST
        FI;

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        size = dest.size
        reg_name = {8: "AL", 16: "AX", 32: "EAX", 64: "RAX"}[size]
        accumulator = cpu.read_register(reg_name)
        sval = src.read()
        dval = dest.read()

        cpu.write_register(reg_name, dval)
        dest.write(Operators.ITEBV(size, accumulator == dval, sval, dval))

        # Affected Flags o..szapc
        cpu._calculate_CMP_flags(size, accumulator - dval, accumulator, dval)

    @instruction
    def CMPXCHG8B(cpu, dest):
        """
        Compares and exchanges bytes.

        Compares the 64-bit value in EDX:EAX (or 128-bit value in RDX:RAX if
        operand size is 128 bits) with the operand (destination operand). If
        the values are equal, the 64-bit value in ECX:EBX (or 128-bit value in
        RCX:RBX) is stored in the destination operand.  Otherwise, the value in
        the destination operand is loaded into EDX:EAX (or RDX:RAX)::

                IF (64-Bit Mode and OperandSize = 64)
                THEN
                    IF (RDX:RAX = DEST)
                    THEN
                        ZF = 1;
                        DEST = RCX:RBX;
                    ELSE
                        ZF = 0;
                        RDX:RAX = DEST;
                    FI
                ELSE
                    IF (EDX:EAX = DEST)
                    THEN
                        ZF = 1;
                        DEST = ECX:EBX;
                    ELSE
                        ZF = 0;
                        EDX:EAX = DEST;
                    FI;
                FI;

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        size = dest.size
        half_size = size // 2
        cmp_reg_name_l = {64: "EAX", 128: "RAX"}[size]
        cmp_reg_name_h = {64: "EDX", 128: "RDX"}[size]
        src_reg_name_l = {64: "EBX", 128: "RBX"}[size]
        src_reg_name_h = {64: "ECX", 128: "RCX"}[size]

        # EDX:EAX or RDX:RAX
        cmph = cpu.read_register(cmp_reg_name_h)
        cmpl = cpu.read_register(cmp_reg_name_l)

        srch = cpu.read_register(src_reg_name_h)
        srcl = cpu.read_register(src_reg_name_l)

        cmp0 = Operators.CONCAT(size, cmph, cmpl)
        src0 = Operators.CONCAT(size, srch, srcl)
        arg_dest = dest.read()
        cpu.ZF = arg_dest == cmp0

        dest.write(Operators.ITEBV(size, cpu.ZF, Operators.CONCAT(size, srch, srcl), arg_dest))
        cpu.write_register(
            cmp_reg_name_l,
            Operators.ITEBV(half_size, cpu.ZF, cmpl, Operators.EXTRACT(arg_dest, 0, half_size)),
        )
        cpu.write_register(
            cmp_reg_name_h,
            Operators.ITEBV(
                half_size, cpu.ZF, cmph, Operators.EXTRACT(arg_dest, half_size, half_size)
            ),
        )

    @instruction
    def DAA(cpu):
        """
        Decimal adjusts AL after addition.

        Adjusts the sum of two packed BCD values to create a packed BCD result. The AL register
        is the implied source and destination operand. If a decimal carry is detected, the CF
        and AF flags are set accordingly.
        The CF and AF flags are set if the adjustment of the value results in a decimal carry in
        either digit of the result. The SF, ZF, and PF flags are set according to the result.

        This instruction is not valid in 64-bit mode.::

                IF (((AL AND 0FH) > 9) or AF  =  1)
                THEN
                    AL  =  AL + 6;
                    CF  =  CF OR CarryFromLastAddition; (* CF OR carry from AL  =  AL + 6 *)
                    AF  =  1;
                ELSE
                    AF  =  0;
                FI;
                IF ((AL AND F0H) > 90H) or CF  =  1)
                THEN
                    AL  =  AL + 60H;
                    CF  =  1;
                ELSE
                    CF  =  0;
                FI;

        :param cpu: current CPU.
        """

        cpu.AF = Operators.OR((cpu.AL & 0x0F) > 9, cpu.AF)
        oldAL = cpu.AL
        cpu.AL = Operators.ITEBV(8, cpu.AF, cpu.AL + 6, cpu.AL)
        cpu.CF = Operators.ITE(cpu.AF, Operators.OR(cpu.CF, cpu.AL < oldAL), cpu.CF)

        cpu.CF = Operators.OR((cpu.AL & 0xF0) > 0x90, cpu.CF)
        cpu.AL = Operators.ITEBV(8, cpu.CF, cpu.AL + 0x60, cpu.AL)
        """
        #old not-symbolic aware version...
        if ((cpu.AL & 0x0f) > 9) or cpu.AF:
            oldAL = cpu.AL
            cpu.AL =  cpu.AL + 6
            cpu.CF = Operators.OR(cpu.CF, cpu.AL < oldAL)
            cpu.AF  =  True
        else:
            cpu.AF  =  False

        if ((cpu.AL & 0xf0) > 0x90) or cpu.CF:
            cpu.AL  = cpu.AL + 0x60
            cpu.CF  =  True
        else:
            cpu.CF  =  False
        """

        cpu.ZF = cpu.AL == 0
        cpu.SF = (cpu.AL & 0x80) != 0
        cpu.PF = cpu._calculate_parity_flag(cpu.AL)

    @instruction
    def DAS(cpu):
        """
        Decimal adjusts AL after subtraction.

        Adjusts the result of the subtraction of two packed BCD values to create a packed BCD result.
        The AL register is the implied source and destination operand. If a decimal borrow is detected,
        the CF and AF flags are set accordingly. This instruction is not valid in 64-bit mode.

        The SF, ZF, and PF flags are set according to the result.::

                IF (AL AND 0FH) > 9 OR AF  =  1
                THEN
                    AL  =  AL - 6;
                    CF  =  CF OR BorrowFromLastSubtraction; (* CF OR borrow from AL  =  AL - 6 *)
                    AF  =  1;
                ELSE
                    AF  =  0;
                FI;
                IF ((AL > 99H) or OLD_CF  =  1)
                THEN
                    AL  =  AL - 60H;
                    CF  =  1;

        :param cpu: current CPU.
        """
        oldAL = cpu.AL
        oldCF = cpu.CF

        cpu.AF = Operators.OR((cpu.AL & 0x0F) > 9, cpu.AF)
        cpu.AL = Operators.ITEBV(8, cpu.AF, cpu.AL - 6, cpu.AL)
        cpu.CF = Operators.ITE(cpu.AF, Operators.OR(oldCF, cpu.AL > oldAL), cpu.CF)

        cpu.CF = Operators.ITE(Operators.OR(oldAL > 0x99, oldCF), True, cpu.CF)
        cpu.AL = Operators.ITEBV(8, Operators.OR(oldAL > 0x99, oldCF), cpu.AL - 0x60, cpu.AL)
        #
        """
        if (cpu.AL & 0x0f) > 9 or cpu.AF:
            cpu.AL = cpu.AL - 6;
            cpu.CF = Operators.OR(oldCF, cpu.AL > oldAL)
            cpu.AF = True
        else:
            cpu.AF  =  False

        if ((oldAL > 0x99) or oldCF):
            cpu.AL = cpu.AL - 0x60
            cpu.CF = True
        """
        cpu.ZF = cpu.AL == 0
        cpu.SF = (cpu.AL & 0x80) != 0
        cpu.PF = cpu._calculate_parity_flag(cpu.AL)

    @instruction
    def DEC(cpu, dest):
        """
        Decrements by 1.

        Subtracts 1 from the destination operand, while preserving the state of
        the CF flag. The destination operand can be a register or a memory
        location. This instruction allows a loop counter to be updated without
        disturbing the CF flag. (To perform a decrement operation that updates
        the CF flag, use a SUB instruction with an immediate operand of 1.) The
        instruction's 64-bit mode default operation size is 32 bits.

        The OF, SF, ZF, AF, and PF flags are set according to the result::

                DEST  =  DEST - 1;

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        arg0 = dest.read()
        res = dest.write(arg0 - 1)
        # Affected Flags o..szapc
        res &= (1 << dest.size) - 1
        SIGN_MASK = 1 << (dest.size - 1)
        cpu.AF = ((arg0 ^ 1) ^ res) & 0x10 != 0
        cpu.ZF = res == 0
        cpu.SF = (res & SIGN_MASK) != 0
        cpu.OF = res == SIGN_MASK
        cpu.PF = cpu._calculate_parity_flag(res)

    @instruction
    def DIV(cpu, src):
        """
        Unsigned divide.

        Divides (unsigned) the value in the AX register, DX:AX register pair,
        or EDX:EAX or RDX:RAX register pair (dividend) by the source operand
        (divisor) and stores the result in the AX (AH:AL), DX:AX, EDX:EAX or
        RDX:RAX registers. The source operand can be a general-purpose register
        or a memory location. The action of this instruction depends of the
        operand size (dividend/divisor). Division using 64-bit operand is
        available only in 64-bit mode. Non-integral results are truncated
        (chopped) towards 0. The reminder is always less than the divisor in
        magnitude. Overflow is indicated with the #DE (divide error) exception
        rather than with the CF flag::

            IF SRC  =  0
                THEN #DE; FI;(* divide error *)
            IF OperandSize  =  8 (* word/byte operation *)
                THEN
                    temp  =  AX / SRC;
                    IF temp > FFH
                        THEN #DE; (* divide error *) ;
                        ELSE
                            AL  =  temp;
                            AH  =  AX MOD SRC;
                    FI;
                ELSE IF OperandSize  =  16 (* doubleword/word operation *)
                    THEN
                        temp  =  DX:AX / SRC;
                        IF temp > FFFFH
                            THEN #DE; (* divide error *) ;
                        ELSE
                            AX  =  temp;
                            DX  =  DX:AX MOD SRC;
                        FI;
                    FI;
                ELSE If OperandSize = 32 (* quadword/doubleword operation *)
                    THEN
                        temp  =  EDX:EAX / SRC;
                        IF temp > FFFFFFFFH
                            THEN #DE; (* divide error *) ;
                        ELSE
                            EAX  =  temp;
                            EDX  =  EDX:EAX MOD SRC;
                        FI;
                    FI;
                ELSE IF OperandSize = 64 (*Doublequadword/quadword operation*)
                    THEN
                        temp = RDX:RAX / SRC;
                        IF temp > FFFFFFFFFFFFFFFFH
                            THEN #DE; (* Divide error *)
                        ELSE
                            RAX = temp;
                            RDX = RDX:RAX MOD SRC;
                        FI;
                    FI;
            FI;

        :param cpu: current CPU.
        :param src: source operand.
        """
        size = src.size
        reg_name_h = {8: "DL", 16: "DX", 32: "EDX", 64: "RDX"}[size]
        reg_name_l = {8: "AL", 16: "AX", 32: "EAX", 64: "RAX"}[size]

        dividend = Operators.CONCAT(
            size * 2, cpu.read_register(reg_name_h), cpu.read_register(reg_name_l)
        )
        divisor = Operators.ZEXTEND(src.read(), size * 2)

        # TODO make symbol friendly
        if isinstance(divisor, int) and divisor == 0:
            raise DivideByZeroError()
        quotient = Operators.UDIV(dividend, divisor)

        MASK = (1 << size) - 1

        # TODO make symbol friendly
        if isinstance(quotient, int) and quotient > MASK:
            raise DivideByZeroError()
        remainder = Operators.UREM(dividend, divisor)

        cpu.write_register(reg_name_l, Operators.EXTRACT(quotient, 0, size))
        cpu.write_register(reg_name_h, Operators.EXTRACT(remainder, 0, size))
        # Flags Affected
        # The CF, OF, SF, ZF, AF, and PF flags are undefined.

    @instruction
    def IDIV(cpu, src):
        """
        Signed divide.

        Divides (signed) the value in the AL, AX, or EAX register by the source
        operand and stores the result in the AX, DX:AX, or EDX:EAX registers.
        The source operand can be a general-purpose register or a memory
        location. The action of this instruction depends on the operand size.::

        IF SRC  =  0
        THEN #DE; (* divide error *)
        FI;
        IF OpernadSize  =  8 (* word/byte operation *)
        THEN
            temp  =  AX / SRC; (* signed division *)
            IF (temp > 7FH) Operators.OR(temp < 80H)
            (* if a positive result is greater than 7FH or a negative result is
            less than 80H *)
            THEN #DE; (* divide error *) ;
            ELSE
                AL  =  temp;
                AH  =  AX SignedModulus SRC;
            FI;
        ELSE
            IF OpernadSize  =  16 (* doubleword/word operation *)
            THEN
                temp  =  DX:AX / SRC; (* signed division *)
                IF (temp > 7FFFH) Operators.OR(temp < 8000H)
                (* if a positive result is greater than 7FFFH *)
                (* or a negative result is less than 8000H *)
                THEN #DE; (* divide error *) ;
                ELSE
                    AX  =  temp;
                    DX  =  DX:AX SignedModulus SRC;
                FI;
            ELSE (* quadword/doubleword operation *)
                temp  =  EDX:EAX / SRC; (* signed division *)
                IF (temp > 7FFFFFFFH) Operators.OR(temp < 80000000H)
                (* if a positive result is greater than 7FFFFFFFH *)
                (* or a negative result is less than 80000000H *)
                THEN #DE; (* divide error *) ;
                ELSE
                    EAX  =  temp;
                    EDX  =  EDX:EAX SignedModulus SRC;
                FI;
            FI;
        FI;

        :param cpu: current CPU.
        :param src: source operand.
        """

        reg_name_h = {8: "AH", 16: "DX", 32: "EDX", 64: "RDX"}[src.size]
        reg_name_l = {8: "AL", 16: "AX", 32: "EAX", 64: "RAX"}[src.size]

        dividend = Operators.CONCAT(
            src.size * 2, cpu.read_register(reg_name_h), cpu.read_register(reg_name_l)
        )

        divisor = src.read()
        if isinstance(divisor, int) and divisor == 0:
            raise DivideByZeroError()

        dst_size = src.size * 2

        divisor = Operators.SEXTEND(divisor, src.size, dst_size)
        mask = (1 << dst_size) - 1
        sign_mask = 1 << (dst_size - 1)

        dividend_sign = (dividend & sign_mask) != 0
        divisor_sign = (divisor & sign_mask) != 0

        if isinstance(divisor, int):
            if divisor_sign:
                divisor = ((~divisor) + 1) & mask
                divisor = -divisor

        if isinstance(dividend, int):
            if dividend_sign:
                dividend = ((~dividend) + 1) & mask
                dividend = -dividend

        quotient = Operators.SDIV(dividend, divisor)
        if isinstance(dividend, int) and isinstance(dividend, int):
            # handle the concrete case
            remainder = dividend - (quotient * divisor)
        else:
            # symbolic case -- optimize via SREM
            remainder = Operators.SREM(dividend, divisor)

        cpu.write_register(reg_name_l, Operators.EXTRACT(quotient, 0, src.size))
        cpu.write_register(reg_name_h, Operators.EXTRACT(remainder, 0, src.size))
        # Flags Affected
        # The CF, OF, SF, ZF, AF, and PF flags are undefined.

    @instruction
    def IMUL(cpu, *operands):
        """
        Signed multiply.

        Performs a signed multiplication of two operands. This instruction has
        three forms, depending on the number of operands.
            - One-operand form. This form is identical to that used by the MUL
            instruction. Here, the source operand (in a general-purpose
            register or memory location) is multiplied by the value in the AL,
            AX, or EAX register (depending on the operand size) and the product
            is stored in the AX, DX:AX, or EDX:EAX registers, respectively.
            - Two-operand form. With this form the destination operand (the
            first operand) is multiplied by the source operand (second
            operand). The destination operand is a general-purpose register and
            the source operand is an immediate value, a general-purpose
            register, or a memory location. The product is then stored in the
            destination operand location.
            - Three-operand form. This form requires a destination operand (the
            first operand) and two source operands (the second and the third
            operands). Here, the first source operand (which can be a
            general-purpose register or a memory location) is multiplied by the
            second source operand (an immediate value). The product is then
            stored in the destination operand (a general-purpose register).

        When an immediate value is used as an operand, it is sign-extended to
        the length of the destination operand format. The CF and OF flags are
        set when significant bits are carried into the upper half of the
        result. The CF and OF flags are cleared when the result fits exactly in
        the lower half of the result. The three forms of the IMUL instruction
        are similar in that the length of the product is calculated to twice
        the length of the operands. With the one-operand form, the product is
        stored exactly in the destination. With the two- and three- operand
        forms, however, result is truncated to the length of the destination
        before it is stored in the destination register. Because of this
        truncation, the CF or OF flag should be tested to ensure that no
        significant bits are lost. The two- and three-operand forms may also be
        used with unsigned operands because the lower half of the product is
        the same regardless if the operands are signed or unsigned. The CF and
        OF flags, however, cannot be used to determine if the upper half of the
        result is non-zero::

        IF (NumberOfOperands == 1)
        THEN
            IF (OperandSize == 8)
            THEN
                AX = AL * SRC (* Signed multiplication *)
                IF AL == AX
                THEN
                    CF = 0; OF = 0;
                ELSE
                    CF = 1; OF = 1;
                FI;
            ELSE
                IF OperandSize == 16
                THEN
                    DX:AX = AX * SRC (* Signed multiplication *)
                    IF sign_extend_to_32 (AX) == DX:AX
                    THEN
                        CF = 0; OF = 0;
                    ELSE
                        CF = 1; OF = 1;
                    FI;
                ELSE
                    IF OperandSize == 32
                    THEN
                        EDX:EAX = EAX * SRC (* Signed multiplication *)
                        IF EAX == EDX:EAX
                        THEN
                            CF = 0; OF = 0;
                        ELSE
                            CF = 1; OF = 1;
                        FI;
                    ELSE (* OperandSize = 64 *)
                        RDX:RAX = RAX * SRC (* Signed multiplication *)
                        IF RAX == RDX:RAX
                        THEN
                            CF = 0; OF = 0;
                        ELSE
                           CF = 1; OF = 1;
                        FI;
                    FI;
                FI;
        ELSE
            IF (NumberOfOperands = 2)
            THEN
                temp = DEST * SRC (* Signed multiplication; temp is double DEST size *)
                DEST = DEST * SRC (* Signed multiplication *)
                IF temp != DEST
                THEN
                    CF = 1; OF = 1;
                ELSE
                    CF = 0; OF = 0;
                FI;
            ELSE (* NumberOfOperands = 3 *)
                DEST = SRC1 * SRC2 (* Signed multiplication *)
                temp = SRC1 * SRC2 (* Signed multiplication; temp is double SRC1 size *)
                IF temp != DEST
                THEN
                    CF = 1; OF = 1;
                ELSE
                    CF = 0; OF = 0;
                FI;
            FI;
        FI;

        :param cpu: current CPU.
        :param operands: variable list of operands.
        """
        dest = operands[0]
        OperandSize = dest.size
        reg_name_h = {8: "AH", 16: "DX", 32: "EDX", 64: "RDX"}[OperandSize]
        reg_name_l = {8: "AL", 16: "AX", 32: "EAX", 64: "RAX"}[OperandSize]

        arg0 = dest.read()
        arg1 = None
        arg2 = None
        res = None
        if len(operands) == 1:
            arg1 = cpu.read_register(reg_name_l)
            temp = Operators.SEXTEND(arg0, OperandSize, OperandSize * 2) * Operators.SEXTEND(
                arg1, OperandSize, OperandSize * 2
            )
            temp = temp & ((1 << (OperandSize * 2)) - 1)
            cpu.write_register(reg_name_l, Operators.EXTRACT(temp, 0, OperandSize))
            cpu.write_register(reg_name_h, Operators.EXTRACT(temp, OperandSize, OperandSize))
            res = Operators.EXTRACT(temp, 0, OperandSize)
        elif len(operands) == 2:
            arg1 = operands[1].read()
            arg1 = Operators.SEXTEND(arg1, OperandSize, OperandSize * 2)
            temp = Operators.SEXTEND(arg0, OperandSize, OperandSize * 2) * arg1
            temp = temp & ((1 << (OperandSize * 2)) - 1)
            res = dest.write(Operators.EXTRACT(temp, 0, OperandSize))
        else:
            arg1 = operands[1].read()
            arg2 = operands[2].read()
            temp = Operators.SEXTEND(arg1, OperandSize, OperandSize * 2) * Operators.SEXTEND(
                arg2, operands[2].size, OperandSize * 2
            )
            temp = temp & ((1 << (OperandSize * 2)) - 1)
            res = dest.write(Operators.EXTRACT(temp, 0, OperandSize))

        cpu.CF = Operators.SEXTEND(res, OperandSize, OperandSize * 2) != temp
        cpu.OF = cpu.CF

    @instruction
    def INC(cpu, dest):
        """
        Increments by 1.

        Adds 1 to the destination operand, while preserving the state of the
        CF flag. The destination operand can be a register or a memory location.
        This instruction allows a loop counter to be updated without disturbing
        the CF flag. (Use a ADD instruction with an immediate operand of 1 to
        perform an increment operation that does updates the CF flag.)::

                DEST  =  DEST +1;

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        arg0 = dest.read()
        res = dest.write(arg0 + 1)
        res &= (1 << dest.size) - 1
        SIGN_MASK = 1 << (dest.size - 1)
        cpu.AF = ((arg0 ^ 1) ^ res) & 0x10 != 0
        cpu.ZF = res == 0
        cpu.SF = (res & SIGN_MASK) != 0
        cpu.OF = res == SIGN_MASK
        cpu.PF = cpu._calculate_parity_flag(res)

    @instruction
    def MUL(cpu, src):
        """
        Unsigned multiply.

        Performs an unsigned multiplication of the first operand (destination
        operand) and the second operand (source operand) and stores the result
        in the destination operand. The destination operand is an implied operand
        located in register AL, AX or EAX (depending on the size of the operand);
        the source operand is located in a general-purpose register or a memory location.

        The result is stored in register AX, register pair DX:AX, or register
        pair EDX:EAX (depending on the operand size), with the high-order bits
        of the product contained in register AH, DX, or EDX, respectively. If
        the high-order bits of the product are 0, the CF and OF flags are cleared;
        otherwise, the flags are set::

                IF byte operation
                THEN
                    AX  =  AL * SRC
                ELSE (* word or doubleword operation *)
                    IF OperandSize  =  16
                    THEN
                        DX:AX  =  AX * SRC
                    ELSE (* OperandSize  =  32 *)
                        EDX:EAX  =  EAX * SRC
                    FI;
                FI;

        :param cpu: current CPU.
        :param src: source operand.
        """
        size = src.size
        reg_name_low, reg_name_high = {
            8: ("AL", "AH"),
            16: ("AX", "DX"),
            32: ("EAX", "EDX"),
            64: ("RAX", "RDX"),
        }[size]
        res = Operators.ZEXTEND(cpu.read_register(reg_name_low), 256) * Operators.ZEXTEND(
            src.read(), 256
        )
        cpu.write_register(reg_name_low, Operators.EXTRACT(res, 0, size))
        cpu.write_register(reg_name_high, Operators.EXTRACT(res, size, size))
        cpu.OF = Operators.EXTRACT(res, size, size) != 0
        cpu.CF = cpu.OF

    @instruction
    def NEG(cpu, dest):
        """
        Two's complement negation.

        Replaces the value of operand (the destination operand) with its two's complement.
        (This operation is equivalent to subtracting the operand from 0.) The destination operand is
        located in a general-purpose register or a memory location::

                IF DEST  =  0
                THEN CF  =  0
                ELSE CF  =  1;
                FI;
                DEST  =  - (DEST)

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        source = dest.read()
        res = dest.write(-source)
        cpu._calculate_logic_flags(dest.size, res)
        cpu.CF = source != 0
        cpu.AF = (res & 0x0F) != 0x00

    @instruction
    def SBB(cpu, dest, src):
        """
        Integer subtraction with borrow.

        Adds the source operand (second operand) and the carry (CF) flag, and
        subtracts the result from the destination operand (first operand). The
        result of the subtraction is stored in the destination operand. The
        destination operand can be a register or a memory location; the source
        operand can be an immediate, a register, or a memory location.
        (However, two memory operands cannot be used in one instruction.) The
        state of the CF flag represents a borrow from a previous subtraction.
        When an immediate value is used as an operand, it is sign-extended to
        the length of the destination operand format.
        The SBB instruction does not distinguish between signed or unsigned
        operands. Instead, the processor evaluates the result for both data
        types and sets the OF and CF flags to indicate a borrow in the signed
        or unsigned result, respectively. The SF flag indicates the sign of the
        signed result.  The SBB instruction is usually executed as part of a
        multibyte or multiword subtraction in which a SUB instruction is
        followed by a SBB instruction::

                DEST  =  DEST - (SRC + CF);

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        cpu._SUB(dest, src, carry=True)

    @instruction
    def SUB(cpu, dest, src):
        """
        Subtract.

        Subtracts the second operand (source operand) from the first operand
        (destination operand) and stores the result in the destination operand.
        The destination operand can be a register or a memory location; the
        source operand can be an immediate, register, or memory location.
        (However, two memory operands cannot be used in one instruction.) When
        an immediate value is used as an operand, it is sign-extended to the
        length of the destination operand format.
        The SUB instruction does not distinguish between signed or unsigned
        operands. Instead, the processor evaluates the result for both
        data types and sets the OF and CF flags to indicate a borrow in the
        signed or unsigned result, respectively. The SF flag indicates the sign
        of the signed result::

            DEST  =  DEST - SRC;

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        cpu._SUB(dest, src, carry=False)

    def _SUB(cpu, dest, src, carry=False):
        size = dest.size
        minuend = dest.read()

        if src.size < dest.size:
            subtrahend = Operators.SEXTEND(src.read(), src.size, size)
        else:
            subtrahend = src.read()

        if carry:
            cv = Operators.ITEBV(size, cpu.CF, 1, 0)
            subtrahend += cv

        res = dest.write(minuend - subtrahend) & ((1 << size) - 1)
        cpu._calculate_CMP_flags(dest.size, res, minuend, subtrahend)

    @instruction
    def XADD(cpu, dest, src):
        """
        Exchanges and adds.

        Exchanges the first operand (destination operand) with the second operand
        (source operand), then loads the sum of the two values into the destination
        operand. The destination operand can be a register or a memory location;
        the source operand is a register.
        This instruction can be used with a LOCK prefix::

                TEMP  =  SRC + DEST
                SRC  =  DEST
                DEST  =  TEMP

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        MASK = (1 << dest.size) - 1
        SIGN_MASK = 1 << (dest.size - 1)

        arg0 = dest.read()
        arg1 = src.read()
        temp = (arg1 + arg0) & MASK
        src.write(arg0)
        dest.write(temp)

        # Affected flags: oszapc
        tempCF = Operators.OR(Operators.ULT(temp, arg0), Operators.ULT(temp, arg1))
        cpu.CF = tempCF
        cpu.AF = ((arg0 ^ arg1) ^ temp) & 0x10 != 0
        cpu.ZF = temp == 0
        cpu.SF = (temp & SIGN_MASK) != 0
        cpu.OF = (((arg0 ^ arg1 ^ SIGN_MASK) & (temp ^ arg1)) & SIGN_MASK) != 0
        cpu.PF = cpu._calculate_parity_flag(temp)

    ########################################################################################
    # Generic Operations
    ########################################################################################
    # Move: BSWAP, CMOVB, CMOVBE, CMOVL, CMOVLE, CMOVNB, CMOVNBE, CMOVNL, CMOVNLE,
    #       CMOVNO, CMOVNP, CMOVNS, CMOVNZ, CMOVO, CMOVP, CMOVS, CMOVZ, LAHF, LDS,
    #       LEA, LES, LFS, LGS, LSS, MOV, MOVBE, SAHF, SETB, SETBE,
    #       SETL, SETLE, SETNB, SETNBE, SETNL, SETNLE, SETNO, SETNP, SETNS, SETNZ,
    #       SETO, SETP, SETS, SETZ, XADD, XCHG, XLAT
    ########################################################################################
    @instruction
    def BSWAP(cpu, dest):
        """
        Byte swap.

        Reverses the byte order of a 32-bit (destination) register: bits 0 through
        7 are swapped with bits 24 through 31, and bits 8 through 15 are swapped
        with bits 16 through 23. This instruction is provided for converting little-endian
        values to big-endian format and vice versa.
        To swap bytes in a word value (16-bit register), use the XCHG instruction.
        When the BSWAP instruction references a 16-bit register, the result is
        undefined::

            TEMP  =  DEST
            DEST[7..0]  =  TEMP[31..24]
            DEST[15..8]  =  TEMP[23..16]
            DEST[23..16]  =  TEMP[15..8]
            DEST[31..24]  =  TEMP[7..0]

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        parts = []
        arg0 = dest.read()
        for i in range(0, dest.size, 8):
            parts.append(Operators.EXTRACT(arg0, i, 8))

        dest.write(Operators.CONCAT(8 * len(parts), *parts))

    ########################################################################################
    # Generic Operations -- Moves -- Conditional moves
    ########################################################################################
    #  Unsigned Conditional Moves: CMOVB CMOVNAE CMOVC CMOVB CMOVNBE CMOVA CMOVNB CMOVNC
    #                              CMOVAE CMOVNA CMOVBE CMOVNZ CMOVE CMOVNZ CMOVNE CMOVPE
    #                              CMOVP CMOVPO CMOVNP
    ########################################################################################
    # CMOVcc
    # CMOVB CMOVNAE CMOVC
    @instruction
    def CMOVB(cpu, dest, src):
        """
        Conditional move - Below/not above or equal.

        Tests the status flags in the EFLAGS register and moves the source operand
        (second operand) to the destination operand (first operand) if the given
        test condition is true.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.CF, src.read(), dest.read()))

    # CMOVNBE
    @instruction
    def CMOVA(cpu, dest, src):
        """
        Conditional move - Above/not below or equal.

        Tests the status flags in the EFLAGS register and moves the source operand
        (second operand) to the destination operand (first operand) if the given
        test condition is true.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        dest.write(
            Operators.ITEBV(
                dest.size, Operators.AND(cpu.CF == False, cpu.ZF == False), src.read(), dest.read()
            )
        )

    # CMOVNB CMOVNC
    @instruction
    def CMOVAE(cpu, dest, src):
        """
        Conditional move - Above or equal/not below.

        Tests the status flags in the EFLAGS register and moves the source operand
        (second operand) to the destination operand (first operand) if the given
        test condition is true.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.CF == False, src.read(), dest.read()))

    # CMOVNA
    @instruction
    def CMOVBE(cpu, dest, src):
        """
        Conditional move - Below or equal/not above.

        Tests the status flags in the EFLAGS register and moves the source operand
        (second operand) to the destination operand (first operand) if the given
        test condition is true.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        dest.write(
            Operators.ITEBV(dest.size, Operators.OR(cpu.CF, cpu.ZF), src.read(), dest.read())
        )

    @instruction
    def CMOVZ(cpu, dest, src):
        """
        Conditional move - Equal/zero.

        Tests the status flags in the EFLAGS register and moves the source operand
        (second operand) to the destination operand (first operand) if the given
        test condition is true.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.ZF, src.read(), dest.read()))

    @instruction
    def CMOVNZ(cpu, dest, src):
        """
        Conditional move - Not equal/not zero.

        Tests the status flags in the EFLAGS register and moves the source operand
        (second operand) to the destination operand (first operand) if the given
        test condition is true.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.ZF == False, src.read(), dest.read()))

    # CMOVPE
    @instruction
    def CMOVP(cpu, dest, src):
        """
        Conditional move - Parity/parity even.

        Tests the status flags in the EFLAGS register and moves the source operand
        (second operand) to the destination operand (first operand) if the given
        test condition is true.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.PF, src.read(), dest.read()))

    # CMOVPO

    @instruction
    def CMOVNP(cpu, dest, src):
        """
        Conditional move - Not parity/parity odd.

        Tests the status flags in the EFLAGS register and moves the source operand
        (second operand) to the destination operand (first operand) if the given
        test condition is true.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.PF == False, src.read(), dest.read()))

    ########################################################################################
    # Generic Operations -- Moves -- Signed Conditional Moves
    ########################################################################################
    #  Unsigned Conditional Moves: CMOVGE CMOVNL CMOVL CMOVNGE CMOVLE CMOVNG CMOVO CMOVNO
    #                              CMOVS CMOVNS
    ########################################################################################
    @instruction
    def CMOVG(cpu, dest, src):
        """
        Conditional move - Greater.

        Tests the status flags in the EFLAGS register and moves the source operand
        (second operand) to the destination operand (first operand) if the given
        test condition is true.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        dest.write(
            Operators.ITEBV(
                dest.size, Operators.AND(cpu.ZF == 0, cpu.SF == cpu.OF), src.read(), dest.read()
            )
        )

    # CMOVNL
    @instruction
    def CMOVGE(cpu, dest, src):
        """
        Conditional move - Greater or equal/not less.

        Tests the status flags in the EFLAGS register and moves the source operand
        (second operand) to the destination operand (first operand) if the given
        test condition is true.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        dest.write(Operators.ITEBV(dest.size, (cpu.SF ^ cpu.OF) == 0, src.read(), dest.read()))

    # CMOVNGE
    @instruction
    def CMOVL(cpu, dest, src):
        """
        Conditional move - Less/not greater or equal.

        Tests the status flags in the EFLAGS register and moves the source operand
        (second operand) to the destination operand (first operand) if the given
        test condition is true.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.SF ^ cpu.OF, src.read(), dest.read()))

    # CMOVNG
    @instruction
    def CMOVLE(cpu, dest, src):
        """
        Conditional move - Less or equal/not greater.

        Tests the status flags in the EFLAGS register and moves the source operand
        (second operand) to the destination operand (first operand) if the given
        test condition is true.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        dest.write(
            Operators.ITEBV(
                dest.size, Operators.OR(cpu.SF ^ cpu.OF, cpu.ZF), src.read(), dest.read()
            )
        )

    @instruction
    def CMOVO(cpu, dest, src):
        """
        Conditional move - Overflow.

        Tests the status flags in the EFLAGS register and moves the source operand
        (second operand) to the destination operand (first operand) if the given
        test condition is true.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.OF, src.read(), dest.read()))

    @instruction
    def CMOVNO(cpu, dest, src):
        """
        Conditional move - Not overflow.

        Tests the status flags in the EFLAGS register and moves the source operand
        (second operand) to the destination operand (first operand) if the given
        test condition is true.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.OF == False, src.read(), dest.read()))

    @instruction
    def CMOVS(cpu, dest, src):
        """
        Conditional move - Sign (negative).

        Tests the status flags in the EFLAGS register and moves the source operand
        (second operand) to the destination operand (first operand) if the given
        test condition is true.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.SF, src.read(), dest.read()))

    @instruction
    def CMOVNS(cpu, dest, src):
        """
        Conditional move - Not sign (non-negative).

        Tests the status flags in the EFLAGS register and moves the source operand
        (second operand) to the destination operand (first operand) if the given
        test condition is true.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.SF == False, src.read(), dest.read()))

    @instruction
    def LAHF(cpu):
        """
        Loads status flags into AH register.

        Moves the low byte of the EFLAGS register (which includes status flags
        SF, ZF, AF, PF, and CF) to the AH register. Reserved bits 1, 3, and 5
        of the EFLAGS register are set in the AH register::

                AH  =  EFLAGS(SF:ZF:0:AF:0:PF:1:CF);

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        used_regs = (cpu.SF, cpu.ZF, cpu.AF, cpu.PF, cpu.CF)
        is_expression = any(issymbolic(x) for x in used_regs)

        def make_flag(val, offset):
            if is_expression:
                return Operators.ITEBV(
                    size=8,
                    cond=val,
                    true_value=BitVecConstant(size=8, value=1 << offset),
                    false_value=BitVecConstant(size=8, value=0),
                )
            else:
                return val << offset

        cpu.AH = (
            make_flag(cpu.SF, 7)
            | make_flag(cpu.ZF, 6)
            | make_flag(0, 5)
            | make_flag(cpu.AF, 4)
            | make_flag(0, 3)
            | make_flag(cpu.PF, 2)
            | make_flag(1, 1)
            | make_flag(cpu.CF, 0)
        )

    @instruction
    def LDS(cpu, dest, src):
        """
        Not implemented.

        """
        raise NotImplementedError("LDS")  # TODO

    @instruction
    def LES(cpu, dest, src):
        """
        Not implemented.

        """
        raise NotImplementedError("LES")  # TODO

    @instruction
    def LFS(cpu, dest, src):
        """
        Not implemented.

        """
        raise NotImplementedError("LFS")  # TODO

    @instruction
    def LGS(cpu, dest, src):
        """
        Not implemented.

        """
        raise NotImplementedError("LGS")  # TODO

    @instruction
    def LSS(cpu, dest, src):
        """
        Loads far pointer.

        Loads a far pointer (segment selector and offset) from the second operand
        (source operand) into a segment register and the first operand (destination
        operand). The source operand specifies a 48-bit or a 32-bit pointer in
        memory depending on the current setting of the operand-size attribute
        (32 bits or 16 bits, respectively). The instruction opcode and the destination
        operand specify a segment register/general-purpose register pair. The
        16-bit segment selector from the source operand is loaded into the segment
        register specified with the opcode (DS, SS, ES, FS, or GS). The 32-bit
        or 16-bit offset is loaded into the register specified with the destination
        operand.
        In 64-bit mode, the instruction's default operation size is 32 bits. Using a
        REX prefix in the form of REX.W promotes operation to specify a source operand
        referencing an 80-bit pointer (16-bit selector, 64-bit offset) in memory.
        If one of these instructions is executed in protected mode, additional
        information from the segment descriptor pointed to by the segment selector
        in the source operand is loaded in the hidden part of the selected segment
        register.
        Also in protected mode, a null selector (values 0000 through 0003) can
        be loaded into DS, ES, FS, or GS registers without causing a protection
        exception. (Any subsequent reference to a segment whose corresponding
        segment register is loaded with a null selector, causes a general-protection
        exception (#GP) and no memory reference to the segment occurs.)::

                IF ProtectedMode
                THEN IF SS is loaded
                    THEN IF SegementSelector  =  null
                        THEN #GP(0);
                        FI;
                    ELSE IF Segment selector index is not within descriptor table limits
                        OR Segment selector RPL  CPL
                        OR Access rights indicate nonwritable data segment
                        OR DPL  CPL
                        THEN #GP(selector);
                        FI;
                    ELSE IF Segment marked not present
                        THEN #SS(selector);
                        FI;
                        SS  =  SegmentSelector(SRC);
                        SS  =  SegmentDescriptor([SRC]);
                    ELSE IF DS, ES, FS, or GS is loaded with non-null segment selector
                        THEN IF Segment selector index is not within descriptor table limits
                            OR Access rights indicate segment neither data nor readable code segment
                            OR Segment is data or nonconforming-code segment
                            AND both RPL and CPL > DPL)
                            THEN #GP(selector);
                            FI;
                        ELSE IF Segment marked not present
                            THEN #NP(selector);
                            FI;
                            SegmentRegister  =  SegmentSelector(SRC) AND RPL;
                            SegmentRegister  =  SegmentDescriptor([SRC]);
                        ELSE IF DS, ES, FS, or GS is loaded with a null selector:
                            SegmentRegister  =  NullSelector;
                            SegmentRegister(DescriptorValidBit)  =  0; (*hidden flag; not accessible by software*)
                        FI;
                    FI;
                    IF (Real-Address or Virtual-8086 Mode)
                    THEN
                        SegmentRegister  =  SegmentSelector(SRC);
                    FI;
                    DEST  =  Offset(SRC);
        """
        raise NotImplementedError("LSS")  # TODO

    @instruction
    def LEA(cpu, dest, src):
        """
        Loads effective address.

        Computes the effective address of the second operand (the source operand) and stores it in the first operand
        (destination operand). The source operand is a memory address (offset part) specified with one of the processors
        addressing modes; the destination operand is a general-purpose register. The address-size and operand-size
        attributes affect the action performed by this instruction. The operand-size
        attribute of the instruction is determined by the chosen register; the address-size attribute is determined by the
        attribute of the code segment.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        dest.write(Operators.EXTRACT(src.address(), 0, dest.size))

    @instruction
    def MOV(cpu, dest, src, *rest):  # Fake argument to work around capstone issue # 950
        """
        Move.

        Copies the second operand (source operand) to the first operand (destination
        operand). The source operand can be an immediate value, general-purpose
        register, segment register, or memory location; the destination register
        can be a general-purpose register, segment register, or memory location.
        Both operands must be the same size, which can be a byte, a word, or a
        doubleword.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        :param rest: workaround for a capstone bug, should never be provided
        """
        dest.write(src.read())

    @instruction
    def MOVBE(cpu, dest, src):
        """
        Moves data after swapping bytes.

        Performs a byte swap operation on the data copied from the second operand (source operand) and store the result
        in the first operand (destination operand). The source operand can be a general-purpose register, or memory location; the destination register can be a general-purpose register, or a memory location; however, both operands can
        not be registers, and only one operand can be a memory location. Both operands must be the same size, which can
        be a word, a doubleword or quadword.
        The MOVBE instruction is provided for swapping the bytes on a read from memory or on a write to memory; thus
        providing support for converting little-endian values to big-endian format and vice versa.
        In 64-bit mode, the instruction's default operation size is 32 bits. Use of the REX.R prefix permits access to additional registers (R8-R15). Use of the REX.W prefix promotes operation to 64 bits::

                TEMP = SRC
                IF ( OperandSize = 16)
                THEN
                    DEST[7:0] = TEMP[15:8];
                    DEST[15:8] = TEMP[7:0];
                ELSE IF ( OperandSize = 32)
                    DEST[7:0] = TEMP[31:24];
                    DEST[15:8] = TEMP[23:16];
                    DEST[23:16] = TEMP[15:8];
                    DEST[31:23] = TEMP[7:0];
                ELSE IF ( OperandSize = 64)
                    DEST[7:0] = TEMP[63:56];
                    DEST[15:8] = TEMP[55:48];
                    DEST[23:16] = TEMP[47:40];
                    DEST[31:24] = TEMP[39:32];
                    DEST[39:32] = TEMP[31:24];
                    DEST[47:40] = TEMP[23:16];
                    DEST[55:48] = TEMP[15:8];
                    DEST[63:56] = TEMP[7:0];
                FI;

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        size = dest.size
        arg0 = dest.read()
        temp = 0
        for pos in range(0, size, 8):
            temp = (temp << 8) | (arg0 & 0xFF)
            arg0 = arg0 >> 8
        dest.write(arg0)

    @instruction
    def SAHF(cpu):
        """
        Stores AH into flags.

        Loads the SF, ZF, AF, PF, and CF flags of the EFLAGS register with values
        from the corresponding bits in the AH register (bits 7, 6, 4, 2, and 0,
        respectively). Bits 1, 3, and 5 of register AH are ignored; the corresponding
        reserved bits (1, 3, and 5) in the EFLAGS register remain as shown below::

                EFLAGS(SF:ZF:0:AF:0:PF:1:CF)  =  AH;

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """

        eflags_size = 32
        val = cpu.AH & 0xD5 | 0x02

        cpu.EFLAGS = Operators.ZEXTEND(val, eflags_size)

    @instruction
    def SETA(cpu, dest):
        """
        Sets byte if above.

        Sets the destination operand to 0 or 1 depending on the settings of the status flags (CF, SF, OF, ZF, and PF, 1, 0) in the
        EFLAGS register. The destination operand points to a byte register or a byte in memory. The condition code suffix
        (cc, 1, 0) indicates the condition being tested for::
                IF condition
                THEN
                    DEST = 1;
                ELSE
                    DEST = 0;
                FI;

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, Operators.OR(cpu.CF, cpu.ZF) == False, 1, 0))

    @instruction
    def SETAE(cpu, dest):
        """
        Sets byte if above or equal.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.CF == False, 1, 0))

    @instruction
    def SETB(cpu, dest):
        """
        Sets byte if below.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.CF, 1, 0))

    @instruction
    def SETBE(cpu, dest):
        """
        Sets byte if below or equal.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, Operators.OR(cpu.CF, cpu.ZF), 1, 0))

    @instruction
    def SETC(cpu, dest):
        """
        Sets if carry.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.CF, 1, 0))

    @instruction
    def SETE(cpu, dest):
        """
        Sets byte if equal.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.ZF, 1, 0))

    @instruction
    def SETG(cpu, dest):
        """
        Sets byte if greater.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(
            Operators.ITEBV(dest.size, Operators.AND(cpu.ZF == False, cpu.SF == cpu.OF), 1, 0)
        )

    @instruction
    def SETGE(cpu, dest):
        """
        Sets byte if greater or equal.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.SF == cpu.OF, 1, 0))

    @instruction
    def SETL(cpu, dest):
        """
        Sets byte if less.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.SF != cpu.OF, 1, 0))

    @instruction
    def SETLE(cpu, dest):
        """
        Sets byte if less or equal.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, Operators.OR(cpu.ZF, cpu.SF != cpu.OF), 1, 0))

    @instruction
    def SETNA(cpu, dest):
        """
        Sets byte if not above.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, Operators.OR(cpu.CF, cpu.ZF), 1, 0))

    @instruction
    def SETNAE(cpu, dest):
        """
        Sets byte if not above or equal.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.CF, 1, 0))

    @instruction
    def SETNB(cpu, dest):
        """
        Sets byte if not below.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.CF == False, 1, 0))

    @instruction
    def SETNBE(cpu, dest):
        """
        Sets byte if not below or equal.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(
            Operators.ITEBV(dest.size, Operators.AND(cpu.CF == False, cpu.ZF == False), 1, 0)
        )

    @instruction
    def SETNC(cpu, dest):
        """
        Sets byte if not carry.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.CF == False, 1, 0))

    @instruction
    def SETNE(cpu, dest):
        """
        Sets byte if not equal.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.ZF == False, 1, 0))

    @instruction
    def SETNG(cpu, dest):
        """
        Sets byte if not greater.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, Operators.OR(cpu.ZF, cpu.SF != cpu.OF), 1, 0))

    @instruction
    def SETNGE(cpu, dest):
        """
        Sets if not greater or equal.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.SF != cpu.OF, 1, 0))

    @instruction
    def SETNL(cpu, dest):
        """
        Sets byte if not less.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.SF == cpu.OF, 1, 0))

    @instruction
    def SETNLE(cpu, dest):
        """
        Sets byte if not less or equal.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(
            Operators.ITEBV(dest.size, Operators.AND(cpu.ZF == False, cpu.SF == cpu.OF), 1, 0)
        )

    @instruction
    def SETNO(cpu, dest):
        """
        Sets byte if not overflow.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.OF == False, 1, 0))

    @instruction
    def SETNP(cpu, dest):
        """
        Sets byte if not parity.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.PF == False, 1, 0))

    @instruction
    def SETNS(cpu, dest):
        """
        Sets byte if not sign.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.SF == False, 1, 0))

    @instruction
    def SETNZ(cpu, dest):
        """
        Sets byte if not zero.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.ZF == False, 1, 0))

    @instruction
    def SETO(cpu, dest):
        """
        Sets byte if overflow.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.OF, 1, 0))

    @instruction
    def SETP(cpu, dest):
        """
        Sets byte if parity.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.PF, 1, 0))

    @instruction
    def SETPE(cpu, dest):
        """
        Sets byte if parity even.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.PF, 1, 0))

    @instruction
    def SETPO(cpu, dest):
        """
        Sets byte if parity odd.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.PF == False, 1, 0))

    @instruction
    def SETS(cpu, dest):
        """
        Sets byte if sign.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.SF, 1, 0))

    @instruction
    def SETZ(cpu, dest):
        """
        Sets byte if zero.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(Operators.ITEBV(dest.size, cpu.ZF, 1, 0))

    @instruction
    def XCHG(cpu, dest, src):
        """
        Exchanges register/memory with register.

        Exchanges the contents of the destination (first) and source (second)
        operands. The operands can be two general-purpose registers or a register
        and a memory location. If a memory operand is referenced, the processor's
        locking protocol is automatically implemented for the duration of the
        exchange operation, regardless of the presence or absence of the LOCK
        prefix or of the value of the IOPL.
        This instruction is useful for implementing semaphores or similar data
        structures for process synchronization.
        The XCHG instruction can also be used instead of the BSWAP instruction
        for 16-bit operands::

                TEMP  =  DEST
                DEST  =  SRC
                SRC  =  TEMP

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        temp = dest.read()
        dest.write(src.read())
        src.write(temp)

    ########################################################################################
    # Generic Operations
    ########################################################################################
    # Stack: LEAVE, POP, PUSH, POPF, PUSHF, INT
    #
    # Not Implemented: BOUND, ENTER, INT1, INTO, IRET, IRETD, POPA, POPAD, POPFD,
    #                  PUSHA, PUSHAD, PUSHFD
    ########################################################################################
    @instruction
    def LEAVE(cpu):
        """
        High level procedure exit.

        Releases the stack frame set up by an earlier ENTER instruction. The
        LEAVE instruction copies the frame pointer (in the EBP register) into
        the stack pointer register (ESP), which releases the stack space allocated
        to the stack frame. The old frame pointer (the frame pointer for the calling
        procedure that was saved by the ENTER instruction) is then popped from
        the stack into the EBP register, restoring the calling procedure's stack
        frame.
        A RET instruction is commonly executed following a LEAVE instruction
        to return program control to the calling procedure::

                IF Stackaddress_bit_size  =  32
                THEN
                    ESP  =  EBP;
                ELSE (* Stackaddress_bit_size  =  16*)
                    SP  =  BP;
                FI;
                IF OperandSize  =  32
                THEN
                    EBP  =  Pop();
                ELSE (* OperandSize  =  16*)
                    BP  =  Pop();
                FI;

        :param cpu: current CPU.
        """
        cpu.STACK = cpu.FRAME
        cpu.FRAME = cpu.pop(cpu.address_bit_size)

    @instruction
    def POP(cpu, dest):
        """
        Pops a value from the stack.

        Loads the value from the top of the stack to the location specified
        with the destination operand and then increments the stack pointer.

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        dest.write(cpu.pop(dest.size))

    @instruction
    def PUSH(cpu, src):
        """
        Pushes a value onto the stack.

        Decrements the stack pointer and then stores the source operand on the top of the stack.

        :param cpu: current CPU.
        :param src: source operand.
        """
        # http://stackoverflow.com/questions/11291151/how-push-imm-encodes
        size = src.size
        v = src.read()
        if size != 64 and size != cpu.address_bit_size // 2:
            v = Operators.SEXTEND(v, size, cpu.address_bit_size)
            size = cpu.address_bit_size
        cpu.push(v, size)

    @instruction
    def POPF(cpu):
        """
        Pops stack into EFLAGS register.

        :param cpu: current CPU.
        """
        mask = (
            0x00000001 | 0x00000004 | 0x00000010 | 0x00000040 | 0x00000080 | 0x00000400 | 0x00000800
        )
        val = cpu.pop(16)
        eflags_size = 32
        cpu.EFLAGS = Operators.ZEXTEND(val & mask, eflags_size)

    @instruction
    def POPFD(cpu):
        """
        Pops stack into EFLAGS register.

        :param cpu: current CPU.
        """
        mask = (
            0x00000001 | 0x00000004 | 0x00000010 | 0x00000040 | 0x00000080 | 0x00000400 | 0x00000800
        )
        cpu.EFLAGS = cpu.pop(32) & mask

    @instruction
    def POPFQ(cpu):
        """
        Pops stack into EFLAGS register.

        :param cpu: current CPU.
        """
        mask = (
            0x00000001 | 0x00000004 | 0x00000010 | 0x00000040 | 0x00000080 | 0x00000400 | 0x00000800
        )
        cpu.EFLAGS = (cpu.EFLAGS & ~mask) | cpu.pop(64) & mask

    @instruction
    def PUSHF(cpu):
        """
        Pushes FLAGS register onto the stack.

        :param cpu: current CPU.
        """
        cpu.push(cpu.EFLAGS, 16)

    @instruction
    def PUSHFD(cpu):
        """
        Pushes EFLAGS register onto the stack.

        :param cpu: current CPU.
        """
        cpu.push(cpu.EFLAGS, 32)

    @instruction
    def PUSHFQ(cpu):
        """
        Pushes RFLAGS register onto the stack.

        :param cpu: current CPU.
        """
        cpu.push(cpu.RFLAGS, 64)

    @instruction
    def INT(cpu, op0):
        """
        Calls to interrupt procedure.

        The INT n instruction generates a call to the interrupt or exception handler specified
        with the destination operand. The INT n instruction is the  general mnemonic for executing
        a software-generated call to an interrupt handler. The INTO instruction is a special
        mnemonic for calling overflow exception (#OF), interrupt vector number 4. The overflow
        interrupt checks the OF flag in the EFLAGS register and calls the overflow interrupt handler
        if the OF flag is set to 1.

        :param cpu: current CPU.
        :param op0: destination operand.
        """
        if op0.read() != 0x80:
            logger.warning("Unsupported interrupt")
        raise Interruption(op0.read())

    @instruction
    def INT3(cpu):
        """
        Breakpoint

        :param cpu: current CPU.
        """
        raise Interruption(3)

    ########################################################################################
    # Generic Operations
    ########################################################################################
    # Branch: CALL, RETN, JB, JBE, JCXZ, JECXZ, JL, JLE, JMP, JNB, JNBE, JNL, JNLE,
    #         JNO, JNP, JNS, JNZ, JO, JP, JS, JZ, LOOP, LOOPNZ, LOOPZ
    #
    # Not Implemented: CALLF, RETF, JMPF
    ########################################################################################
    @instruction
    def CALL(cpu, op0):
        """
        Procedure call.

        Saves procedure linking information on the stack and branches to the called procedure specified using the target
        operand. The target operand specifies the address of the first instruction in the called procedure. The operand can
        be an immediate value, a general-purpose register, or a memory location.

        :param cpu: current CPU.
        :param op0: target operand.
        """
        # TODO FIX 64Bit FIX segment
        proc = op0.read()
        cpu.push(cpu.PC, cpu.address_bit_size)
        cpu.PC = proc

    @instruction
    def RET(cpu, *operands):
        """
        Returns from procedure.

        Transfers program control to a return address located on the top of
        the stack. The address is usually placed on the stack by a CALL instruction,
        and the return is made to the instruction that follows the CALL instruction.
        The optional source operand specifies the number of stack bytes to be
        released after the return address is popped; the default is none.

        :param cpu: current CPU.
        :param operands: variable operands list.
        """
        # TODO FIX 64Bit FIX segment
        N = 0
        if len(operands) > 0:
            N = operands[0].read()
        cpu.PC = cpu.pop(cpu.address_bit_size)
        cpu.STACK += N

    @instruction
    def JA(cpu, target):
        """
        Jumps short if above.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(
            cpu.address_bit_size,
            Operators.AND(cpu.CF == False, cpu.ZF == False),
            target.read(),
            cpu.PC,
        )

    @instruction
    def JAE(cpu, target):
        """
        Jumps short if above or equal.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(cpu.address_bit_size, cpu.CF == False, target.read(), cpu.PC)

    @instruction
    def JB(cpu, target):
        """
        Jumps short if below.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(cpu.address_bit_size, cpu.CF == True, target.read(), cpu.PC)

    @instruction
    def JBE(cpu, target):
        """
        Jumps short if below or equal.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(
            cpu.address_bit_size, Operators.OR(cpu.CF, cpu.ZF), target.read(), cpu.PC
        )

    @instruction
    def JC(cpu, target):
        """
        Jumps short if carry.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(cpu.address_bit_size, cpu.CF, target.read(), cpu.PC)

    @instruction
    def JCXZ(cpu, target):
        """
        Jumps short if CX register is 0.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(cpu.address_bit_size, cpu.CX == 0, target.read(), cpu.PC)

    @instruction
    def JECXZ(cpu, target):
        """
        Jumps short if ECX register is 0.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(cpu.address_bit_size, cpu.ECX == 0, target.read(), cpu.PC)

    @instruction
    def JRCXZ(cpu, target):
        """
        Jumps short if RCX register is 0.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(cpu.address_bit_size, cpu.RCX == 0, target.read(), cpu.PC)

    @instruction
    def JE(cpu, target):
        """
        Jumps short if equal.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(cpu.address_bit_size, cpu.ZF, target.read(), cpu.PC)

    @instruction
    def JG(cpu, target):
        """
        Jumps short if greater.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(
            cpu.address_bit_size,
            Operators.AND(cpu.ZF == False, cpu.SF == cpu.OF),
            target.read(),
            cpu.PC,
        )

    @instruction
    def JGE(cpu, target):
        """
        Jumps short if greater or equal.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(cpu.address_bit_size, (cpu.SF == cpu.OF), target.read(), cpu.PC)

    @instruction
    def JL(cpu, target):
        """
        Jumps short if less.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(cpu.address_bit_size, (cpu.SF != cpu.OF), target.read(), cpu.PC)

    @instruction
    def JLE(cpu, target):
        """
        Jumps short if less or equal.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(
            cpu.address_bit_size, Operators.OR(cpu.ZF, cpu.SF != cpu.OF), target.read(), cpu.PC
        )

    @instruction
    def JNA(cpu, target):
        """
        Jumps short if not above.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(
            cpu.address_bit_size, Operators.OR(cpu.CF, cpu.ZF), target.read(), cpu.PC
        )

    @instruction
    def JNAE(cpu, target):
        """
        Jumps short if not above or equal.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(cpu.address_bit_size, cpu.CF, target.read(), cpu.PC)

    @instruction
    def JNB(cpu, target):
        """
        Jumps short if not below.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(cpu.address_bit_size, cpu.CF == False, target.read(), cpu.PC)

    @instruction
    def JNBE(cpu, target):
        """
        Jumps short if not below or equal.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(
            cpu.address_bit_size,
            Operators.AND(cpu.CF == False, cpu.ZF == False),
            target.read(),
            cpu.PC,
        )

    @instruction
    def JNC(cpu, target):
        """
        Jumps short if not carry.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(cpu.address_bit_size, False == cpu.CF, target.read(), cpu.PC)

    @instruction
    def JNE(cpu, target):
        """
        Jumps short if not equal.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(cpu.address_bit_size, False == cpu.ZF, target.read(), cpu.PC)

    @instruction
    def JNG(cpu, target):
        """
        Jumps short if not greater.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(
            cpu.address_bit_size, Operators.OR(cpu.ZF, cpu.SF != cpu.OF), target.read(), cpu.PC
        )

    @instruction
    def JNGE(cpu, target):
        """
        Jumps short if not greater or equal.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(cpu.address_bit_size, (cpu.SF != cpu.OF), target.read(), cpu.PC)

    @instruction
    def JNL(cpu, target):
        """
        Jumps short if not less.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(cpu.address_bit_size, (cpu.SF == cpu.OF), target.read(), cpu.PC)

    @instruction
    def JNLE(cpu, target):
        """
        Jumps short if not less or equal.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(
            cpu.address_bit_size,
            Operators.AND(False == cpu.ZF, cpu.SF == cpu.OF),
            target.read(),
            cpu.PC,
        )

    @instruction
    def JNO(cpu, target):
        """
        Jumps short if not overflow.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(cpu.address_bit_size, False == cpu.OF, target.read(), cpu.PC)

    @instruction
    def JNP(cpu, target):
        """
        Jumps short if not parity.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(cpu.address_bit_size, False == cpu.PF, target.read(), cpu.PC)

    @instruction
    def JNS(cpu, target):
        """
        Jumps short if not sign.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(cpu.address_bit_size, False == cpu.SF, target.read(), cpu.PC)

    def JNZ(cpu, target):
        """
        Jumps short if not zero.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.JNE(target)

    @instruction
    def JO(cpu, target):
        """
        Jumps short if overflow.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(cpu.address_bit_size, cpu.OF, target.read(), cpu.PC)

    @instruction
    def JP(cpu, target):
        """
        Jumps short if parity.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(cpu.address_bit_size, cpu.PF, target.read(), cpu.PC)

    @instruction
    def JPE(cpu, target):
        """
        Jumps short if parity even.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(cpu.address_bit_size, cpu.PF, target.read(), cpu.PC)

    @instruction
    def JPO(cpu, target):
        """
        Jumps short if parity odd.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(cpu.address_bit_size, False == cpu.PF, target.read(), cpu.PC)

    @instruction
    def JS(cpu, target):
        """
        Jumps short if sign.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(cpu.address_bit_size, cpu.SF, target.read(), cpu.PC)

    @instruction
    def JZ(cpu, target):
        """
        Jumps short if zero.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = Operators.ITEBV(cpu.address_bit_size, cpu.ZF, target.read(), cpu.PC)

    @instruction
    def JMP(cpu, target):
        """
        Jump.

        Transfers program control to a different point in the instruction stream without
        recording return information. The destination (target) operand specifies the address
        of the instruction being jumped to. This operand can be an immediate value, a general-purpose register, or a memory location.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        cpu.PC = target.read()

    def LJMP(cpu, cs_selector, target):
        """
        We are just going to ignore the CS selector for now.
        """
        logger.info("LJMP: Jumping to: %r:%r", cs_selector.read(), target.read())
        cpu.CS = cs_selector.read()
        cpu.PC = target.read()

    # LOOPZ
    def LOOP(cpu, dest):
        """
        Loops according to ECX counter.

        Performs a loop operation using the ECX or CX register as a counter.
        Each time the LOOP instruction is executed, the count register is decremented,
        then checked for 0. If the count is 0, the loop is terminated and program
        execution continues with the instruction following the LOOP instruction.
        If the count is not zero, a near jump is performed to the destination
        (target) operand, which is presumably the instruction at the beginning
        of the loop. If the address-size attribute is 32 bits, the ECX register
        is used as the count register; otherwise the CX register is used::

                IF address_bit_size  =  32
                THEN
                    Count is ECX;
                ELSE (* address_bit_size  =  16 *)
                    Count is CX;
                FI;
                Count  =  Count - 1;

                IF (Count  0)  =  1
                THEN
                    EIP  =  EIP + SignExtend(DEST);
                    IF OperandSize  =  16
                    THEN
                        EIP  =  EIP AND 0000FFFFH;
                    FI;
                ELSE
                    Terminate loop and continue program execution at EIP;
                FI;

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        counter_name = {16: "CX", 32: "ECX", 64: "RCX"}[cpu.address_bit_size]
        counter = cpu.write_register(counter_name, cpu.read_register(counter_name) - 1)
        cpu.PC = Operators.ITEBV(
            cpu.address_bit_size,
            counter == 0,
            (cpu.PC + dest.read()) & ((1 << dest.size) - 1),
            cpu.PC + cpu.instruction.size,
        )

    def LOOPNZ(cpu, target):
        """
        Loops if ECX counter is nonzero.

        :param cpu: current CPU.
        :param target: destination operand.
        """
        counter_name = {16: "CX", 32: "ECX", 64: "RCX"}[cpu.address_bit_size]
        counter = cpu.write_register(counter_name, cpu.read_register(counter_name) - 1)
        cpu.PC = Operators.ITEBV(
            cpu.address_bit_size,
            counter != 0,
            (cpu.PC + target.read()) & ((1 << target.size) - 1),
            cpu.PC + cpu.instruction.size,
        )

    ########################################################################################
    # Generic Operations
    ########################################################################################
    # Shifts: RCL, RCR, ROL, ROR, SAL, SAR, SHL, SHLD, SHR, SHRD
    #
    ########################################################################################

    @instruction
    def RCL(cpu, dest, src):
        """
        Rotates through carry left.

        Shifts (rotates) the bits of the first operand (destination operand) the number of bit positions specified in the
        second operand (count operand) and stores the result in the destination operand. The destination operand can be
        a register or a memory location; the count operand is an unsigned integer that can be an immediate or a value in
        the CL register. In legacy and compatibility mode, the processor restricts the count to a number between 0 and 31
        by masking all the bits in the count operand except the 5 least-significant bits.

        The RCL instruction shifts the CF flag into the least-significant bit and shifts the most-significant bit into the CF flag.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: count operand.
        """
        OperandSize = dest.size
        count = src.read()
        countMask = {8: 0x1F, 16: 0x1F, 32: 0x1F, 64: 0x3F}[OperandSize]
        tempCount = Operators.ZEXTEND((count & countMask) % (src.size + 1), OperandSize)

        value = dest.read()

        if isinstance(tempCount, int) and tempCount == 0:
            # this is a no-op
            new_val = value
            dest.write(new_val)
        else:
            carry = Operators.ITEBV(OperandSize, cpu.CF, 1, 0)
            right = value >> (OperandSize - tempCount)
            new_val = (value << tempCount) | (carry << (tempCount - 1)) | (right >> 1)
            dest.write(new_val)

            def sf(v, size):
                return (v & (1 << (size - 1))) != 0

            cpu.CF = sf(value << (tempCount - 1), OperandSize)
            cpu.OF = Operators.ITE(tempCount == 1, sf(new_val, OperandSize) != cpu.CF, cpu.OF)

    @instruction
    def RCR(cpu, dest, src):
        """
        Rotates through carry right (RCR).

        Shifts (rotates) the bits of the first operand (destination operand) the number of bit positions specified in the
        second operand (count operand) and stores the result in the destination operand. The destination operand can be
        a register or a memory location; the count operand is an unsigned integer that can be an immediate or a value in
        the CL register. In legacy and compatibility mode, the processor restricts the count to a number between 0 and 31
        by masking all the bits in the count operand except the 5 least-significant bits.

        Rotate through carry right (RCR) instructions shift all the bits toward less significant bit positions, except
        for the least-significant bit, which is rotated to the most-significant bit location. The RCR instruction shifts the
        CF flag into the most-significant bit and shifts the least-significant bit into the CF flag.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: count operand.
        """
        OperandSize = dest.size
        count = src.read()
        countMask = {8: 0x1F, 16: 0x1F, 32: 0x1F, 64: 0x3F}[OperandSize]
        tempCount = Operators.ZEXTEND((count & countMask) % (src.size + 1), OperandSize)

        value = dest.read()
        if isinstance(tempCount, int) and tempCount == 0:
            # this is a no-op
            new_val = value
            dest.write(new_val)
        else:
            carry = Operators.ITEBV(OperandSize, cpu.CF, 1, 0)
            left = value >> (tempCount - 1)
            right = value << (OperandSize - tempCount)

            new_val = (left >> 1) | (carry << (OperandSize - tempCount)) | (right << 1)

            dest.write(new_val)

            cpu.CF = Operators.ITE(tempCount != 0, (left & 1) == 1, cpu.CF)
            # for RCR these are calculated before rotation starts
            s_MSB = ((new_val >> (OperandSize - 1)) & 0x1) == 1
            s_MSB2 = ((new_val >> (OperandSize - 2)) & 0x1) == 1
            cpu.OF = Operators.ITE(tempCount == 1, s_MSB ^ s_MSB2, cpu.OF)

    @instruction
    def ROL(cpu, dest, src):
        """
        Rotates left (ROL).

        Shifts (rotates) the bits of the first operand (destination operand) the number of bit positions specified in the
        second operand (count operand) and stores the result in the destination operand. The destination operand can be
        a register or a memory location; the count operand is an unsigned integer that can be an immediate or a value in
        the CL register. In legacy and compatibility mode, the processor restricts the count to a number between 0 and 31
        by masking all the bits in the count operand except the 5 least-significant bits.

        The rotate left shift all the bits toward more-significant bit positions, except for the most-significant bit, which
        is rotated to the least-significant bit location.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: count operand.
        """
        OperandSize = dest.size
        count = src.read()
        countMask = {8: 0x1F, 16: 0x1F, 32: 0x1F, 64: 0x3F}[OperandSize]
        tempCount = Operators.ZEXTEND((count & countMask) % (OperandSize), OperandSize)

        value = dest.read()
        newValue = (value << tempCount) | (value >> (OperandSize - tempCount))
        dest.write(newValue)

        cpu.CF = Operators.ITE(tempCount != 0, (newValue & 1) == 1, cpu.CF)
        s_MSB = ((newValue >> (OperandSize - 1)) & 0x1) == 1
        cpu.OF = Operators.ITE(tempCount == 1, s_MSB ^ cpu.CF, cpu.OF)

    @instruction
    def ROR(cpu, dest, src):
        """
        Rotates right (ROR).

        Shifts (rotates) the bits of the first operand (destination operand) the number of bit positions specified in the
        second operand (count operand) and stores the result in the destination operand. The destination operand can be
        a register or a memory location; the count operand is an unsigned integer that can be an immediate or a value in
        the CL register. In legacy and compatibility mode, the processor restricts the count to a number between 0 and 31
        by masking all the bits in the count operand except the 5 least-significant bits.

        The rotate right (ROR) instruction shift all the bits toward less significant bit positions, except
        for the least-significant bit, which is rotated to the most-significant bit location.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: count operand.
        """
        OperandSize = dest.size
        count = src.read()
        countMask = {8: 0x1F, 16: 0x1F, 32: 0x1F, 64: 0x3F}[OperandSize]
        tempCount = Operators.ZEXTEND((count & countMask) % (OperandSize), OperandSize)

        value = dest.read()

        newValue = (value >> tempCount) | (value << (OperandSize - tempCount))
        dest.write(newValue)

        cpu.CF = Operators.ITE(tempCount != 0, ((newValue >> (OperandSize - 1)) & 0x1) == 1, cpu.CF)
        s_MSB = ((newValue >> (OperandSize - 1)) & 0x1) == 1
        s_MSB2 = ((newValue >> (OperandSize - 2)) & 0x1) == 1
        cpu.OF = Operators.ITE(tempCount == 1, s_MSB ^ s_MSB2, cpu.OF)

    @instruction
    def SAL(cpu, dest, src):
        """
        The shift arithmetic left.

        Shifts the bits in the first operand (destination operand) to the left or right by the number of bits specified in the
        second operand (count operand). Bits shifted beyond the destination operand boundary are first shifted into the CF
        flag, then discarded. At the end of the shift operation, the CF flag contains the last bit shifted out of the destination
        operand.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: count operand.
        """
        OperandSize = dest.size
        count = src.read()
        countMask = {8: 0x1F, 16: 0x1F, 32: 0x1F, 64: 0x3F}[OperandSize]
        tempCount = Operators.ZEXTEND(count & countMask, dest.size)

        tempDest = value = dest.read()
        res = dest.write(Operators.ITEBV(dest.size, tempCount == 0, tempDest, value << tempCount))

        # Should not modify flags if tempcount == 0
        MASK = (1 << OperandSize) - 1
        SIGN_MASK = 1 << (OperandSize - 1)

        cpu.CF = Operators.OR(
            Operators.AND(tempCount == 0, cpu.CF),
            Operators.AND(tempCount != 0, (tempDest & (1 << (OperandSize - tempCount)) != 0)),
        )
        # OF is only set iff count == 1, and set to XOR(CF, MSB(res))
        # OF is only defined for count == 1, but in practice (unit tests from real cpu) its calculated for count != 0
        cpu.OF = Operators.ITE(
            tempCount != 0, (cpu.CF) ^ (((res >> (OperandSize - 1)) & 0x1) == 1), cpu.OF
        )
        cpu.SF = Operators.OR(
            Operators.AND(tempCount == 0, cpu.SF),
            Operators.AND(tempCount != 0, (res & SIGN_MASK) != 0),
        )
        cpu.ZF = Operators.OR(
            Operators.AND(tempCount == 0, cpu.ZF), Operators.AND(tempCount != 0, res == 0)
        )
        cpu.PF = Operators.OR(
            Operators.AND(tempCount == 0, cpu.PF),
            Operators.AND(tempCount != 0, cpu._calculate_parity_flag(res)),
        )

    def SHL(cpu, dest, src):
        """
        The shift logical left.

        The shift arithmetic left (SAL) and shift logical left (SHL) instructions perform the same operation.

        :param cpu: current cpu.
        :param dest: destination operand.
        :param src: source operand.
        """
        return cpu.SAL(dest, src)

    @instruction
    def SAR(cpu, dest, src):
        """
        Shift arithmetic right.

        The shift arithmetic right (SAR) and shift logical right (SHR) instructions shift the bits of the destination operand to
        the right (toward less significant bit locations). For each shift count, the least significant bit of the destination
        operand is shifted into the CF flag, and the most significant bit is either set or cleared depending on the instruction
        type. The SHR instruction clears the most significant bit. the SAR instruction sets or clears the most significant bit
        to correspond to the sign (most significant bit) of the original value in the destination operand. In effect, the SAR
        instruction fills the empty bit position's shifted value with the sign of the unshifted value

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        OperandSize = dest.size
        countMask = {8: 0x1F, 16: 0x1F, 32: 0x1F, 64: 0x3F}[OperandSize]

        count = src.read() & countMask
        value = dest.read()

        res = Operators.SAR(OperandSize, value, Operators.ZEXTEND(count, OperandSize))
        dest.write(res)

        SIGN_MASK = 1 << (OperandSize - 1)

        # We can't use this one as the 'true' expression gets eagerly calculated even on count == 0		 +        cpu.CF = Operators.ITE(count!=0, ((value >> Operators.ZEXTEND(count-1, OperandSize)) & 1) !=0, cpu.CF)
        # cpu.CF = Operators.ITE(count!=0, ((value >> Operators.ZEXTEND(count-1, OperandSize)) & 1) !=0, cpu.CF)

        if issymbolic(count):
            # We can't use this one as the EXTRACT op needs the offset arguments to be concrete
            #    cpu.CF = Operators.ITE(count!=0, Operands.EXTRACT(value,count-1,1) !=0, cpu.CF)
            cpu.CF = Operators.ITE(
                Operators.AND(count != 0, count <= OperandSize),
                ((value >> Operators.ZEXTEND(count - 1, OperandSize)) & 1) != 0,
                cpu.CF,
            )
        else:
            if count != 0:
                if count > OperandSize:
                    count = OperandSize
                cpu.CF = Operators.EXTRACT(value, count - 1, 1) != 0

        # on count == 0 AF is unaffected, for count > 0, AF is undefined.
        # in either case, do not touch AF
        cpu.ZF = Operators.ITE(count != 0, res == 0, cpu.ZF)
        cpu.SF = Operators.ITE(count != 0, (res & SIGN_MASK) != 0, cpu.SF)
        cpu.OF = Operators.ITE(count == 1, False, cpu.OF)
        cpu.PF = Operators.ITE(count != 0, cpu._calculate_parity_flag(res), cpu.PF)

    @instruction
    def SHR(cpu, dest, src):
        """
        Shift logical right.

        The shift arithmetic right (SAR) and shift logical right (SHR)
        instructions shift the bits of the destination operand to the right
        (toward less significant bit locations). For each shift count, the
        least significant bit of the destination operand is shifted into the CF
        flag, and the most significant bit is either set or cleared depending
        on the instruction type. The SHR instruction clears the most
        significant bit.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: count operand.
        """
        OperandSize = dest.size
        count = Operators.ZEXTEND(src.read() & (OperandSize - 1), OperandSize)
        value = dest.read()

        res = dest.write(value >> count)  # UNSIGNED Operators.UDIV2 !! TODO Check

        MASK = (1 << OperandSize) - 1
        SIGN_MASK = 1 << (OperandSize - 1)

        if issymbolic(count):
            cpu.CF = Operators.ITE(
                count != 0, ((value >> Operators.ZEXTEND(count - 1, OperandSize)) & 1) != 0, cpu.CF
            )
        else:
            if count != 0:
                cpu.CF = Operators.EXTRACT(value, count - 1, 1) != 0

        cpu.ZF = Operators.ITE(count != 0, res == 0, cpu.ZF)
        cpu.SF = Operators.ITE(count != 0, (res & SIGN_MASK) != 0, cpu.SF)
        # OF is only defined for count == 1, but in practice (unit tests from real cpu) it's calculated for count != 0
        cpu.OF = Operators.ITE(count != 0, ((value >> (OperandSize - 1)) & 0x1) == 1, cpu.OF)
        cpu.PF = Operators.ITE(count != 0, cpu._calculate_parity_flag(res), cpu.PF)

    def _set_shiftd_flags(cpu, opsize, original, result, lastbit, count):

        MASK = (1 << opsize) - 1
        SIGN_MASK = 1 << (opsize - 1)

        # tempcount can be CL
        cpu.CF = Operators.OR(Operators.AND(cpu.CF, count == 0), Operators.AND(count != 0, lastbit))

        # on one bit shifts, OF is set if a sign change occurred, otherwise cleared
        # undefined for > 1 bit shifts
        signchange = (result & SIGN_MASK) != (original & SIGN_MASK)
        cpu.OF = Operators.ITE(count == 1, signchange, cpu.OF)

        cpu.PF = Operators.ITE(count == 0, cpu.PF, cpu._calculate_parity_flag(result))
        cpu.SF = Operators.ITE(count == 0, cpu.SF, (result & SIGN_MASK) != 0)
        cpu.ZF = Operators.ITE(count == 0, cpu.ZF, result == 0)

    @instruction
    def SHRD(cpu, dest, src, count):
        """
        Double precision shift right.

        Shifts the first operand (destination operand) to the right the number of bits specified by the third operand
        (count operand). The second operand (source operand) provides bits to shift in from the left (starting with
        the most significant bit of the destination operand).

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        :param count: count operand
        """
        OperandSize = dest.size
        MASK = (1 << OperandSize) - 1
        # count is masked based on destination size
        tempCount = Operators.ZEXTEND(count.read(), OperandSize) & (OperandSize - 1)
        if isinstance(tempCount, int) and tempCount == 0:
            pass
        else:
            arg0 = dest.read()
            arg1 = src.read()
            # do the shift
            res = Operators.ITEBV(
                OperandSize,
                tempCount == 0,
                arg0,
                (arg0 >> tempCount) | (arg1 << (dest.size - tempCount)),
            )
            res = res & MASK
            dest.write(res)
            lastbit = 0 != (arg0 >> (tempCount - 1)) & 1

            cpu._set_shiftd_flags(OperandSize, arg0, res, lastbit, tempCount)

    @instruction
    def SHLD(cpu, dest, src, count):
        """
        Double precision shift right.

        Shifts the first operand (destination operand) to the left the number of bits specified by the third operand
        (count operand). The second operand (source operand) provides bits to shift in from the right (starting with
        the least significant bit of the destination operand).

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        :param count: count operand
        """
        OperandSize = dest.size
        tempCount = Operators.ZEXTEND(count.read(), OperandSize) & (OperandSize - 1)
        arg0 = dest.read()
        arg1 = src.read()

        MASK = (1 << OperandSize) - 1
        t0 = arg0 << tempCount
        t1 = arg1 >> (OperandSize - tempCount)
        res = Operators.ITEBV(OperandSize, tempCount == 0, arg0, t0 | t1)
        res = res & MASK
        dest.write(res)
        if isinstance(tempCount, int) and tempCount == 0:
            pass
        else:
            SIGN_MASK = 1 << (OperandSize - 1)
            lastbit = 0 != ((arg0 << (tempCount - 1)) & SIGN_MASK)

            cpu._set_shiftd_flags(OperandSize, arg0, res, lastbit, tempCount)

    ########################################################################################
    # Generic Operations
    ########################################################################################
    # Bits: BSF, BSR, BT, BTC, BTR, BTS, POPCNT
    #
    ########################################################################################
    def _getMemoryBit(cpu, bitbase, bitoffset):
        """Calculate address and bit offset given a base address and a bit offset
        relative to that address (in the form of asm operands)"""
        assert bitbase.type == "memory"
        assert bitbase.size >= bitoffset.size
        addr = bitbase.address()
        offt = Operators.SEXTEND(bitoffset.read(), bitoffset.size, bitbase.size)
        offt_is_neg = offt >= (1 << (bitbase.size - 1))
        offt_in_bytes = offt // 8
        bitpos = offt % 8

        new_addr = addr + Operators.ITEBV(bitbase.size, offt_is_neg, -offt_in_bytes, offt_in_bytes)
        return (new_addr, bitpos)

    @instruction
    def BSF(cpu, dest, src):
        """
        Bit scan forward.

        Searches the source operand (second operand) for the least significant
        set bit (1 bit). If a least significant 1 bit is found, its bit index
        is stored in the destination operand (first operand). The source operand
        can be a register or a memory location; the destination operand is a register.
        The bit index is an unsigned offset from bit 0 of the source operand.
        If the contents source operand are 0, the contents of the destination
        operand is undefined::

                    IF SRC  =  0
                    THEN
                        ZF  =  1;
                        DEST is undefined;
                    ELSE
                        ZF  =  0;
                        temp  =  0;
                        WHILE Bit(SRC, temp)  =  0
                        DO
                            temp  =  temp + 1;
                            DEST  =  temp;
                        OD;
                    FI;

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        value = src.read()
        flag = Operators.EXTRACT(value, 0, 1) == 1
        res = 0
        for pos in range(1, src.size):
            res = Operators.ITEBV(dest.size, flag, res, pos)
            flag = Operators.OR(flag, Operators.EXTRACT(value, pos, 1) == 1)

        cpu.ZF = value == 0
        dest.write(Operators.ITEBV(dest.size, cpu.ZF, dest.read(), res))

    @instruction
    def BSR(cpu, dest, src):
        """
        Bit scan reverse.

        Searches the source operand (second operand) for the most significant
        set bit (1 bit). If a most significant 1 bit is found, its bit index is
        stored in the destination operand (first operand). The source operand
        can be a register or a memory location; the destination operand is a register.
        The bit index is an unsigned offset from bit 0 of the source operand.
        If the contents source operand are 0, the contents of the destination
        operand is undefined::

                IF SRC  =  0
                THEN
                    ZF  =  1;
                    DEST is undefined;
                ELSE
                    ZF  =  0;
                    temp  =  OperandSize - 1;
                    WHILE Bit(SRC, temp)  =  0
                    DO
                        temp  =  temp - 1;
                        DEST  =  temp;
                    OD;
                FI;

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        value = src.read()
        flag = Operators.EXTRACT(value, src.size - 1, 1) == 1
        res = 0

        for pos in reversed(range(0, src.size)):
            res = Operators.ITEBV(dest.size, flag, res, pos)
            flag = Operators.OR(flag, (Operators.EXTRACT(value, pos, 1) == 1))

        cpu.PF = cpu._calculate_parity_flag(res)
        cpu.ZF = value == 0
        dest.write(Operators.ITEBV(dest.size, cpu.ZF, dest.read(), res))

    @instruction
    def BT(cpu, dest, src):
        """
        Bit Test.

        Selects the bit in a bit string (specified with the first operand, called the bit base) at the
        bit-position designated by the bit offset (specified by the second operand) and stores the value
        of the bit in the CF flag. The bit base operand can be a register or a memory location; the bit
        offset operand can be a register or an immediate value:
            - If the bit base operand specifies a register, the instruction takes the modulo 16, 32, or 64
              of the bit offset operand (modulo size depends on the mode and register size; 64-bit operands
              are available only in 64-bit mode).
            - If the bit base operand specifies a memory location, the operand represents the address of the
              byte in memory that contains the bit base (bit 0 of the specified byte) of the bit string. The
              range of the bit position that can be referenced by the offset operand depends on the operand size.

        :param cpu: current CPU.
        :param dest: bit base.
        :param src: bit offset.
        """
        if dest.type == "register":
            cpu.CF = ((dest.read() >> (src.read() % dest.size)) & 1) != 0
        elif dest.type == "memory":
            addr, pos = cpu._getMemoryBit(dest, src)
            base, size, ty = cpu.get_descriptor(cpu.DS)
            value = cpu.read_int(addr + base, 8)
            cpu.CF = Operators.EXTRACT(value, pos, 1) == 1
        else:
            raise NotImplementedError(f"Unknown operand for BT: {dest.type}")

    @instruction
    def BTC(cpu, dest, src):
        """
        Bit test and complement.

        Selects the bit in a bit string (specified with the first operand, called
        the bit base) at the bit-position designated by the bit offset operand
        (second operand), stores the value of the bit in the CF flag, and complements
        the selected bit in the bit string.

        :param cpu: current CPU.
        :param dest: bit base operand.
        :param src: bit offset operand.
        """
        if dest.type == "register":
            value = dest.read()
            pos = src.read() % dest.size
            cpu.CF = value & (1 << pos) == 1 << pos
            dest.write(value ^ (1 << pos))
        elif dest.type == "memory":
            addr, pos = cpu._getMemoryBit(dest, src)
            base, size, ty = cpu.get_descriptor(cpu.DS)
            addr += base
            value = cpu.read_int(addr, 8)
            cpu.CF = value & (1 << pos) == 1 << pos
            value = value ^ (1 << pos)
            cpu.write_int(addr, value, 8)
        else:
            raise NotImplementedError(f"Unknown operand for BTC: {dest.type}")

    @instruction
    def BTR(cpu, dest, src):
        """
        Bit test and reset.

        Selects the bit in a bit string (specified with the first operand, called
        the bit base) at the bit-position designated by the bit offset operand
        (second operand), stores the value of the bit in the CF flag, and clears
        the selected bit in the bit string to 0.

        :param cpu: current CPU.
        :param dest: bit base operand.
        :param src: bit offset operand.
        """
        if dest.type == "register":
            value = dest.read()
            pos = src.read() % dest.size
            cpu.CF = value & (1 << pos) == 1 << pos
            dest.write(value & ~(1 << pos))
        elif dest.type == "memory":
            addr, pos = cpu._getMemoryBit(dest, src)
            base, size, ty = cpu.get_descriptor(cpu.DS)
            addr += base
            value = cpu.read_int(addr, 8)
            cpu.CF = value & (1 << pos) == 1 << pos
            value = value & ~(1 << pos)
            cpu.write_int(addr, value, 8)
        else:
            raise NotImplementedError(f"Unknown operand for BTR: {dest.type}")

    @instruction
    def BTS(cpu, dest, src):
        """
        Bit test and set.

        Selects the bit in a bit string (specified with the first operand, called
        the bit base) at the bit-position designated by the bit offset operand
        (second operand), stores the value of the bit in the CF flag, and sets
        the selected bit in the bit string to 1.

        :param cpu: current CPU.
        :param dest: bit base operand.
        :param src: bit offset operand.
        """

        if dest.type == "register":
            value = dest.read()
            pos = src.read() % dest.size
            cpu.CF = value & (1 << pos) == 1 << pos
            dest.write(value | (1 << pos))
        elif dest.type == "memory":
            addr, pos = cpu._getMemoryBit(dest, src)
            base, size, ty = cpu.get_descriptor(cpu.DS)
            addr += base
            # read from addr
            value = cpu.read_int(addr, 8)
            cpu.CF = value & (1 << pos) == 1 << pos
            value = value | (1 << pos)
            cpu.write_int(addr, value, 8)
        else:
            raise NotImplementedError(f"Unknown operand for BTS: {dest.type}")

    @instruction
    def POPCNT(cpu, dest, src):
        """
        This instruction calculates of number of bits set to 1 in the second
        operand (source) and returns the count in the first operand (a destination
        register).
        Count = 0;
        For (i=0; i < OperandSize; i++) {
            IF (SRC[ i] = 1) // i'th bit
                THEN Count++;
            FI;
        }
        DEST = Count;
        Flags Affected
        OF, SF, ZF, AF, CF, PF are all cleared.
        ZF is set if SRC = 0, otherwise ZF is cleared
        """
        count = 0
        source = src.read()
        for i in range(src.size):
            count += Operators.ITEBV(dest.size, (source >> i) & 1 == 1, 1, 0)
        dest.write(count)
        # Flags
        cpu.OF = False
        cpu.SF = False
        cpu.AF = False
        cpu.CF = False
        cpu.PF = False
        cpu.ZF = source == 0

    ########################################################################################
    # Flag Operations
    ########################################################################################
    # Bits: STD, CLD, STC, CLC,
    #
    ########################################################################################

    @instruction
    def CLD(cpu):
        """
        Clears direction flag.
        Clears the DF flag in the EFLAGS register. When the DF flag is set to 0, string operations
        increment the index registers (ESI and/or EDI)::

            DF  =  0;

        :param cpu: current CPU.
        """
        cpu.DF = False

    @instruction
    def STD(cpu):
        """
        Sets direction flag.

        Sets the DF flag in the EFLAGS register. When the DF flag is set to 1, string operations decrement
        the index registers (ESI and/or EDI)::

            DF  =  1;

        :param cpu: current CPU.
        """
        cpu.DF = True

    @instruction
    def CLC(cpu):
        """
        Clears CF
        :param cpu: current CPU.
        """
        cpu.CF = False

    @instruction
    def STC(cpu):
        """
        Sets CF
        :param cpu: current CPU.
        """
        cpu.CF = True

    ########################################################################################
    # Generic Operations
    ########################################################################################
    # Bits: CMPS, INS, LODS, MOVS, OUTS, SCAS, STOS
    #
    ########################################################################################
    @repe
    def CMPS(cpu, dest, src):
        """
        Compares string operands.

        Compares the byte, word, double word or quad specified with the first source
        operand with the byte, word, double or quad word specified with the second
        source operand and sets the status flags in the EFLAGS register according
        to the results. Both the source operands are located in memory::

                temp  = SRC1 - SRC2;
                SetStatusFlags(temp);
                IF (byte comparison)
                THEN IF DF  =  0
                    THEN
                        (E)SI  =  (E)SI + 1;
                        (E)DI  =  (E)DI + 1;
                    ELSE
                        (E)SI  =  (E)SI - 1;
                        (E)DI  =  (E)DI - 1;
                    FI;
                ELSE IF (word comparison)
                    THEN IF DF  =  0
                        (E)SI  =  (E)SI + 2;
                        (E)DI  =  (E)DI + 2;
                    ELSE
                        (E)SI  =  (E)SI - 2;
                        (E)DI  =  (E)DI - 2;
                    FI;
                ELSE (* doubleword comparison*)
                    THEN IF DF  =  0
                        (E)SI  =  (E)SI + 4;
                        (E)DI  =  (E)DI + 4;
                    ELSE
                        (E)SI  =  (E)SI - 4;
                        (E)DI  =  (E)DI - 4;
                    FI;
                FI;

        :param cpu: current CPU.
        :param dest: first source operand.
        :param src: second source operand.
        """
        src_reg = {8: "SI", 32: "ESI", 64: "RSI"}[cpu.address_bit_size]
        dest_reg = {8: "DI", 32: "EDI", 64: "RDI"}[cpu.address_bit_size]

        base, _, ty = cpu.get_descriptor(cpu.DS)

        src_addr = cpu.read_register(src_reg) + base
        dest_addr = cpu.read_register(dest_reg) + base
        size = dest.size

        # Compare
        arg1 = cpu.read_int(dest_addr, size)
        arg0 = cpu.read_int(src_addr, size)
        res = (arg0 - arg1) & ((1 << size) - 1)

        cpu._calculate_CMP_flags(size, res, arg0, arg1)

        # Advance EDI/ESI pointers
        increment = Operators.ITEBV(cpu.address_bit_size, cpu.DF, -size // 8, size // 8)
        cpu.write_register(src_reg, cpu.read_register(src_reg) + increment)
        cpu.write_register(dest_reg, cpu.read_register(dest_reg) + increment)

    @rep
    def LODS(cpu, dest, src):
        """
        Loads string.

        Loads a byte, word, or doubleword from the source operand into the AL, AX, or EAX register, respectively. The
        source operand is a memory location, the address of which is read from the DS:ESI or the DS:SI registers
        (depending on the address-size attribute of the instruction, 32 or 16, respectively). The DS segment may be over-
        ridden with a segment override prefix.
        After the byte, word, or doubleword is transferred from the memory location into the AL, AX, or EAX register, the
        (E)SI register is incremented or decremented automatically according to the setting of the DF flag in the EFLAGS
        register. (If the DF flag is 0, the (E)SI register is incremented; if the DF flag is 1, the ESI register is decremented.)
        The (E)SI register is incremented or decremented by 1 for byte operations, by 2 for word operations, or by 4 for
        doubleword operations.

        :param cpu: current CPU.
        :param dest: source operand.
        """
        src_reg = {8: "SI", 32: "ESI", 64: "RSI"}[cpu.address_bit_size]
        base, _, ty = cpu.get_descriptor(cpu.DS)

        src_addr = cpu.read_register(src_reg) + base
        size = dest.size

        arg0 = cpu.read_int(src_addr, size)
        dest.write(arg0)

        increment = Operators.ITEBV(cpu.address_bit_size, cpu.DF, -size // 8, size // 8)
        cpu.write_register(src_reg, cpu.read_register(src_reg) + increment)

    @rep
    def MOVS(cpu, dest, src):
        """
        Moves data from string to string.

        Moves the byte, word, or doubleword specified with the second operand (source operand) to the location specified
        with the first operand (destination operand). Both the source and destination operands are located in memory. The
        address of the source operand is read from the DS:ESI or the DS:SI registers (depending on the address-size
        attribute of the instruction, 32 or 16, respectively). The address of the destination operand is read from the ES:EDI
        or the ES:DI registers (again depending on the address-size attribute of the instruction). The DS segment may be
        overridden with a segment override prefix, but the ES segment cannot be overridden.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        base, size, ty = cpu.get_descriptor(cpu.DS)
        src_addr = src.address() + base
        dest_addr = dest.address() + base

        src_reg = src.mem.base
        dest_reg = dest.mem.base
        size = dest.size

        # Copy the data
        dest.write(src.read())

        # Advance EDI/ESI pointers
        increment = Operators.ITEBV(cpu.address_bit_size, cpu.DF, -size // 8, size // 8)
        cpu.write_register(src_reg, cpu.read_register(src_reg) + increment)
        cpu.write_register(dest_reg, cpu.read_register(dest_reg) + increment)

    @repe
    def SCAS(cpu, dest, src):
        """
        Scans String.

        Compares the byte, word, or double word specified with the memory operand
        with the value in the AL, AX, EAX, or RAX register, and sets the status flags
        according to the results. The memory operand address is read from either
        the ES:RDI, ES:EDI or the ES:DI registers (depending on the address-size
        attribute of the instruction, 32 or 16, respectively)::

                IF (byte comparison)
                THEN
                    temp  =  AL - SRC;
                    SetStatusFlags(temp);
                    THEN IF DF  =  0
                        THEN (E)DI  =  (E)DI + 1;
                        ELSE (E)DI  =  (E)DI - 1;
                        FI;
                    ELSE IF (word comparison)
                        THEN
                            temp  =  AX - SRC;
                            SetStatusFlags(temp)
                            THEN IF DF  =  0
                                THEN (E)DI  =  (E)DI + 2;
                                ELSE (E)DI  =  (E)DI - 2;
                                FI;
                     ELSE (* doubleword comparison *)
                           temp  =  EAX - SRC;
                           SetStatusFlags(temp)
                           THEN IF DF  =  0
                                THEN
                                    (E)DI  =  (E)DI + 4;
                                ELSE
                                    (E)DI  =  (E)DI - 4;
                                FI;
                           FI;
                     FI;

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        dest_reg = dest.reg
        mem_reg = src.mem.base  # , src.type, src.read()
        size = dest.size
        arg0 = dest.read()
        arg1 = src.read()
        res = arg0 - arg1
        cpu._calculate_CMP_flags(size, res, arg0, arg1)

        increment = Operators.ITEBV(cpu.address_bit_size, cpu.DF, -size // 8, size // 8)
        cpu.write_register(mem_reg, cpu.read_register(mem_reg) + increment)

    @rep
    def STOS(cpu, dest, src):
        """
        Stores String.

        Stores a byte, word, or doubleword from the AL, AX, or EAX register,
        respectively, into the destination operand. The destination operand is
        a memory location, the address of which is read from either the ES:EDI
        or the ES:DI registers (depending on the address-size attribute of the
        instruction, 32 or 16, respectively). The ES segment cannot be overridden
        with a segment override prefix.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        size = src.size
        dest.write(src.read())
        dest_reg = dest.mem.base
        increment = Operators.ITEBV(
            {"RDI": 64, "EDI": 32, "DI": 16}[dest_reg], cpu.DF, -size // 8, size // 8
        )
        cpu.write_register(dest_reg, cpu.read_register(dest_reg) + increment)

    ########################################################################################
    # MMX Operations
    ########################################################################################
    # State Management: EMMS
    #
    ########################################################################################
    @instruction
    def EMMS(cpu):
        """
        Empty MMX Technology State

        Sets the values of all the tags in the x87 FPU tag word to empty (all
        1s). This operation marks the x87 FPU data registers (which are aliased
        to the MMX technology registers) as available for use by x87 FPU
        floating-point instructions.

            x87FPUTagWord <- FFFFH;
        """
        cpu.FPTAG = 0xFFFF

    # @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@
    # @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@
    # @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@
    # @@@@@@@@@@@@@@@@@ compulsive coding after this @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@
    @instruction
    def STMXCSR(cpu, dest):
        """Store MXCSR Register State
        Stores the contents of the MXCSR control and status register to the destination operand.
        The destination operand is a 32-bit memory location. The reserved bits in the MXCSR register
        are stored as 0s."""
        dest.write(0x1F80)

    @instruction
    def PAUSE(cpu):
        pass

    @instruction
    def ANDN(cpu, dest, src1, src2):
        """Performs a bitwise logical AND of inverted second operand (the first source operand)
        with the third operand (the second source operand). The result is stored in the first
        operand (destination operand).

             DEST <- (NOT SRC1) bitwiseAND SRC2;
             SF <- DEST[OperandSize -1];
             ZF <- (DEST = 0);
        Flags Affected
             SF and ZF are updated based on result. OF and CF flags are cleared. AF and PF flags are undefined.
        """
        value = ~src1.read() & src2.read()
        dest.write(value)
        cpu.ZF = value == 0
        cpu.SF = (value & (1 << dest.size)) != 0
        cpu.OF = False
        cpu.CF = False

    @instruction
    def SHLX(cpu, dest, src, count):
        """
        The shift arithmetic left.

        Shifts the bits in the first operand (destination operand) to the left or right by the number of bits specified in the
        second operand (count operand). Bits shifted beyond the destination operand boundary are first shifted into the CF
        flag, then discarded. At the end of the shift operation, the CF flag contains the last bit shifted out of the destination
        operand.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: count operand.
        """
        OperandSize = dest.size
        count = count.read()
        countMask = {8: 0x1F, 16: 0x1F, 32: 0x1F, 64: 0x3F}[OperandSize]
        tempCount = Operators.ZEXTEND(count & countMask, dest.size)
        tempDest = value = src.read()
        res = dest.write(Operators.ITEBV(dest.size, tempCount == 0, tempDest, value << tempCount))

    @instruction
    def SHRX(cpu, dest, src, count):
        """
        The shift arithmetic right.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: count operand.
        """
        OperandSize = dest.size
        count = count.read()
        countMask = {8: 0x1F, 16: 0x1F, 32: 0x1F, 64: 0x3F}[OperandSize]
        tempCount = Operators.ZEXTEND(count & countMask, dest.size)
        tempDest = value = src.read()
        res = dest.write(Operators.ITEBV(dest.size, tempCount == 0, tempDest, value >> tempCount))

    @instruction
    def SARX(cpu, dest, src, count):
        """
        The shift arithmetic right.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: count operand.
        """
        OperandSize = dest.size
        count = count.read()
        countMask = {8: 0x1F, 16: 0x1F, 32: 0x1F, 64: 0x3F}[OperandSize]
        tempCount = count & countMask
        tempDest = value = src.read()

        sign = value & (1 << (OperandSize - 1))
        while tempCount != 0:
            cpu.CF = (value & 0x1) != 0  # LSB
            value = (value >> 1) | sign
            tempCount = tempCount - 1
        res = dest.write(value)

    @instruction
    def PMINUB(cpu, dest, src):
        """
        PMINUB: returns minimum of packed unsigned byte integers in the dest operand
        see PMAXUB
        """
        dest_value = dest.read()
        src_value = src.read()
        result = 0
        for pos in range(0, dest.size, 8):
            itema = (dest_value >> pos) & 0xFF
            itemb = (src_value >> pos) & 0xFF
            result |= Operators.ITEBV(dest.size, itema < itemb, itema, itemb) << pos
        dest.write(result)

    @instruction
    def PMAXUB(cpu, dest, src):
        """
        PMAXUB: returns maximum of packed unsigned byte integers in the dest operand

        Performs a SIMD compare of the packed unsigned byte in the second source operand
        and the first source operand and returns the maximum value for each pair of
        integers to the destination operand.

        Example :
        $xmm1.v16_int8 = {..., 0xf2, 0xd1}
        $xmm2.v16_int8 = {..., 0xd2, 0xf1}
        # after pmaxub xmm1, xmm2, we get
        $xmm1.v16_int8 = {..., 0xf2, 0xf1}
        """
        dest_value = dest.read()
        src_value = src.read()
        result = 0
        for pos in range(0, dest.size, 8):
            itema = (dest_value >> pos) & 0xFF
            itemb = (src_value >> pos) & 0xFF
            result |= Operators.ITEBV(dest.size, itema > itemb, itema, itemb) << pos
        dest.write(result)

    @instruction
    def VPXOR(cpu, dest, arg0, arg1):
        res = dest.write(arg0.read() ^ arg1.read())

    @instruction
    def PXOR(cpu, dest, src):
        """
        Logical exclusive OR.

        Performs a bitwise logical exclusive-OR (XOR) operation on the quadword
        source (second) and destination (first) operands and stores the result
        in the destination operand location. The source operand can be an MMX(TM)
        technology register or a quadword memory location; the destination operand
        must be an MMX register. Each bit of the result is 1 if the corresponding
        bits of the two operands are different; each bit is 0 if the corresponding
        bits of the operands are the same::

            DEST  =  DEST XOR SRC;

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: quadword source operand.
        """
        res = dest.write(dest.read() ^ src.read())

    def _PUNPCKL(cpu, dest, src, item_size):
        """
        Generic PUNPCKL
        """
        assert dest.size == src.size
        size = dest.size
        dest_value = dest.read()
        src_value = src.read()
        mask = (1 << item_size) - 1
        res = 0
        count = 0
        for pos in range(0, size // item_size):
            if count >= size:
                break
            item0 = Operators.ZEXTEND((dest_value >> (pos * item_size)) & mask, size)
            item1 = Operators.ZEXTEND((src_value >> (pos * item_size)) & mask, size)
            res |= item0 << count
            count += item_size
            res |= item1 << count
            count += item_size

        dest.write(res)

    def _PUNPCKH(cpu, dest, src, item_size):
        """
        Generic PUNPCKH
        """
        assert dest.size == src.size
        size = dest.size
        dest_value = dest.read()
        src_value = src.read()
        mask = (1 << item_size) - 1
        res = 0
        count = 0
        for pos in reversed(range(0, size // item_size)):
            if count >= size:
                break
            item0 = Operators.ZEXTEND((dest_value >> (pos * item_size)) & mask, size)
            item1 = Operators.ZEXTEND((src_value >> (pos * item_size)) & mask, size)
            res = res << item_size
            res |= item1
            res = res << item_size
            res |= item0
            count += item_size * 2

        dest.write(res)

    @instruction
    def PUNPCKHBW(cpu, dest, src):
        cpu._PUNPCKH(dest, src, 8)

    @instruction
    def PUNPCKHWD(cpu, dest, src):
        cpu._PUNPCKH(dest, src, 16)

    @instruction
    def PUNPCKHDQ(cpu, dest, src):
        cpu._PUNPCKH(dest, src, 32)

    @instruction
    def PUNPCKHQDQ(cpu, dest, src):
        cpu._PUNPCKH(dest, src, 64)

    @instruction
    def PUNPCKLBW(cpu, dest, src):
        """
        Interleaves the low-order bytes of the source and destination operands.

        Unpacks and interleaves the low-order data elements (bytes, words, doublewords, and quadwords)
        of the destination operand (first operand) and source operand (second operand) into the
        destination operand.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        cpu._PUNPCKL(dest, src, 8)

    @instruction
    def PUNPCKLWD(cpu, dest, src):
        """
        Interleaves the low-order bytes of the source and destination operands.

        Unpacks and interleaves the low-order data elements (bytes, words, doublewords, and quadwords)
        of the destination operand (first operand) and source operand (second operand) into the
        destination operand.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        cpu._PUNPCKL(dest, src, 16)

    @instruction
    def PUNPCKLQDQ(cpu, dest, src):
        """
        Interleaves the low-order quad-words of the source and destination operands.

        Unpacks and interleaves the low-order data elements (bytes, words, doublewords, and quadwords)
        of the destination operand (first operand) and source operand (second operand) into the
        destination operand.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        cpu._PUNPCKL(dest, src, 64)

    @instruction
    def PUNPCKLDQ(cpu, dest, src):
        """
        Interleaves the low-order double-words of the source and destination operands.

        Unpacks and interleaves the low-order data elements (bytes, words, doublewords, and quadwords)
        of the destination operand (first operand) and source operand (second operand) into the
        destination operand.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        cpu._PUNPCKL(dest, src, 32)

    @instruction
    def PSHUFW(cpu, op0, op1, op3):
        """
        Packed shuffle words.

        Copies doublewords from source operand (second operand) and inserts them in the destination operand
        (first operand) at locations selected with the order operand (third operand).

        :param cpu: current CPU.
        :param op0: destination operand.
        :param op1: source operand.
        :param op3: order operand.
        """
        size = op0.size
        arg0 = op0.read()
        arg1 = op1.read()
        arg3 = Operators.ZEXTEND(op3.read(), size)
        assert size == 64
        arg0 |= (arg1 >> ((arg3 >> 0) & 3 * 16)) & 0xFFFF
        arg0 |= ((arg1 >> ((arg3 >> 2) & 3 * 16)) & 0xFFFF) << 16
        arg0 |= ((arg1 >> ((arg3 >> 4) & 3 * 16)) & 0xFFFF) << 32
        arg0 |= ((arg1 >> ((arg3 >> 6) & 3 * 16)) & 0xFFFF) << 48
        op0.write(arg0)

    @instruction
    def PSHUFLW(cpu, op0, op1, op3):
        """
        Shuffle Packed Low Words

        Copies words from the low quadword of the source operand (second operand)
        and inserts them in the low quadword of the destination operand (first operand)
        at word locations selected with the order operand (third operand).

        This operation is similar to the operation used by the PSHUFD instruction.

            Operation
            Destination[0..15] = (Source >> (Order[0..1] * 16))[0..15];
            Destination[16..31] = (Source >> (Order[2..3] * 16))[0..15];
            Destination[32..47] = (Source >> (Order[4..5] * 16))[0..15];
            Destination[48..63] = (Source >> (Order[6..7] * 16))[0..15];
            Destination[64..127] = Source[64..127];
        """
        size = op0.size
        arg0 = op0.read()
        arg1 = op1.read()
        arg3 = Operators.ZEXTEND(op3.read(), size)
        arg0 = arg1 & 0xFFFFFFFFFFFFFFFF0000000000000000
        arg0 |= (arg1 >> (((arg3 >> 0) & 3) * 16)) & 0xFFFF
        arg0 |= ((arg1 >> (((arg3 >> 2) & 3) * 16)) & 0xFFFF) << 16
        arg0 |= ((arg1 >> (((arg3 >> 4) & 3) * 16)) & 0xFFFF) << 32
        arg0 |= ((arg1 >> (((arg3 >> 6) & 3) * 16)) & 0xFFFF) << 48

        op0.write(arg0)

    @instruction
    def PSHUFD(cpu, op0, op1, op3):
        """
        Packed shuffle doublewords.

        Copies doublewords from source operand (second operand) and inserts them in the destination operand
        (first operand) at locations selected with the order operand (third operand).

        :param cpu: current CPU.
        :param op0: destination operand.
        :param op1: source operand.
        :param op3: order operand.
        """
        size = op0.size
        arg0 = op0.read()
        arg1 = op1.read()
        order = Operators.ZEXTEND(op3.read(), size)

        arg0 = arg0 & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000
        arg0 |= (arg1 >> (((order >> 0) & 3) * 32)) & 0xFFFFFFFF
        arg0 |= ((arg1 >> (((order >> 2) & 3) * 32)) & 0xFFFFFFFF) << 32
        arg0 |= ((arg1 >> (((order >> 4) & 3) * 32)) & 0xFFFFFFFF) << 64
        arg0 |= ((arg1 >> (((order >> 6) & 3) * 32)) & 0xFFFFFFFF) << 96

        op0.write(arg0)

    @instruction
    def MOVDQU(cpu, op0, op1):
        """
        Moves unaligned double quadword.

        Moves a double quadword from the source operand (second operand) to the destination operand
        (first operand)::

            OP0  =  OP1;

        :param cpu: current CPU.
        :param op0: destination operand.
        :param op1: source operand.
        """

        op0.write(op1.read())

    @instruction
    def MOVDQA(cpu, op0, op1):
        """
        Moves aligned double quadword.

        Moves a double quadword from the source operand (second operand) to the destination operand
        (first operand)::
            OP0  =  OP1;

        :param cpu: current CPU.
        :param op0: destination operand.
        :param op1: source operand.
        @todo: check alignment.
        """
        op0.write(op1.read())

    @instruction
    def PCMPEQB(cpu, op0, op1):
        """
        Packed compare for equal.

        Performs a SIMD compare for equality of the packed bytes, words, or doublewords in the
        destination operand (first operand) and the source operand (second operand). If a pair of
        data elements are equal, the corresponding data element in the destination operand is set
        to all 1s; otherwise, it is set to all 0s. The source operand can be an MMX(TM) technology
        register or a 64-bit memory location, or it can be an XMM register or a 128-bit memory location.
        The destination operand can be an MMX or an XMM register.
        The PCMPEQB instruction compares the bytes in the destination operand to the corresponding bytes
        in the source operand.

        :param cpu: current CPU.
        :param op0: destination operand.
        :param op1: source operand.
        """
        arg0 = op0.read()
        arg1 = op1.read()
        res = 0

        for i in range(0, op0.size, 8):
            res = Operators.ITEBV(
                op0.size,
                Operators.EXTRACT(arg0, i, 8) == Operators.EXTRACT(arg1, i, 8),
                res | (0xFF << i),
                res,
            )
            # if (arg0>>i)&0xff == (arg1>>i)&0xff:
            #    res = res | (0xff << i)
        op0.write(res)

    @instruction
    def PCMPEQD(cpu, op0, op1):
        """
        PCMPEQD: Packed compare for equal with double words
        see PCMPEQB
        """
        arg0 = op0.read()
        arg1 = op1.read()
        res = 0

        for i in range(0, op0.size, 32):
            res = Operators.ITEBV(
                op0.size,
                Operators.EXTRACT(arg0, i, 32) == Operators.EXTRACT(arg1, i, 32),
                res | (0xFFFFFFFF << i),
                res,
            )
        op0.write(res)

    @instruction
    def PCMPGTD(cpu, op0, op1):
        """
        PCMPGTD: Packed compare for greater than with double words
        see PCMPEQB
        """
        arg0 = op0.read()
        arg1 = op1.read()
        res = 0

        for i in range(0, op0.size, 32):
            res = Operators.ITEBV(
                op0.size,
                Operators.EXTRACT(arg0, i, 32) > Operators.EXTRACT(arg1, i, 32),
                res | (0xFFFFFFFF << i),
                res,
            )
        op0.write(res)

    @instruction
    def PADDD(cpu, op0, op1):
        """
        PADDD: Packed add with double words

        Performs a SIMD add of the packed integers from the source operand (second operand)
        and the destination operand (first operand), and stores the packed integer results
        in the destination operand

        Example :
        $xmm1.v16_int8 = {..., 0x00000003, 0x00000001}
        $xmm2.v16_int8 = {..., 0x00000004, 0x00000002}
        # after paddd xmm1, xmm2, we get
        $xmm1.v16_int8 = {..., 0x00000007, 0x00000003}
        """
        arg0 = op0.read()
        arg1 = op1.read()
        res = 0

        for i in range(0, op0.size, 32):
            res |= (
                (Operators.EXTRACT(arg0, i, 32) + Operators.EXTRACT(arg1, i, 32)) & 0xFFFFFFFF
            ) << i
        op0.write(res)

    @instruction
    def PADDQ(cpu, op0, op1):
        """
        PADDQ: Packed add with quadruple words
        see PADDD
        """
        arg0 = op0.read()
        arg1 = op1.read()
        res = 0

        for i in range(0, op0.size, 64):
            res |= (
                (Operators.EXTRACT(arg0, i, 64) + Operators.EXTRACT(arg1, i, 64))
                & 0xFFFFFFFFFFFFFFFF
            ) << i
        op0.write(res)

    @instruction
    def PSLLD(cpu, op0, op1):
        """
        PSLLD: Packed shift left logical with double words

        Shifts the destination operand (first operand) to the left by the number of bytes specified
        in the count operand (second operand). The empty low-order bytes are cleared (set to all 0s).
        If the value specified by the count operand is greater than 15, the destination operand is
        set to all 0s. The count operand is an 8-bit immediate.

        Example :
        $xmm1.v16_int8 = {..., 0x00000003, 0x00000001}
        # after pslld xmm1, 2, we get
        $xmm1.v16_int8 = {..., 0x0000000c, 0x00000004}
        """
        arg0 = op0.read()
        arg1 = op1.read()
        res = 0

        for i in range(0, op0.size, 32):
            res |= ((Operators.EXTRACT(arg0, i, 32) << arg1) & 0xFFFFFFFF) << i
        op0.write(res)

    @instruction
    def PSLLQ(cpu, op0, op1):
        """
        PSLLQ: Packed shift left logical with quadruple words
        see PSLLD
        """
        arg0 = op0.read()
        arg1 = op1.read()
        res = 0

        for i in range(0, op0.size, 64):
            res |= ((Operators.EXTRACT(arg0, i, 64) << arg1) & 0xFFFFFFFFFFFFFFFF) << i
        op0.write(res)

    ############################################################################
    # Implementation of PCMPxSTRx Instructions:
    # + PCMPESTRM, PCMPESTRI, PCMPISTRM, PCMPISTRI
    ##
    # """
    # See Ref: https://software.intel.com/sites/default/files/m/8/b/8/D9156103.pdf

    # :param cpu: current CPU.
    # :param op0: compare oprand 1
    # :param op1: compare oprand 2
    # :param op2: control byte
    #             - op2[3:2] :
    #               + 00: Equal Any
    #               + 01: Ranges
    #               + 10: Equal Each
    #               + 11: Equal Ordered
    # """
    #############################################################################
    def _pcmpxstrx_srcdat_format(self, ctlbyte):
        # Parse CTL Byte
        # Source Data Format
        if (Operators.EXTRACT(ctlbyte, 0, 2) & 1) == 0:
            stepsize = 8
        else:
            stepsize = 16
        return stepsize

    def _pcmpxstri_output_selection(self, ctlbyte, res):
        # Output Selection
        # PCMPESTRI/PCMPISTRI
        stepsize = self._pcmpxstrx_srcdat_format(ctlbyte)
        if Operators.EXTRACT(ctlbyte, 6, 1) == 0:
            oecx = 0
            tres = res
            while (tres & 1) == 0:
                oecx += 1
                tres >>= 1
            return oecx
        else:
            oecx = 128 // stepsize - 1
            tres = res
            msbmask = 1 << (128 // stepsize) - 1
            while (tres & msbmask) == 0:
                oecx -= 1
                tres = (tres << 1) & ((msbmask << 1) - 1)
            return oecx

    def _pcmpxstrm_output_selection(self, ctlbyte, res):
        # Output Selection
        # PCMPESTRM/PCMPISTRM
        if Operators.EXTRACT(ctlbyte, 6, 1) == 0:
            return res
        else:
            stepsize = self._pcmpxstrx_srcdat_format(ctlbyte)
            xmmres = 0
            for i in range(0, 128, stepsize):
                if res & 1 == 1:
                    xmmres |= ((1 << stepsize) - 1) << i
                res >>= 1
            return xmmres

    def _pcmpistrx_varg(self, arg, ctlbyte):
        step = self._pcmpxstrx_srcdat_format(ctlbyte)
        result = []
        for i in range(0, 128, step):
            uc = Operators.EXTRACT(arg, i, step)
            if uc == 0:
                break
            result.append(uc)
        return result

    def _pcmpestrx_varg(self, arg, regname, ctlbyte):
        reg = self.read_register(regname)
        if issymbolic(reg):
            raise ConcretizeRegister(self, regname, "Concretize PCMPESTRx ECX/EDX")
        smask = 1 << (self.regfile.sizeof(regname) - 1)
        step = self._pcmpxstrx_srcdat_format(ctlbyte)
        if reg & smask == 1:
            val = Operators.NOT(reg - 1)
        else:
            val = reg
        if val > 128 // step:
            val = 128 // step
        result = []
        for i in range(val):
            uc = Operators.EXTRACT(arg, i * step, step)
            result.append(uc)
        return result

    def _pcmpxstrx_aggregation_operation(self, varg0, varg1, ctlbyte):
        ##
        needle = [e for e in varg0]
        haystack = [e for e in varg1]

        # Aggregation Operation
        res = 0
        stepsize = self._pcmpxstrx_srcdat_format(ctlbyte)
        xmmsize = 128
        if Operators.EXTRACT(ctlbyte, 2, 2) == 0:
            # raise NotImplementedError("pcmpistrx Equal any")
            for i in range(len(haystack)):
                if haystack[i] in needle:
                    res |= 1 << i
        elif Operators.EXTRACT(ctlbyte, 2, 2) == 1:
            # raise NotImplementedError("pcmpistrx Ranges")
            assert len(needle) % 2 == 0
            for i in range(len(haystack)):
                for j in range(0, len(needle), 2):
                    if haystack[i] >= needle[j] and haystack[i] <= needle[j + 1]:
                        res |= 1 << i
                        break
        elif Operators.EXTRACT(ctlbyte, 2, 2) == 2:
            # raise NotImplementedError("pcmpistrx Equal each")
            # Equal Each requires Null Byte Comparison Here
            while len(needle) < xmmsize // stepsize:
                needle.append("\x00")
            while len(haystack) < xmmsize // stepsize:
                haystack.append("\x00")
            for i in range(xmmsize // stepsize):
                res = Operators.ITEBV(xmmsize, needle[i] == haystack[i], res | (1 << i), res)
        elif Operators.EXTRACT(ctlbyte, 2, 2) == 3:
            # raise NotImplementedError("pcmpistrx Equal ordered")
            if len(haystack) < len(needle):
                return 0
            for i in range(len(haystack)):
                subneedle = needle[
                    : (xmmsize // stepsize - i)
                    if len(needle) + i > xmmsize // stepsize
                    else len(needle)
                ]
                res = Operators.ITEBV(
                    xmmsize, haystack[i : i + len(subneedle)] == subneedle, res | (1 << i), res
                )
        return res

    def _pcmpxstrx_polarity(self, res1, ctlbyte, arg2len):
        # Polarity
        stepsize = self._pcmpxstrx_srcdat_format(ctlbyte)
        if Operators.EXTRACT(ctlbyte, 4, 2) == 0:
            res2 = res1
        if Operators.EXTRACT(ctlbyte, 4, 2) == 1:
            res2 = ((1 << (128 // stepsize)) - 1) ^ res1
        if Operators.EXTRACT(ctlbyte, 4, 2) == 2:
            res2 = res1
        if Operators.EXTRACT(ctlbyte, 4, 2) == 3:
            res2 = ((1 << arg2len) - 1) ^ res1
        return res2

    def _pcmpxstrx_setflags(self, res, varg0, varg1, ctlbyte):
        stepsize = self._pcmpxstrx_srcdat_format(ctlbyte)
        self.ZF = len(varg1) < 128 // stepsize
        self.SF = len(varg0) < 128 // stepsize
        self.CF = res != 0
        self.OF = res & 1
        self.AF = False
        self.PF = False

    def _pcmpxstrx_operands(self, op0, op1, op2):
        arg0 = op0.read()
        arg1 = op1.read()
        ctlbyte = op2.read()
        if issymbolic(arg0):
            # XMM Register
            assert op0.type == "register"
            raise ConcretizeRegister(self, op0.reg, "Concretize for PCMPXSTRX")
        if issymbolic(arg1):
            if op1.type == "register":
                # XMM Register
                raise ConcretizeRegister(self, op1.reg, "Concretize for PCMPXSTRX")
            else:
                # Memory
                raise ConcretizeMemory(self.memory, op1.address(), op0.size)
        assert not issymbolic(ctlbyte)
        return (arg0, arg1, ctlbyte)

    @instruction
    def PCMPISTRI(cpu, op0, op1, op2):
        arg0, arg1, ctlbyte = cpu._pcmpxstrx_operands(op0, op1, op2)
        varg0 = cpu._pcmpistrx_varg(arg0, ctlbyte)
        varg1 = cpu._pcmpistrx_varg(arg1, ctlbyte)
        res = cpu._pcmpxstrx_aggregation_operation(varg0, varg1, ctlbyte)
        res = cpu._pcmpxstrx_polarity(res, ctlbyte, len(varg1))
        if res == 0:
            cpu.ECX = 128 // cpu._pcmpxstrx_srcdat_format(ctlbyte)
        else:
            cpu.ECX = cpu._pcmpxstri_output_selection(ctlbyte, res)
        cpu._pcmpxstrx_setflags(res, varg0, varg1, ctlbyte)

    @instruction
    def PCMPISTRM(cpu, op0, op1, op2):
        arg0, arg1, ctlbyte = cpu._pcmpxstrx_operands(op0, op1, op2)
        varg0 = cpu._pcmpistrx_varg(arg0, ctlbyte)
        varg1 = cpu._pcmpistrx_varg(arg1, ctlbyte)
        res = cpu._pcmpxstrx_aggregation_operation(varg0, varg1, ctlbyte)
        res = cpu._pcmpxstrx_polarity(res, ctlbyte, len(varg1))
        cpu.XMM0 = cpu._pcmpxstrm_output_selection(ctlbyte, res)
        cpu._pcmpxstrx_setflags(res, varg0, varg1, ctlbyte)

    @instruction
    def PCMPESTRI(cpu, op0, op1, op2):
        arg0, arg1, ctlbyte = cpu._pcmpxstrx_operands(op0, op1, op2)
        varg0 = cpu._pcmpestrx_varg(arg0, "EAX", ctlbyte)
        varg1 = cpu._pcmpestrx_varg(arg1, "EDX", ctlbyte)
        res = cpu._pcmpxstrx_aggregation_operation(varg0, varg1, ctlbyte)
        res = cpu._pcmpxstrx_polarity(res, ctlbyte, len(varg1))
        if res == 0:
            cpu.ECX = 128 // cpu._pcmpxstrx_srcdat_format(ctlbyte)
        else:
            cpu.ECX = cpu._pcmpxstri_output_selection(ctlbyte, res)
        cpu._pcmpxstrx_setflags(res, varg0, varg1, ctlbyte)

    @instruction
    def PCMPESTRM(cpu, op0, op1, op2):
        arg0, arg1, ctlbyte = cpu._pcmpxstrx_operands(op0, op1, op2)
        varg0 = cpu._pcmpestrx_varg(arg0, "EAX", ctlbyte)
        varg1 = cpu._pcmpestrx_varg(arg1, "EDX", ctlbyte)
        res = cpu._pcmpxstrx_aggregation_operation(varg0, varg1, ctlbyte)
        res = cpu._pcmpxstrx_polarity(res, ctlbyte, len(varg1))
        cpu.XMM0 = cpu._pcmpxstrm_output_selection(ctlbyte, res)
        cpu._pcmpxstrx_setflags(res, varg0, varg1, ctlbyte)

    @instruction
    def PMOVMSKB(cpu, op0, op1):
        """
        Moves byte mask to general-purpose register.

        Creates an 8-bit mask made up of the most significant bit of each byte of the source operand
        (second operand) and stores the result in the low byte or word of the destination operand
        (first operand). The source operand is an MMX(TM) technology or an XXM register; the destination
        operand is a general-purpose register.

        :param cpu: current CPU.
        :param op0: destination operand.
        :param op1: source operand.
        """
        arg0 = op0.read()
        arg1 = op1.read()

        res = 0
        for i in reversed(range(7, op1.size, 8)):
            res = (res << 1) | ((arg1 >> i) & 1)
        op0.write(Operators.EXTRACT(res, 0, op0.size))

    @instruction
    def PSRLDQ(cpu, dest, src):
        """
        Packed shift right logical double quadword.

        Shifts the destination operand (first operand) to the right by the number
        of bytes specified in the count operand (second operand). The empty high-order
        bytes are cleared (set to all 0s). If the value specified by the count
        operand is greater than 15, the destination operand is set to all 0s.
        The destination operand is an XMM register. The count operand is an 8-bit
        immediate::

            TEMP  =  SRC;
            if (TEMP > 15) TEMP  =  16;
            DEST  =  DEST >> (temp * 8);

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: count operand.
        """
        # TODO(yan): Verify the correctness of truncating SRC like this ( tests
        # use '-1' as the value
        temp = Operators.EXTRACT(src.read(), 0, 8)
        temp = Operators.ITEBV(src.size, temp > 15, 16, temp)
        dest.write(dest.read() >> (temp * 8))

    @instruction
    def NOP(cpu, arg0=None):
        """
        No Operation.

        Performs no operation. This instruction is a one-byte instruction that  takes up space in the
        instruction stream but does not affect the machine.
        The NOP instruction is an alias mnemonic for the XCHG (E)AX, (E)AX instruction.

        :param cpu: current CPU.
        :param arg0: this argument is ignored.
        """

    @instruction
    def MOVD(cpu, op0, op1):
        cpu._writeCorrectSize(op0, op1)

    @instruction
    def MOVZX(cpu, op0, op1):
        """
        Moves with zero-extend.

        Copies the contents of the source operand (register or memory location) to the destination
        operand (register) and zero extends the value to 16 or 32 bits. The size of the converted value
        depends on the operand-size attribute::

                OP0  =  ZeroExtend(OP1);

        :param cpu: current CPU.
        :param op0: destination operand.
        :param op1: source operand.
        """
        op0.write(Operators.ZEXTEND(op1.read(), op0.size))

    @instruction
    def MOVSX(cpu, op0, op1):
        """
        Moves with sign-extension.

        Copies the contents of the source operand (register or memory location) to the destination
        operand (register) and sign extends the value to 16::

                OP0  =  SignExtend(OP1);

        :param cpu: current CPU.
        :param op0: destination operand.
        :param op1: source operand.
        """
        op0.write(Operators.SEXTEND(op1.read(), op1.size, op0.size))

    @instruction
    def MOVSXD(cpu, op0, op1):
        """Move DWORD with sign extension to QWORD."""
        op0.write(Operators.SEXTEND(op1.read(), op1.size, op0.size))

    @instruction
    def CQO(cpu):
        """
        RDX:RAX = sign-extend of RAX.
        """
        res = Operators.SEXTEND(cpu.RAX, 64, 128)
        cpu.RAX = Operators.EXTRACT(res, 0, 64)
        cpu.RDX = Operators.EXTRACT(res, 64, 64)

    @instruction
    def CDQE(cpu):
        """
        RAX = sign-extend of EAX.
        """
        cpu.RAX = Operators.SEXTEND(cpu.EAX, 32, 64)

    @instruction
    def CDQ(cpu):
        """
        EDX:EAX = sign-extend of EAX
        """
        cpu.EDX = Operators.EXTRACT(Operators.SEXTEND(cpu.EAX, 32, 64), 32, 32)

    @instruction
    def CWDE(cpu):
        """
        Converts word to doubleword.

        ::
            DX = sign-extend of AX.

        :param cpu: current CPU.
        """
        bit = Operators.EXTRACT(cpu.AX, 15, 1)
        cpu.EAX = Operators.SEXTEND(cpu.AX, 16, 32)
        cpu.EDX = Operators.SEXTEND(bit, 1, 32)

    @instruction
    def CBW(cpu):
        """
        Converts byte to word.

        Double the size of the source operand by means of sign extension::

                AX = sign-extend of AL.

        :param cpu: current CPU.
        """
        cpu.AX = Operators.SEXTEND(cpu.AL, 8, 16)

    @instruction
    def RDTSC(cpu):
        """
        Reads time-stamp counter.

        Loads the current value of the processor's time-stamp counter into the
        EDX:EAX registers.  The time-stamp counter is contained in a 64-bit
        MSR. The high-order 32 bits of the MSR are loaded into the EDX
        register, and the low-order 32 bits are loaded into the EAX register.
        The processor increments the time-stamp counter MSR every clock cycle
        and resets it to 0 whenever the processor is reset.

        :param cpu: current CPU.
        """
        val = cpu.icount
        cpu.RAX = val & 0xFFFFFFFF
        cpu.RDX = (val >> 32) & 0xFFFFFFFF

    # AVX
    def _writeCorrectSize(cpu, op0, op1):
        if op0.size > op1.size:
            op0.write(Operators.ZEXTEND(op1.read(), op0.size))
        else:
            op0.write(Operators.EXTRACT(op1.read(), 0, op0.size))

    @instruction
    def VMOVD(cpu, op0, op1):
        cpu._writeCorrectSize(op0, op1)

    # MMX
    @instruction
    def VMOVUPS(cpu, op0, op1):
        arg1 = op1.read()
        op0.write(arg1)

    @instruction
    def VMOVAPS(cpu, op0, op1):
        arg1 = op1.read()
        op0.write(arg1)

    @instruction
    def VMOVQ(cpu, op0, op1):
        cpu._writeCorrectSize(op0, op1)

    # FPU:
    @instruction
    def FNSTCW(cpu, dest):
        """
        Stores x87 FPU Control Word.

        Stores the current value of the FPU control word at the specified destination in memory.
        The FSTCW instruction checks for and handles pending unmasked floating-point exceptions
        before storing the control word; the FNSTCW instruction does not::

            DEST  =  FPUControlWord;

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        cpu.write_int(dest.address(), cpu.FPCW, 16)

    def sem_SYSCALL(cpu):
        """
        Syscall semantics without @instruction for use in emulator
        """
        cpu.RCX = cpu.RIP
        cpu.R11 = cpu.RFLAGS
        raise Syscall()

    @instruction
    def SYSCALL(cpu):
        """
        Calls to interrupt procedure.

        The INT n instruction generates a call to the interrupt or exception handler specified
        with the destination operand. The INT n instruction is the general mnemonic for executing
        a software-generated call to an interrupt handler. The INTO instruction is a special
        mnemonic for calling overflow exception (#OF), interrupt vector number 4. The overflow
        interrupt checks the OF flag in the EFLAGS register and calls the overflow interrupt handler
        if the OF flag is set to 1.

        :param cpu: current CPU.
        """
        cpu.sem_SYSCALL()

    @instruction
    def MOVLPD(cpu, dest, src):
        """
        Moves low packed double-precision floating-point value.

        Moves a double-precision floating-point value from the source operand (second operand) and the
        destination operand (first operand). The source and destination operands can be an XMM register
        or a 64-bit memory location. This instruction allows double-precision floating-point values to be moved
        to and from the low quadword of an XMM register and memory. It cannot be used for register to register
        or memory to memory moves. When the destination operand is an XMM register, the high quadword of the
        register remains unchanged.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        value = src.read()
        if src.size == 64 and dest.size == 128:
            value = (dest.read() & 0xFFFFFFFFFFFFFFFF0000000000000000) | Operators.ZEXTEND(
                value, 128
            )
        dest.write(value)

    @instruction
    def MOVHPD(cpu, dest, src):
        """
        Moves high packed double-precision floating-point value.

        Moves a double-precision floating-point value from the source operand (second operand) and the
        destination operand (first operand). The source and destination operands can be an XMM register
        or a 64-bit memory location. This instruction allows double-precision floating-point values to be moved
        to and from the high quadword of an XMM register and memory. It cannot be used for register to
        register or memory to memory moves. When the destination operand is an XMM register, the low quadword
        of the register remains unchanged.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        if src.size == 128:
            assert dest.size == 64
            dest.write(Operators.EXTRACT(src.read(), 64, 64))
        else:
            assert src.size == 64 and dest.size == 128
            value = Operators.EXTRACT(dest.read(), 0, 64)  # low part
            dest.write(Operators.CONCAT(128, src.read(), value))

    @instruction
    def MOVHPS(cpu, dest, src):
        """
        Moves high packed single-precision floating-point value.

        Moves two packed single-precision floating-point values from the source operand
        (second operand) to the destination operand (first operand). The source and destination
        operands can be an XMM register or a 64-bit memory location. The instruction allows
        single-precision floating-point values to be moved to and from the high quadword of
        an XMM register and memory. It cannot be used for register to register or memory to
        memory moves. When the destination operand is an XMM register, the low quadword
        of the register remains unchanged.
        """
        if src.size == 128:
            assert dest.size == 64
            dest.write(Operators.EXTRACT(src.read(), 64, 64))
        else:
            assert src.size == 64 and dest.size == 128
            value = Operators.EXTRACT(dest.read(), 0, 64)  # low part
            dest.write(Operators.CONCAT(128, src.read(), value))

    @instruction
    def PSUBB(cpu, dest, src):
        """
        Packed subtract.

        Performs a SIMD subtract of the packed integers of the source operand (second operand) from the packed
        integers of the destination operand (first operand), and stores the packed integer results in the
        destination operand. The source operand can be an MMX(TM) technology register or a 64-bit memory location,
        or it can be an XMM register or a 128-bit memory location. The destination operand can be an MMX or an XMM
        register.
        The PSUBB instruction subtracts packed byte integers. When an individual result is too large or too small
        to be represented in a byte, the result is wrapped around and the low 8 bits are written to the
        destination element.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        result = []
        value_a = dest.read()
        value_b = src.read()
        for i in reversed(range(0, dest.size, 8)):
            a = Operators.EXTRACT(value_a, i, 8)
            b = Operators.EXTRACT(value_b, i, 8)
            result.append((a - b) & 0xFF)
        dest.write(Operators.CONCAT(8 * len(result), *result))

    @instruction
    def POR(cpu, dest, src):
        """
        Performs a bitwise logical OR operation on the source operand (second operand) and the destination operand
        (first operand) and stores the result in the destination operand. The source operand can be an MMX technology
        register or a 64-bit memory location or it can be an XMM register or a 128-bit memory location. The destination
        operand can be an MMX technology register or an XMM register. Each bit of the result is set to 1 if either
        or both of the corresponding bits of the first and second operands are 1; otherwise, it is set to 0.
        """
        res = dest.write(dest.read() | src.read())

    @instruction
    def XORPS(cpu, dest, src):
        """
        Performs a bitwise logical OR operation on the source operand (second operand) and the destination operand
        (first operand) and stores the result in the destination operand. The source operand can be an MMX technology
        register or a 64-bit memory location or it can be an XMM register or a 128-bit memory location. The destination
        operand can be an MMX technology register or an XMM register. Each bit of the result is set to 1 if either
        or both of the corresponding bits of the first and second operands are 1; otherwise, it is set to 0.
        """
        res = dest.write(dest.read() ^ src.read())

    @instruction
    def VORPD(cpu, dest, src, src2):
        """
        Performs a bitwise logical OR operation on the source operand (second operand) and second source operand (third operand)
         and stores the result in the destination operand (first operand).
        """
        res = dest.write(src.read() | src2.read())

    @instruction
    def VORPS(cpu, dest, src, src2):
        """
        Performs a bitwise logical OR operation on the source operand (second operand) and second source operand (third operand)
         and stores the result in the destination operand (first operand).
        """
        res = dest.write(src.read() | src2.read())

    @instruction
    def PTEST(cpu, dest, src):
        """PTEST
        PTEST set the ZF flag if all bits in the result are 0 of the bitwise AND
        of the first source operand (first operand) and the second source operand
        (second operand). Also this sets the CF flag if all bits in the result
        are 0 of the bitwise AND of the second source operand (second operand)
        and the logical NOT of the destination operand.
        """
        cpu.OF = False
        cpu.AF = False
        cpu.PF = False
        cpu.SF = False
        cpu.ZF = (
            Operators.EXTRACT(dest.read(), 0, 128) & Operators.EXTRACT(src.read(), 0, 128)
        ) == 0
        cpu.CF = (
            Operators.EXTRACT(src.read(), 0, 128) & ~(Operators.EXTRACT(dest.read(), 0, 128))
        ) == 0

    @instruction
    def VPTEST(cpu, dest, src):
        cpu.OF = False
        cpu.AF = False
        cpu.PF = False
        cpu.SF = False
        cpu.ZF = (dest.read() & src.read()) == 0
        cpu.CF = (dest.read() & ~src.read()) == 0

    @instruction
    def MOVAPS(cpu, dest, src):
        """
        Moves aligned packed single-precision floating-point values.

        Moves a double quadword containing four packed single-precision floating-point numbers from the
        source operand (second operand) to the destination operand (first operand). This instruction can be
        used to load an XMM register from a 128-bit memory location, to store the contents of an XMM register
        into a 128-bit memory location, or move data between two XMM registers.
        When the source or destination operand is a memory operand, the operand must be aligned on a 16-byte
        boundary or a general-protection exception (#GP) will be generated::

                DEST  =  SRC;

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        dest.write(src.read())

    @instruction
    def MOVQ(cpu, dest, src):
        """
        Move quadword.

        Copies a quadword from the source operand (second operand) to the destination operand (first operand).
        The source and destination operands can be MMX(TM) technology registers, XMM registers, or 64-bit memory
        locations. This instruction can be used to move a between two MMX registers or between an MMX register
        and a 64-bit memory location, or to move data between two XMM registers or between an XMM register and
        a 64-bit memory location. The instruction cannot be used to transfer data between memory locations.
        When the source operand is an XMM register, the low quadword is moved; when the destination operand is
        an XMM register, the quadword is stored to the low quadword of the register, and the high quadword is
        cleared to all 0s::

            MOVQ instruction when operating on MMX registers and memory locations:

            DEST  =  SRC;

            MOVQ instruction when source and destination operands are XMM registers:

            DEST[63-0]  =  SRC[63-0];

            MOVQ instruction when source operand is XMM register and destination operand is memory location:

            DEST  =  SRC[63-0];

            MOVQ instruction when source operand is memory location and destination operand is XMM register:

            DEST[63-0]  =  SRC;
            DEST[127-64]  =  0000000000000000H;

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        # mmx to mmx or mmx to mem
        if dest.size == src.size and dest.size == 64:
            dest.write(src.read())
        # two xmm regs
        elif dest.size == src.size and dest.size == 128:
            src_lo = Operators.EXTRACT(src.read(), 0, 64)
            dest.write(Operators.ZEXTEND(src_lo, 128))
        # mem to xmm
        elif dest.size == 128 and src.size == 64:
            dest.write(Operators.ZEXTEND(src.read(), dest.size))
        # xmm to mem
        elif dest.size == 64 and src.size == 128:
            dest.write(Operators.EXTRACT(src.read(), 0, dest.size))
        else:
            msg = "Invalid size in MOVQ"
            logger.error(msg)
            raise CpuException(msg)

    @instruction
    def MOVSD(cpu, dest, src):
        """
        Move Scalar Double-Precision Floating-Point Value

        Moves a scalar double-precision floating-point value from the source
        operand (second operand) to the destination operand (first operand).
        The source and destination operands can be XMM registers or 64-bit memory
        locations. This instruction can be used to move a double-precision
        floating-point value to and from the low quadword of an XMM register and
        a 64-bit memory location, or to move a double-precision floating-point
        value between the low quadwords of two XMM registers. The instruction
        cannot be used to transfer data between memory locations.
        When the source and destination operands are XMM registers, the high
        quadword of the destination operand remains unchanged. When the source
        operand is a memory location and destination operand is an XMM registers,
        the high quadword of the destination operand is cleared to all 0s.

        :param cpu: current CPU.
        :param dest: destination operand.
        :param src: source operand.
        """
        assert dest.type != "memory" or src.type != "memory"
        value = Operators.EXTRACT(src.read(), 0, 64)
        if dest.size > src.size:
            value = Operators.ZEXTEND(value, dest.size)
        dest.write(value)

    @instruction
    def MOVSS(cpu, dest, src):
        """
        Moves a scalar single-precision floating-point value

        Moves a scalar single-precision floating-point value from the source operand (second operand)
        to the destination operand (first operand). The source and destination operands can be XMM
        registers or 32-bit memory locations. This instruction can be used to move a single-precision
        floating-point value to and from the low doubleword of an XMM register and a 32-bit memory
        location, or to move a single-precision floating-point value between the low doublewords of
        two XMM registers. The instruction cannot be used to transfer data between memory locations.
        When the source and destination operands are XMM registers, the three high-order doublewords of the
        destination operand remain unchanged. When the source operand is a memory location and destination
        operand is an XMM registers, the three high-order doublewords of the destination operand are cleared to all 0s.

        //MOVSS instruction when source and destination operands are XMM registers:
        if(IsXMM(Source) && IsXMM(Destination))
            Destination[0..31] = Source[0..31];
            //Destination[32..127] remains unchanged
            //MOVSS instruction when source operand is XMM register and destination operand is memory location:
        else if(IsXMM(Source) && IsMemory(Destination))
            Destination = Source[0..31];
        //MOVSS instruction when source operand is memory location and destination operand is XMM register:
        else {
                Destination[0..31] = Source;
                Destination[32..127] = 0;
        }
        """
        if dest.type == "register" and src.type == "register":
            assert dest.size == 128 and src.size == 128
            dest.write(dest.read() & ~0xFFFFFFFF | src.read() & 0xFFFFFFFF)
        elif dest.type == "memory":
            assert src.type == "register"
            dest.write(Operators.EXTRACT(src.read(), 0, dest.size))
        else:
            assert src.type == "memory" and dest.type == "register"
            assert src.size == 32 and dest.size == 128
            dest.write(Operators.ZEXTEND(src.read(), 128))

    @instruction
    def VMOVDQA(cpu, dest, src):
        """
        Move Aligned Double Quadword

        Moves 128 bits of packed integer values from the source operand (second
        operand) to the destination operand (first operand). This instruction
        can be used to load an XMM register from a 128-bit memory location, to
        store the contents of an XMM register into a 128-bit memory location, or
        to move data between two XMM registers.

        When the source or destination operand is a memory operand, the operand
        must be aligned on a 16-byte boundary or a general-protection exception
        (#GP) will be generated. To move integer data to and from unaligned
        memory locations, use the VMOVDQU instruction."""
        # TODO raise exception when unaligned!
        dest.write(src.read())

    @instruction
    def VMOVDQU(cpu, dest, src):
        """
        Move Unaligned Double Quadword

        Moves 128 bits of packed integer values from the source operand (second operand)
        to the destination operand (first operand). This instruction can be used to load
        an XMM register from a 128-bit memory location, to store the contents of an XMM
        register into a 128-bit memory location, or to move data between two XMM registers.
        When the source or destination operand is a memory operand, the operand may be
        unaligned on a 16-byte boundary without causing a general-protection exception
        (#GP) to be generated.

            VMOVDQU (VEX.128 encoded version)
            DEST[127:0] <- SRC[127:0]
            DEST[VLMAX-1:128] <- 0
            VMOVDQU (VEX.256 encoded version)
            DEST[255:0] <- SRC[255:0]
        """
        # FIXME for VEX128? or do testcase
        dest.write(src.read())

    @instruction
    def VEXTRACTF128(cpu, dest, src, offset):
        """Extract Packed Floating-Point Values

        Extracts 128-bits of packed floating-point values from the source
        operand (second operand) at an 128-bit offset from imm8[0] into the
        destination operand (first operand). The destination may be either an
        XMM register or an 128-bit memory location.
        """
        offset = offset.read()
        dest.write(Operators.EXTRACT(src.read(), offset * 128, (offset + 1) * 128))

    @instruction
    def PREFETCHT0(cpu, arg):
        """
        Not implemented.

        Performs no operation.
        """

    @instruction
    def PREFETCHT1(cpu, arg):
        """
        Not implemented.

        Performs no operation.
        """

    @instruction
    def PREFETCHT2(cpu, arg):
        """
        Not implemented.

        Performs no operation.
        """

    @instruction
    def PREFETCHTNTA(cpu, arg):
        """
        Not implemented.

        Performs no operation.
        """

    @instruction
    def PINSRW(cpu, dest, src, count):
        if dest.size == 64:
            # PINSRW instruction with 64-bit source operand:
            sel = count.read() & 3
            mask = [0x000000000000FFFF, 0x00000000FFFF0000, 0x0000FFFF00000000, 0xFFFF000000000000][
                sel
            ]
        else:
            # PINSRW instruction with 128-bit source operand
            assert dest.size == 128
            sel = count.read() & 7
            mask = [
                0x0000000000000000000000000000FFFF,
                0x000000000000000000000000FFFF0000,
                0x00000000000000000000FFFF00000000,
                0x0000000000000000FFFF000000000000,
                0x000000000000FFFF0000000000000000,
                0x00000000FFFF00000000000000000000,
                0x0000FFFF000000000000000000000000,
                0xFFFF0000000000000000000000000000,
            ][sel]
        dest.write(
            (dest.read() & ~mask)
            | ((Operators.ZEXTEND(src.read(), dest.size) << (sel * 16)) & mask)
        )

    @instruction
    def PEXTRW(cpu, dest, src, count):
        if src.size == 64:
            sel = Operators.ZEXTEND(Operators.EXTRACT(count.read(), 0, 2), src.size)
        else:
            sel = Operators.ZEXTEND(Operators.EXTRACT(count.read(), 0, 3), src.size)
        tmp = (src.read() >> (sel * 16)) & 0xFFFF
        dest.write(Operators.EXTRACT(tmp, 0, dest.size))

    @instruction
    def PALIGNR(cpu, dest, src, offset):
        """ALIGNR concatenates the destination operand (the first operand) and the source
        operand (the second operand) into an intermediate composite, shifts the composite
        at byte granularity to the right by a constant immediate, and extracts the right-
        aligned result into the destination."""
        dest.write(
            Operators.EXTRACT(
                Operators.CONCAT(dest.size * 2, dest.read(), src.read()),
                offset.read() * 8,
                dest.size,
            )
        )

    @instruction
    def PSLLDQ(cpu, dest, src):
        """Packed Shift Left Logical Double Quadword
        Shifts the destination operand (first operand) to the left by the number
         of bytes specified in the count operand (second operand). The empty low-order
         bytes are cleared (set to all 0s). If the value specified by the count
         operand is greater than 15, the destination operand is set to all 0s.
         The destination operand is an XMM register. The count operand is an 8-bit
         immediate.

            TEMP  =  COUNT;
            if (TEMP > 15) TEMP  =  16;
            DEST  =  DEST << (TEMP * 8);
        """
        count = Operators.ZEXTEND(src.read(), dest.size * 2)
        byte_count = Operators.ITEBV(src.size * 2, count > 15, 16, count)
        bit_count = byte_count * 8
        val = Operators.ZEXTEND(dest.read(), dest.size * 2)
        val = val << (Operators.ZEXTEND(bit_count, dest.size * 2))
        dest.write(Operators.EXTRACT(val, 0, dest.size))

    # FIXME
    @instruction
    def PSRLQ(cpu, dest, src):
        """Shift Packed Data Right Logical

        Shifts the bits in the individual quadword in the destination operand to the right by
        the number of bits specified in the count operand . As the bits in the data elements
        are shifted right, the empty high-order bits are cleared (set to 0). If the value
        specified by the count operand is greater than  63, then the destination operand is set
        to all 0s.

        if(OperandSize == 64) {
                        //PSRLQ instruction with 64-bit operand:
                        if(Count > 63) Destination[64..0] = 0;
                        else Destination = ZeroExtend(Destination >> Count);
                }
                else {
                        //PSRLQ instruction with 128-bit operand:
                        if(Count > 15) Destination[128..0] = 0;
                        else {
                                Destination[0..63] = ZeroExtend(Destination[0..63] >> Count);
                                Destination[64..127] = ZeroExtend(Destination[64..127] >> Count);
                        }
                }
        """

        count = src.read()
        count = Operators.ITEBV(src.size, Operators.UGT(count, 63), 64, count)
        count = Operators.EXTRACT(count, 0, 64)
        if dest.size == 64:
            dest.write(dest.read() >> count)
        else:
            hi = Operators.EXTRACT(dest.read(), 64, 64) >> count
            low = Operators.EXTRACT(dest.read(), 0, 64) >> count
            dest.write(Operators.CONCAT(128, hi, low))

    @instruction
    def PAND(cpu, dest, src):
        dest.write(dest.read() & src.read())

    @instruction
    def LSL(cpu, limit_ptr, selector):
        selector = selector.read()

        if issymbolic(selector):
            # need to check if selector can be any of cpu_segments.keys()
            # and if so concretize accordingly
            raise NotImplementedError("Do not yet implement symbolic LSL")

        # Checks that the segment selector is not null.
        if (
            selector == 0 or selector not in cpu._segments
        ):  # Shouldn't we need check for max GDTR limit instead?
            cpu.ZF = False
            logger.info("Invalid selector %s. Clearing ZF", selector)
            return

        base, limit, ty = cpu.get_descriptor(selector)

        # Check CPL and type
        # TODO http://x86.renejeschke.de/html/file_module_x86_id_162.html
        logger.debug("LSL instruction not fully implemented")

        cpu.ZF = True
        limit_ptr.write(limit)

    @instruction
    def SYSENTER(cpu):
        """
        Calls to system

        Executes a fast call to a level 0 system procedure or routine

        :param cpu: current CPU.
        """
        raise Syscall()

    @instruction
    def TZCNT(cpu, dest, src):
        """
        Count the number of trailing least significant zero bits in source
        operand (second operand) and returns the result in destination
        operand (first operand). TZCNT is an extension of the BSF instruction.

        The key difference between TZCNT and BSF instruction is that TZCNT
        provides operand size as output when source operand is zero while in
        the case of BSF instruction, if source operand is zero, the content of
        destination operand are undefined. On processors that do not support
        TZCNT, the instruction byte encoding is executed as BSF
        """

        value = src.read()
        flag = Operators.EXTRACT(value, 0, 1) == 1
        res = 0
        for pos in range(1, src.size):
            res = Operators.ITEBV(dest.size, flag, res, pos)
            flag = Operators.OR(flag, Operators.EXTRACT(value, pos, 1) == 1)

        cpu.CF = res == src.size
        cpu.ZF = res == 0
        dest.write(res)

    @instruction
    def VPSHUFB(cpu, op0, op1, op3):
        """
        Packed shuffle bytes.

        Copies bytes from source operand (second operand) and inserts them in the destination operand
        (first operand) at locations selected with the order operand (third operand).

        :param cpu: current CPU.
        :param op0: destination operand.
        :param op1: source operand.
        :param op3: order operand.
        """
        size = op0.size
        arg0 = op0.read()
        arg1 = op1.read()
        arg3 = Operators.ZEXTEND(op3.read(), size)

        arg0 |= Operators.ITEBV(
            size, Operators.EXTRACT(arg3, 7, 1) == 1, 0, (arg1 >> ((arg3 >> 0) & 7 * 8)) & 0xFF
        )
        arg0 |= Operators.ITEBV(
            size,
            Operators.EXTRACT(arg3, 15, 1) == 1,
            0,
            ((arg1 >> ((arg3 >> 8) & 7 * 8)) & 0xFF) << 8,
        )
        arg0 |= Operators.ITEBV(
            size,
            Operators.EXTRACT(arg3, 23, 1) == 1,
            0,
            ((arg1 >> ((arg3 >> 16) & 7 * 8)) & 0xFF) << 16,
        )
        arg0 |= Operators.ITEBV(
            size,
            Operators.EXTRACT(arg3, 31, 1) == 1,
            0,
            ((arg1 >> ((arg3 >> 24) & 7 * 8)) & 0xFF) << 24,
        )
        arg0 |= Operators.ITEBV(
            size,
            Operators.EXTRACT(arg3, 39, 1) == 1,
            0,
            ((arg1 >> ((arg3 >> 32) & 7 * 8)) & 0xFF) << 32,
        )
        arg0 |= Operators.ITEBV(
            size,
            Operators.EXTRACT(arg3, 47, 1) == 1,
            0,
            ((arg1 >> ((arg3 >> 40) & 7 * 8)) & 0xFF) << 40,
        )
        arg0 |= Operators.ITEBV(
            size,
            Operators.EXTRACT(arg3, 55, 1) == 1,
            0,
            ((arg1 >> ((arg3 >> 48) & 7 * 8)) & 0xFF) << 48,
        )
        arg0 |= Operators.ITEBV(
            size,
            Operators.EXTRACT(arg3, 63, 1) == 1,
            0,
            ((arg1 >> ((arg3 >> 56) & 7 * 8)) & 0xFF) << 56,
        )
        arg0 |= Operators.ITEBV(
            size,
            Operators.EXTRACT(arg3, 71, 1) == 1,
            0,
            ((arg1 >> ((arg3 >> 64) & 7 * 8)) & 0xFF) << 64,
        )
        arg0 |= Operators.ITEBV(
            size,
            Operators.EXTRACT(arg3, 79, 1) == 1,
            0,
            ((arg1 >> ((arg3 >> 72) & 7 * 8)) & 0xFF) << 72,
        )
        arg0 |= Operators.ITEBV(
            size,
            Operators.EXTRACT(arg3, 87, 1) == 1,
            0,
            ((arg1 >> ((arg3 >> 80) & 7 * 8)) & 0xFF) << 80,
        )
        arg0 |= Operators.ITEBV(
            size,
            Operators.EXTRACT(arg3, 95, 1) == 1,
            0,
            ((arg1 >> ((arg3 >> 88) & 7 * 8)) & 0xFF) << 88,
        )
        arg0 |= Operators.ITEBV(
            size,
            Operators.EXTRACT(arg3, 103, 1) == 1,
            0,
            ((arg1 >> ((arg3 >> 96) & 7 * 8)) & 0xFF) << 96,
        )
        arg0 |= Operators.ITEBV(
            size,
            Operators.EXTRACT(arg3, 111, 1) == 1,
            0,
            ((arg1 >> ((arg3 >> 104) & 7 * 8)) & 0xFF) << 104,
        )
        arg0 |= Operators.ITEBV(
            size,
            Operators.EXTRACT(arg3, 119, 1) == 1,
            0,
            ((arg1 >> ((arg3 >> 112) & 7 * 8)) & 0xFF) << 112,
        )
        arg0 |= Operators.ITEBV(
            size,
            Operators.EXTRACT(arg3, 127, 1) == 1,
            0,
            ((arg1 >> ((arg3 >> 120) & 7 * 8)) & 0xFF) << 120,
        )
        op0.write(arg0)

    @instruction
    def VZEROUPPER(cpu):
        cpu.YMM0 = cpu.YMM0 & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
        cpu.YMM1 = cpu.YMM1 & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
        cpu.YMM2 = cpu.YMM2 & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
        cpu.YMM3 = cpu.YMM3 & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
        cpu.YMM4 = cpu.YMM4 & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
        cpu.YMM5 = cpu.YMM5 & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
        cpu.YMM6 = cpu.YMM6 & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
        cpu.YMM7 = cpu.YMM7 & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF

        if cpu.mode == cs.CS_MODE_64:
            cpu.YMM8 = cpu.YMM8 & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
            cpu.YMM9 = cpu.YMM9 & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
            cpu.YMM10 = cpu.YMM10 & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
            cpu.YMM11 = cpu.YMM11 & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
            cpu.YMM12 = cpu.YMM12 & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
            cpu.YMM13 = cpu.YMM13 & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
            cpu.YMM14 = cpu.YMM14 & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
            cpu.YMM15 = cpu.YMM15 & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF


################################################################################
# Calling conventions


class I386LinuxSyscallAbi(SyscallAbi):
    """
    i386 Linux system call ABI
    """

    def syscall_number(self):
        return self._cpu.EAX

    def get_arguments(self):
        for reg in ("EBX", "ECX", "EDX", "ESI", "EDI", "EBP"):
            yield reg

    def get_result_reg(self):
        return "EAX"

    def write_result(self, result):
        self._cpu.EAX = result


class AMD64LinuxSyscallAbi(SyscallAbi):
    """
    AMD64 Linux system call ABI
    """

    # TODO(yan): Floating point or wide arguments that deviate from the norm are
    # not yet supported.

    def syscall_number(self):
        return self._cpu.RAX

    def get_arguments(self):
        for reg in ("RDI", "RSI", "RDX", "R10", "R8", "R9"):
            yield reg

    def get_result_reg(self):
        return "RAX"

    def write_result(self, result):
        self._cpu.RAX = result


class I386CdeclAbi(Abi):
    """
    i386 cdecl function call semantics
    """

    def get_arguments(self):
        base = self._cpu.STACK + self._cpu.address_bit_size // 8
        for address in self.values_from(base):
            yield address

    def get_result_reg(self):
        return "EAX"

    def write_result(self, result):
        self._cpu.EAX = result

    def ret(self):
        self._cpu.EIP = self._cpu.pop(self._cpu.address_bit_size)


class I386StdcallAbi(Abi):
    """
    x86 Stdcall function call convention. Callee cleans up the stack.
    """

    def __init__(self, cpu):
        super().__init__(cpu)
        self._arguments = 0

    def get_arguments(self):
        base = self._cpu.STACK + self._cpu.address_bit_size // 8
        for address in self.values_from(base):
            self._arguments += 1
            yield address

    def get_result_reg(self):
        return "EAX"

    def write_result(self, result):
        self._cpu.EAX = result

    def ret(self):
        self._cpu.EIP = self._cpu.pop(self._cpu.address_bit_size)

        word_bytes = self._cpu.address_bit_size // 8
        self._cpu.ESP += self._arguments * word_bytes
        self._arguments = 0


class SystemVAbi(Abi):
    """
    x64 SystemV function call convention
    """

    # TODO(yan): Floating point or wide arguments that deviate from the norm are
    # not yet supported.

    def get_arguments(self):
        # First 6 arguments go in registers, rest are popped from stack
        reg_args = ("RDI", "RSI", "RDX", "RCX", "R8", "R9")

        for reg in reg_args:
            yield reg

        word_bytes = self._cpu.address_bit_size // 8
        for address in self.values_from(self._cpu.RSP + word_bytes):
            yield address

    def get_result_reg(self):
        return "RAX"

    def write_result(self, result):
        # XXX(yan): Can also return in rdx for wide values.
        self._cpu.RAX = result

    def ret(self):
        self._cpu.RIP = self._cpu.pop(self._cpu.address_bit_size)


class AMD64Cpu(X86Cpu):
    # Config
    max_instr_width = 15
    address_bit_size = 64
    machine = "amd64"
    arch = cs.CS_ARCH_X86
    mode = cs.CS_MODE_64

    def __init__(self, memory: Memory, *args, **kwargs):
        """
        Builds a CPU model.
        :param memory: memory object for this CPU.
        """
        super().__init__(
            AMD64RegFile(aliases={"PC": "RIP", "STACK": "RSP", "FRAME": "RBP"}),
            memory,
            *args,
            **kwargs,
        )

    def __str__(self):
        """
        Returns a string representation of cpu state

        :rtype: str
        :return: a string containing the name and current value for all the registers.
        """
        CHEADER = "\033[95m"
        CBLUE = "\033[94m"
        CGREEN = "\033[92m"
        CWARNING = "\033[93m"
        CFAIL = "\033[91m"
        CEND = "\033[0m"
        pos = 0

        result = ""
        try:
            instruction = self.instruction
            result += f"Instruction: 0x{instruction.address:016x}:\t{instruction.mnemonic}\t{instruction.op_str}\n"
        except BaseException:
            result += "{can't decode instruction }\n"

        regs = (
            "RAX",
            "RCX",
            "RDX",
            "RBX",
            "RSP",
            "RBP",
            "RSI",
            "RDI",
            "R8",
            "R9",
            "R10",
            "R11",
            "R12",
            "R13",
            "R14",
            "R15",
            "RIP",
            "EFLAGS",
        )
        for reg_name in regs:
            value = self.read_register(reg_name)
            if issymbolic(value):
                result += f"{reg_name:3s}: {CFAIL}{visitors.pretty_print(value, depth=10)}{CEND}\n"
            else:
                result += f"{reg_name:3s}: 0x{value:016x}\n"
            pos = 0

        pos = 0
        for reg_name in ("CF", "SF", "ZF", "OF", "AF", "PF", "IF", "DF"):
            value = self.read_register(reg_name)
            if issymbolic(value):
                result += f"{reg_name}: {CFAIL}{visitors.pretty_print(value, depth=10)}{CEND}\n"
            else:
                result += f"{reg_name}: {value:1x}\n"

            pos = 0

        for reg_name in ["CS", "DS", "ES", "SS", "FS", "GS"]:
            base, size, ty = self.get_descriptor(self.read_register(reg_name))
            result += f"{reg_name}: {base:x}, {size:x} ({ty})\n"

        for reg_name in ["FP0", "FP1", "FP2", "FP3", "FP4", "FP5", "FP6", "FP7", "TOP"]:
            value = getattr(self, reg_name)
            result += f"{reg_name:3s}: {value!r}\n"
            pos = 0

        return result

    @property
    def canonical_registers(self):
        return self.regfile.canonical_registers

    @instruction
    def XLATB(cpu):
        """
        Table look-up translation.

        Locates a byte entry in a table in memory, using the contents of the
        AL register as a table index, then copies the contents of the table entry
        back into the AL register. The index in the AL register is treated as
        an unsigned integer. The XLAT and XLATB instructions get the base address
        of the table in memory from either the DS:EBX or the DS:BX registers.
        In 64-bit mode, operation is similar to that in legacy or compatibility mode.
        AL is used to specify the table index (the operand size is fixed at 8 bits).
        RBX, however, is used to specify the table's base address::

                IF address_bit_size = 16
                THEN
                    AL = (DS:BX + ZeroExtend(AL));
                ELSE IF (address_bit_size = 32)
                    AL = (DS:EBX + ZeroExtend(AL)); FI;
                ELSE (address_bit_size = 64)
                    AL = (RBX + ZeroExtend(AL));
                FI;

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        cpu.AL = cpu.read_int(cpu.RBX + Operators.ZEXTEND(cpu.AL, 64), 8)


class I386Cpu(X86Cpu):
    # Config
    max_instr_width = 15
    address_bit_size = 32
    machine = "i386"
    arch = cs.CS_ARCH_X86
    mode = cs.CS_MODE_32

    def __init__(self, memory: Memory, *args, **kwargs):
        """
        Builds a CPU model.
        :param memory: memory object for this CPU.
        """
        super().__init__(
            AMD64RegFile({"PC": "EIP", "STACK": "ESP", "FRAME": "EBP"}), memory, *args, **kwargs
        )

    def __str__(self):
        """
        Returns a string representation of cpu state

        :rtype: str
        :return: a string containing the name and current value for all the registers.
        """
        CHEADER = "\033[95m"
        CBLUE = "\033[94m"
        CGREEN = "\033[92m"
        CWARNING = "\033[93m"
        CFAIL = "\033[91m"
        CEND = "\033[0m"
        pos = 0

        result = ""
        try:
            instruction = self.instruction
            result += f"Instruction: 0x{instruction.address:016x}:\t{instruction.mnemonic}\t{instruction.op_str}\n"
        except BaseException:
            result += "{can't decode instruction }\n"

        regs = ("EAX", "ECX", "EDX", "EBX", "ESP", "EBP", "ESI", "EDI", "EIP")
        for reg_name in regs:
            value = self.read_register(reg_name)
            if issymbolic(value):
                result += f"{reg_name:3s}: {CFAIL}{visitors.pretty_print(value, depth=10)}{CEND}\n"
            else:
                result += f"{reg_name:3s}: 0x{value:016x}\n"
            pos = 0

        pos = 0
        for reg_name in ["CF", "SF", "ZF", "OF", "AF", "PF", "IF", "DF"]:
            value = self.read_register(reg_name)
            if issymbolic(value):
                result += f"{reg_name}: {CFAIL}{visitors.pretty_print(value, depth=10)}{CEND}\n"
            else:
                result += f"{reg_name}: {value:1x}\n"

            pos = 0

        for reg_name in ["CS", "DS", "ES", "SS", "FS", "GS"]:
            base, size, ty = self.get_descriptor(self.read_register(reg_name))
            result += f"{reg_name}: {base:x}, {size:x} ({ty})\n"

        for reg_name in ["FP0", "FP1", "FP2", "FP3", "FP4", "FP5", "FP6", "FP7", "TOP"]:
            value = getattr(self, reg_name)
            result += f"{reg_name:3s}: {value!r}\n"
            pos = 0

        return result

    @property
    def canonical_registers(self):
        regs = ["EAX", "ECX", "EDX", "EBX", "ESP", "EBP", "ESI", "EDI", "EIP"]
        regs.extend(["CS", "DS", "ES", "SS", "FS", "GS"])
        regs.extend(
            ["FP0", "FP1", "FP2", "FP3", "FP4", "FP5", "FP6", "FP7", "FPCW", "FPSW", "FPTAG"]
        )
        regs.extend(
            [
                "XMM0",
                "XMM1",
                "XMM10",
                "XMM11",
                "XMM12",
                "XMM13",
                "XMM14",
                "XMM15",
                "XMM2",
                "XMM3",
                "XMM4",
                "XMM5",
                "XMM6",
                "XMM7",
                "XMM8",
                "XMM9",
            ]
        )
        regs.extend(["CF", "PF", "AF", "ZF", "SF", "IF", "DF", "OF"])
        return tuple(regs)

    @instruction
    def XLATB(cpu):
        """
        Table look-up translation.

        Locates a byte entry in a table in memory, using the contents of the
        AL register as a table index, then copies the contents of the table entry
        back into the AL register. The index in the AL register is treated as
        an unsigned integer. The XLAT and XLATB instructions get the base address
        of the table in memory from either the DS:EBX or the DS:BX registers.
        In 64-bit mode, operation is similar to that in legacy or compatibility mode.
        AL is used to specify the table index (the operand size is fixed at 8 bits).
        RBX, however, is used to specify the table's base address::

                IF address_bit_size = 16
                THEN
                    AL = (DS:BX + ZeroExtend(AL));
                ELSE IF (address_bit_size = 32)
                    AL = (DS:EBX + ZeroExtend(AL)); FI;
                ELSE (address_bit_size = 64)
                    AL = (RBX + ZeroExtend(AL));
                FI;

        :param cpu: current CPU.
        :param dest: destination operand.
        """
        cpu.AL = cpu.read_int(cpu.EBX + Operators.ZEXTEND(cpu.AL, 32), 8)
