from bisect import bisect
from binascii import hexlify, unhexlify
from builtins import map, next, range, object

# from future.builtins import next, bytes  # type: ignore
import copy

DEFAULT_FORK = "petersburg"

"""
    Example use::
        >>> from pyevmasm import *
        >>> disassemble_one('\\x60\\x10')
        Instruction(0x60, 'PUSH', 1, 0, 1, 0, 'Place 1 byte item on stack.', 16, 0)
        >>> assemble_one('PUSH1 0x10')
        Instruction(0x60, 'PUSH', 1, 0, 1, 0, 'Place 1 byte item on stack.', 16, 0)
        >>> tuple(disassemble_all('\\x30\\x31'))
        (Instruction(0x30, 'ADDRESS', 0, 0, 1, 2, 'Get address of currently executing account.', None, 0),
         Instruction(0x31, 'BALANCE', 0, 1, 1, 20, 'Get balance of the given account.', None, 1))
        >>> tuple(assemble_all('ADDRESS\\nBALANCE'))
        (Instruction(0x30, 'ADDRESS', 0, 0, 1, 2, 'Get address of currently executing account.', None, 0),
         Instruction(0x31, 'BALANCE', 0, 1, 1, 20, 'Get balance of the given account.', None, 1))
        >>> assemble_hex('''PUSH1 0x60\n \
                                    BLOCKHASH\n \
                                    MSTORE\n \
                                    PUSH1 0x2\n \
                                    PUSH2 0x100\n \
                                 ''')
        '0x606040526002610100'
        >>> disassemble_hex('0x606040526002610100')
        'PUSH1 0x60\\nBLOCKHASH\\nMSTORE\\nPUSH1 0x2\\nPUSH2 0x100'

"""


class UnknownMnemonicError(Exception):
    pass


class UnknownOpcodeError(Exception):
    pass


class AssembleError(Exception):
    pass


class ParseError(Exception):
    pass


class Instruction(object):
    def __init__(
        self, opcode, name, operand_size, pops, pushes, fee, description, operand=None, pc=0
    ):
        """
        This represents an EVM instruction.
        EVMAsm will create this for you.

        :param opcode: the opcode value
        :param name: instruction name
        :param operand_size: immediate operand size in bytes
        :param pops: number of items popped from the stack
        :param pushes: number of items pushed into the stack
        :param fee: gas fee for the instruction
        :param description: textual description of the instruction
        :param operand: optional immediate operand
        :param pc: optional program counter of this instruction in the program

        Example use::

            >>> instruction = assemble_one('PUSH1 0x10')
            >>> print('Instruction: %s'% instruction)
            >>> print('\tdescription:', instruction.description)
            >>> print('\tgroup:', instruction.group)
            >>> print('\tpc:', instruction.pc)
            >>> print('\tsize:', instruction.size)
            >>> print('\thas_operand:', instruction.has_operand)
            >>> print('\toperand_size:', instruction.operand_size)
            >>> print('\toperand:', instruction.operand)
            >>> print('\tsemantics:', instruction.semantics)
            >>> print('\tpops:', instruction.pops)
            >>> print('\tpushes:', instruction.pushes)
            >>> print('\tbytes:', '0x'+instruction.bytes.encode('hex'))
            >>> print('\twrites to stack:', instruction.writes_to_stack)
            >>> print('\treads from stack:', instruction.reads_from_stack)
            >>> print('\twrites to memory:', instruction.writes_to_memory)
            >>> print('\treads from memory:', instruction.reads_from_memory)
            >>> print('\twrites to storage:', instruction.writes_to_storage)
            >>> print('\treads from storage:', instruction.reads_from_storage)
            >>> print('\tis terminator', instruction.is_terminator)


        """
        self._opcode = opcode
        self._name = name
        self._operand_size = operand_size
        self._pops = pops
        self._pushes = pushes
        self._fee = fee
        self._description = description
        self._operand = operand  # Immediate operand if any
        self._pc = pc

    def __eq__(self, other):
        """ Instructions are equal if all features match """
        return (
            self._opcode == other._opcode
            and self._name == other._name
            and self._operand == other._operand
            and self._operand_size == other._operand_size
            and self._pops == other._pops
            and self._pushes == other._pushes
            and self._fee == other._fee
            and self._pc == other._pc
            and self._description == other._description
        )

    def __repr__(self):
        output = "Instruction(0x{:x}, {}, {:d}, {:d}, {:d}, {:d}, {}, {}, {})".format(
            self._opcode,
            self._name,
            self._operand_size,
            self._pops,
            self._pushes,
            self._fee,
            self._description,
            self._operand,
            self._pc,
        )
        return output

    def __str__(self):
        if self.has_operand:
            if self.operand is not None:
                return "{} 0x{:x}".format(self.name, self.operand)
            else:
                return "{} ???".format(self.name)
        return self.name

    @property
    def opcode(self):
        """ The opcode as an integer """
        return self._opcode

    @property
    def mnemonic(self):
        """ Alias for name """
        return self.name

    @staticmethod
    def _long_name(short_name, operand_size, pops):
        if short_name == "PUSH":
            return "PUSH{:d}".format(operand_size)
        elif short_name == "DUP":
            return "DUP{:d}".format(pops)
        elif short_name == "SWAP":
            return "SWAP{:d}".format(pops - 1)
        elif short_name == "LOG":
            return "LOG{:d}".format(pops - 2)
        return short_name

    @property
    def name(self):
        """ The instruction name/mnemonic """
        return self._long_name(self._name, self._operand_size, self._pops)

    def parse_operand(self, buf):
        """ Parses an operand from buf

            :param buf: a buffer
            :type buf: iterator/generator/string
        """
        buf = iter(buf)
        try:
            operand = 0
            for _ in range(self.operand_size):
                operand <<= 8
                operand |= next(buf)
            self._operand = operand
        except StopIteration:
            raise ParseError("Not enough data for decoding")

    @property
    def operand_size(self):
        """ The immediate operand size """
        return self._operand_size

    @property
    def has_operand(self):
        """ True if the instruction uses an immediate operand"""
        return self.operand_size > 0

    @property
    def operand(self):
        return self._operand

    @operand.setter
    def operand(self, value):
        if self.operand_size != 0 and value is not None:
            mask = (1 << self.operand_size * 8) - 1
            if ~mask & value:
                raise ValueError("operand should be {:d} bits long".format(self.operand_size * 8))
            self._operand = value

    @property
    def pops(self):
        """ Number words popped from the stack """
        return self._pops

    @property
    def pushes(self):
        """ Number words pushed to the stack """
        return self._pushes

    @property
    def size(self):
        """ Size of the encoded instruction """
        return self._operand_size + 1

    @property
    def fee(self):
        """ The basic gas fee of the instruction """
        return self._fee

    @property
    def semantics(self):
        """ Canonical semantics """
        return self._name

    @property
    def description(self):
        """ Colloquial description of the instruction """
        return self._description

    @property
    def bytes(self):
        """ Encoded instruction """
        b = [bytes([self._opcode])]
        for offset in reversed(range(self.operand_size)):
            b.append(bytes([(self.operand >> offset * 8) & 0xFF]))
        return b"".join(b)

    @property
    def pc(self):
        return self._pc

    @pc.setter
    def pc(self, value):
        """Location in the program (optional)"""
        self._pc = value

    @property
    def group(self):
        """ Instruction classification as per the yellow paper """
        classes = {
            0: "Stop and Arithmetic Operations",
            1: "Comparison & Bitwise Logic Operations",
            2: "SHA3",
            3: "Environmental Information",
            4: "Block Information",
            5: "Stack, Memory, Storage and Flow Operations",
            6: "Push Operations",
            7: "Push Operations",
            8: "Duplication Operations",
            9: "Exchange Operations",
            0xA: "Logging Operations",
            0xF: "System operations",
        }
        return classes.get(self.opcode >> 4, "Invalid instruction")

    @property
    def uses_stack(self):
        """ True if the instruction reads/writes from/to the stack """
        return self.reads_from_stack or self.writes_to_stack

    @property
    def reads_from_stack(self):
        """ True if the instruction reads from stack """
        return self.pops > 0

    @property
    def writes_to_stack(self):
        """ True if the instruction writes to the stack """
        return self.pushes > 0

    @property
    def writes_to_memory(self):
        """ True if the instruction writes to memory """
        return self.semantics in {
            "MSTORE",
            "MSTORE8",
            "CALLDATACOPY",
            "CODECOPY",
            "EXTCODECOPY",
            "RETURNDATACOPY",
            "CALL",
            "STATICCALL",
            "DELEGATECALL",
            "CALLCODE",
        }

    @property
    def reads_from_memory(self):
        """ True if the instruction reads from memory """
        return self.semantics in {
            "MLOAD",
            "CREATE",
            "CALL",
            "STATICCALL",
            "DELEGATECALL",
            "CALLCODE",
            "RETURN",
            "REVERT",
        }

    @property
    def writes_to_storage(self):
        """ True if the instruction writes to the storage """
        return self.semantics == "SSTORE"

    @property
    def reads_from_storage(self):
        """ True if the instruction reads from the storage """
        return self.semantics == "SLOAD"

    @property
    def is_terminator(self):
        """ True if the instruction is a basic block terminator """
        return self.semantics in {
            "RETURN",
            "STOP",
            "INVALID",
            "JUMP",
            "JUMPI",
            "SELFDESTRUCT",
            "REVERT",
        }

    @property
    def is_endtx(self):
        """ True if the instruction is a transaction terminator """
        return self.semantics in {"RETURN", "STOP", "INVALID", "SELFDESTRUCT", "REVERT"}

    @property
    def is_starttx(self):
        """ True if the instruction is a transaction initiator """
        return self.semantics in {
            "CREATE",
            "CREATE2",
            "CALL",
            "CALLCODE",
            "DELEGATECALL",
            "STATICCALL",
        }

    @property
    def is_branch(self):
        """ True if the instruction is a jump """
        return self.semantics in {"JUMP", "JUMPI"}

    @property
    def is_environmental(self):
        """ True if the instruction access enviromental data """
        return self.group == "Environmental Information"

    @property
    def is_system(self):
        """ True if the instruction is a system operation """
        return self.group == "System operations"

    @property
    def uses_block_info(self):
        """ True if the instruction access block information"""
        return self.group == "Block Information"

    @property
    def is_arithmetic(self):
        """ True if the instruction is an arithmetic operation """
        return self.semantics in {
            "ADD",
            "MUL",
            "SUB",
            "DIV",
            "SDIV",
            "MOD",
            "SMOD",
            "ADDMOD",
            "MULMOD",
            "EXP",
            "SIGNEXTEND",
            "SHL",
            "SHR",
            "SAR",
        }


def assemble_one(asmcode, pc=0, fork=DEFAULT_FORK):
    """ Assemble one EVM instruction from its textual representation.

        :param asmcode: assembly code for one instruction
        :type asmcode: str
        :param pc: program counter of the instruction(optional)
        :type pc: int
        :param fork: fork name (optional)
        :type fork: str
        :return: An Instruction object
        :rtype: Instruction

        Example use::

            >>> print assemble_one('LT')


    """
    try:
        instruction_table = instruction_tables[fork]
        asmcode = asmcode.strip().split(" ")
        instr = instruction_table[asmcode[0].upper()]
        if pc:
            instr.pc = pc
        if instr.operand_size > 0:
            assert len(asmcode) == 2
            instr.operand = int(asmcode[1], 0)
        return instr
    except Exception:
        raise AssembleError("Something wrong at pc {:d}".format(pc))


def assemble_all(asmcode, pc=0, fork=DEFAULT_FORK):
    """ Assemble a sequence of textual representation of EVM instructions

        :param asmcode: assembly code for any number of instructions
        :type asmcode: str
        :param pc: program counter of the first instruction(optional)
        :type pc: int
        :param fork: fork name (optional)
        :type fork: str
        :return: An generator of Instruction objects
        :rtype: generator[Instructions]

        Example use::

            >>> assemble_one('''PUSH1 0x60\n \
                            PUSH1 0x40\n \
                            MSTORE\n \
                            PUSH1 0x2\n \
                            PUSH2 0x108\n \
                            PUSH1 0x0\n \
                            POP\n \
                            SSTORE\n \
                            PUSH1 0x40\n \
                            MLOAD\n \
                            ''')

    """
    asmcode = asmcode.split("\n")
    asmcode = iter(asmcode)
    for line in asmcode:
        if not line.strip():
            continue
        instr = assemble_one(line, pc=pc, fork=fork)
        yield instr
        pc += instr.size


def disassemble_one(bytecode, pc=0, fork=DEFAULT_FORK):
    """ Disassemble a single instruction from a bytecode

        :param bytecode: the bytecode stream
        :type bytecode: str | bytes | bytearray | iterator
        :param pc: program counter of the instruction(optional)
        :type pc: int
        :param fork: fork name (optional)
        :type fork: str
        :return: an Instruction object
        :rtype: Instruction

        Example use::

            >>> print disassemble_one('\x60\x10')

    """
    instruction_table = instruction_tables[fork]
    if isinstance(bytecode, bytes):
        bytecode = bytearray(bytecode)
    if isinstance(bytecode, str):
        bytecode = bytearray(bytecode.encode("latin-1"))

    bytecode = iter(bytecode)
    try:
        opcode = next(bytecode)
    except StopIteration:
        return

    assert isinstance(opcode, int)

    instruction = copy.copy(instruction_table.get(opcode, None))
    if instruction is None:
        instruction = Instruction(opcode, "INVALID", 0, 0, 0, 0, "Unspecified invalid instruction.")
    instruction.pc = pc

    try:
        if instruction.has_operand:
            instruction.parse_operand(bytecode)
    except ParseError:
        instruction = None
    finally:
        return instruction


def disassemble_all(bytecode, pc=0, fork=DEFAULT_FORK):
    """ Disassemble all instructions in bytecode

        :param bytecode: an evm bytecode (binary)
        :type bytecode: str | bytes | bytearray | iterator
        :param pc: program counter of the first instruction(optional)
        :type pc: int
        :param fork: fork name (optional)
        :type fork: str
        :return: An generator of Instruction objects
        :rtype: list[Instruction]

        Example use::

            >>> for inst in disassemble_all(bytecode):
            ...    print(instr)

            ...
            PUSH1 0x60
            PUSH1 0x40
            MSTORE
            PUSH1 0x2
            PUSH2 0x108
            PUSH1 0x0
            POP
            SSTORE
            PUSH1 0x40
            MLOAD


    """
    if isinstance(bytecode, bytes):
        bytecode = bytearray(bytecode)
    if isinstance(bytecode, str):
        bytecode = bytearray(bytecode.encode("latin-1"))

    bytecode = iter(bytecode)
    while True:
        instr = disassemble_one(bytecode, pc=pc, fork=fork)
        if not instr:
            return
        pc += instr.size
        yield instr


def disassemble(bytecode, pc=0, fork=DEFAULT_FORK):
    """ Disassemble an EVM bytecode

        :param bytecode: binary representation of an evm bytecode
        :type bytecode: str | bytes | bytearray
        :param pc: program counter of the first instruction(optional)
        :type pc: int
        :param fork: fork name (optional)
        :type fork: str
        :return: the text representation of the assembler code

        Example use::

            >>> disassemble("\x60\x60\x60\x40\x52\x60\x02\x61\x01\x00")
            ...
            PUSH1 0x60
            BLOCKHASH
            MSTORE
            PUSH1 0x2
            PUSH2 0x100

    """
    return "\n".join(map(str, disassemble_all(bytecode, pc=pc, fork=fork)))


def assemble(asmcode, pc=0, fork=DEFAULT_FORK):
    """ Assemble an EVM program

        :param asmcode: an evm assembler program
        :type asmcode: str
        :param pc: program counter of the first instruction(optional)
        :type pc: int
        :param fork: fork name (optional)
        :type fork: str
        :return: the hex representation of the bytecode
        :rtype: str

        Example use::

            >>> assemble('''PUSH1 0x60\n \
                                   BLOCKHASH\n \
                                   MSTORE\n \
                                   PUSH1 0x2\n \
                                   PUSH2 0x100\n \
                                ''')
            ...
            b"\x60\x60\x60\x40\x52\x60\x02\x61\x01\x00"
    """
    return b"".join(x.bytes for x in assemble_all(asmcode, pc=pc, fork=fork))


def disassemble_hex(bytecode, pc=0, fork=DEFAULT_FORK):
    """ Disassemble an EVM bytecode

        :param bytecode: canonical representation of an evm bytecode (hexadecimal)
        :type bytecode: str
        :param pc: program counter of the first instruction(optional)
        :type pc: int
        :param fork: fork name (optional)
        :type fork: str
        :return: the text representation of the assembler code
        :rtype: str

        Example use::

            >>> disassemble_hex("0x6060604052600261010")
            ...
            PUSH1 0x60
            BLOCKHASH
            MSTORE
            PUSH1 0x2
            PUSH2 0x100

    """
    if bytecode.startswith("0x"):
        bytecode = bytecode[2:]
    bytecode = unhexlify(bytecode)
    return disassemble(bytecode, pc=pc, fork=fork)


def assemble_hex(asmcode, pc=0, fork=DEFAULT_FORK):
    """ Assemble an EVM program

        :param asmcode: an evm assembler program
        :type asmcode: str | iterator[Instruction]
        :param pc: program counter of the first instruction(optional)
        :type pc: int
        :param fork: fork name (optional)
        :type fork: str
        :return: the hex representation of the bytecode
        :rtype: str

        Example use::

            >>> assemble_hex('''PUSH1 0x60\n \
                                       BLOCKHASH\n \
                                       MSTORE\n \
                                       PUSH1 0x2\n \
                                       PUSH2 0x100\n \
                                    ''')
            ...
            "0x6060604052600261010"
    """
    if isinstance(asmcode, list):
        return "0x" + hexlify(b"".join([x.bytes for x in asmcode])).decode("ascii")
    return "0x" + hexlify(assemble(asmcode, pc=pc, fork=fork)).decode("ascii")


class InstructionTable:
    """
    EVM Instruction factory
        Implements an immutable, iterable instruction LUT that can be indexed by both mnemonic or opcode.

    Example::

        >>> from pyevmasm import instruction_tables
        >>> instruction_table = instruction_tables['byzantium']
        >>> instruction_table[0]
        Instruction(0x0, 'STOP', 0, 0, 0, 0, 'Halts execution.', None, 0)
        >>> instruction_table['STOP']
        Instruction(0x0, 'STOP', 0, 0, 0, 0, 'Halts execution.', None, 0)
        >>> i = instruction_table.__iter__()
        >>> i.__next__()
        Instruction(0x0, 'STOP', 0, 0, 0, 0, 'Halts execution.', None, 0)
        >>> i.__next__()
        Instruction(0x1, 'ADD', 0, 2, 1, 3, 'Addition operation.', None, 0)
        >>> i.__next__()
        Instruction(0x2, 'MUL', 0, 2, 1, 5, 'Multiplication operation.', None, 0)
        >>> i.__next__()
        Instruction(0x3, 'SUB', 0, 2, 1, 3, 'Subtraction operation.', None, 0)

    """

    __slots__ = ("_instruction_list", "__name_to_opcode")

    def __init__(self, *args, **kwargs):
        previous_fork = kwargs.get("previous_fork", None)

        self._instruction_list = {}
        self.__name_to_opcode = None

        if previous_fork is not None:
            if not isinstance(previous_fork, self.__class__):
                raise TypeError("{} expected".format(self.__class__))
            self._instruction_list.update(previous_fork._instruction_list)

        self._instruction_list.update(args[0])
        self.__name_to_opcode = None

    @property
    def _name_to_opcode(self):
        if self.__name_to_opcode is None:
            self.__name_to_opcode = {}
            for (
                opcode,
                (name, operand_size, pops, pushes, gas, description),
            ) in self._instruction_list.items():
                long_name = Instruction._long_name(name, operand_size, pops)
                self.__name_to_opcode[long_name] = opcode
        return self.__name_to_opcode

    def _search_by_name(self, k):
        return self._search_by_opcode(self._name_to_opcode[k])

    def _search_by_opcode(self, k):
        return (k,) + self._instruction_list[k]

    def _search(self, k):
        try:
            value = self._search_by_opcode(k)
        except KeyError:
            value = self._search_by_name(k)
        return value

    def __getitem__(self, k):
        return Instruction(*self._search(k))

    def get(self, k, default=None):
        try:
            return Instruction(*self._search(k))
        except KeyError:
            return default

    def __contains__(self, k):
        return k in self._instruction_list or k in self._name_to_opcode

    def __iter__(self):
        for k in self.keys():
            yield Instruction(*((k,) + self._instruction_list[k]))

    def keys(self):
        return sorted(self._instruction_list.keys())

    def __repr__(self):
        return repr(self._instruction_list)


# from http://gavwood.com/paper.pdf
frontier_instruction_table = {
    0x0: ("STOP", 0, 0, 0, 0, "Halts execution."),
    0x1: ("ADD", 0, 2, 1, 3, "Addition operation."),
    0x2: ("MUL", 0, 2, 1, 5, "Multiplication operation."),
    0x3: ("SUB", 0, 2, 1, 3, "Subtraction operation."),
    0x4: ("DIV", 0, 2, 1, 5, "Integer division operation."),
    0x5: ("SDIV", 0, 2, 1, 5, "Signed integer division operation (truncated)."),
    0x6: ("MOD", 0, 2, 1, 5, "Modulo remainder operation."),
    0x7: ("SMOD", 0, 2, 1, 5, "Signed modulo remainder operation."),
    0x8: ("ADDMOD", 0, 3, 1, 8, "Modulo addition operation."),
    0x9: ("MULMOD", 0, 3, 1, 8, "Modulo multiplication operation."),
    0xA: ("EXP", 0, 2, 1, 10, "Exponential operation."),
    0xB: ("SIGNEXTEND", 0, 2, 1, 5, "Extend length of two's complement signed integer."),
    0x10: ("LT", 0, 2, 1, 3, "Less-than comparision."),
    0x11: ("GT", 0, 2, 1, 3, "Greater-than comparision."),
    0x12: ("SLT", 0, 2, 1, 3, "Signed less-than comparision."),
    0x13: ("SGT", 0, 2, 1, 3, "Signed greater-than comparision."),
    0x14: ("EQ", 0, 2, 1, 3, "Equality comparision."),
    0x15: ("ISZERO", 0, 1, 1, 3, "Simple not operator."),
    0x16: ("AND", 0, 2, 1, 3, "Bitwise AND operation."),
    0x17: ("OR", 0, 2, 1, 3, "Bitwise OR operation."),
    0x18: ("XOR", 0, 2, 1, 3, "Bitwise XOR operation."),
    0x19: ("NOT", 0, 1, 1, 3, "Bitwise NOT operation."),
    0x1A: ("BYTE", 0, 2, 1, 3, "Retrieve single byte from word."),
    0x20: ("SHA3", 0, 2, 1, 30, "Compute Keccak-256 hash."),
    0x30: ("ADDRESS", 0, 0, 1, 2, "Get address of currently executing account."),
    0x31: ("BALANCE", 0, 1, 1, 20, "Get balance of the given account."),
    0x32: ("ORIGIN", 0, 0, 1, 2, "Get execution origination address."),
    0x33: ("CALLER", 0, 0, 1, 2, "Get caller address."),
    0x34: (
        "CALLVALUE",
        0,
        0,
        1,
        2,
        "Get deposited value by the instruction/transaction responsible for this execution.",
    ),
    0x35: ("CALLDATALOAD", 0, 1, 1, 3, "Get input data of current environment."),
    0x36: ("CALLDATASIZE", 0, 0, 1, 2, "Get size of input data in current environment."),
    0x37: ("CALLDATACOPY", 0, 3, 0, 3, "Copy input data in current environment to memory."),
    0x38: ("CODESIZE", 0, 0, 1, 2, "Get size of code running in current environment."),
    0x39: ("CODECOPY", 0, 3, 0, 3, "Copy code running in current environment to memory."),
    0x3A: ("GASPRICE", 0, 0, 1, 2, "Get price of gas in current environment."),
    0x3B: ("EXTCODESIZE", 0, 1, 1, 20, "Get size of an account's code."),
    0x3C: ("EXTCODECOPY", 0, 4, 0, 20, "Copy an account's code to memory."),
    0x40: ("BLOCKHASH", 0, 1, 1, 20, "Get the hash of one of the 256 most recent complete blocks."),
    0x41: ("COINBASE", 0, 0, 1, 2, "Get the block's beneficiary address."),
    0x42: ("TIMESTAMP", 0, 0, 1, 2, "Get the block's timestamp."),
    0x43: ("NUMBER", 0, 0, 1, 2, "Get the block's number."),
    0x44: ("DIFFICULTY", 0, 0, 1, 2, "Get the block's difficulty."),
    0x45: ("GASLIMIT", 0, 0, 1, 2, "Get the block's gas limit."),
    0x50: ("POP", 0, 1, 0, 2, "Remove item from stack."),
    0x51: ("MLOAD", 0, 1, 1, 3, "Load word from memory."),
    0x52: ("MSTORE", 0, 2, 0, 3, "Save word to memory."),
    0x53: ("MSTORE8", 0, 2, 0, 3, "Save byte to memory."),
    0x54: ("SLOAD", 0, 1, 1, 50, "Load word from storage."),
    0x55: ("SSTORE", 0, 2, 0, 0, "Save word to storage."),
    0x56: ("JUMP", 0, 1, 0, 8, "Alter the program counter."),
    0x57: ("JUMPI", 0, 2, 0, 10, "Conditionally alter the program counter."),
    0x58: ("GETPC", 0, 0, 1, 2, "Get the value of the program counter prior to the increment."),
    0x59: ("MSIZE", 0, 0, 1, 2, "Get the size of active memory in bytes."),
    0x5A: (
        "GAS",
        0,
        0,
        1,
        2,
        "Get the amount of available gas, including the corresponding reduction the amount of available gas.",
    ),
    0x5B: ("JUMPDEST", 0, 0, 0, 1, "Mark a valid destination for jumps."),
    0x60: ("PUSH", 1, 0, 1, 3, "Place 1 byte item on stack."),
    0x61: ("PUSH", 2, 0, 1, 3, "Place 2-byte item on stack."),
    0x62: ("PUSH", 3, 0, 1, 3, "Place 3-byte item on stack."),
    0x63: ("PUSH", 4, 0, 1, 3, "Place 4-byte item on stack."),
    0x64: ("PUSH", 5, 0, 1, 3, "Place 5-byte item on stack."),
    0x65: ("PUSH", 6, 0, 1, 3, "Place 6-byte item on stack."),
    0x66: ("PUSH", 7, 0, 1, 3, "Place 7-byte item on stack."),
    0x67: ("PUSH", 8, 0, 1, 3, "Place 8-byte item on stack."),
    0x68: ("PUSH", 9, 0, 1, 3, "Place 9-byte item on stack."),
    0x69: ("PUSH", 10, 0, 1, 3, "Place 10-byte item on stack."),
    0x6A: ("PUSH", 11, 0, 1, 3, "Place 11-byte item on stack."),
    0x6B: ("PUSH", 12, 0, 1, 3, "Place 12-byte item on stack."),
    0x6C: ("PUSH", 13, 0, 1, 3, "Place 13-byte item on stack."),
    0x6D: ("PUSH", 14, 0, 1, 3, "Place 14-byte item on stack."),
    0x6E: ("PUSH", 15, 0, 1, 3, "Place 15-byte item on stack."),
    0x6F: ("PUSH", 16, 0, 1, 3, "Place 16-byte item on stack."),
    0x70: ("PUSH", 17, 0, 1, 3, "Place 17-byte item on stack."),
    0x71: ("PUSH", 18, 0, 1, 3, "Place 18-byte item on stack."),
    0x72: ("PUSH", 19, 0, 1, 3, "Place 19-byte item on stack."),
    0x73: ("PUSH", 20, 0, 1, 3, "Place 20-byte item on stack."),
    0x74: ("PUSH", 21, 0, 1, 3, "Place 21-byte item on stack."),
    0x75: ("PUSH", 22, 0, 1, 3, "Place 22-byte item on stack."),
    0x76: ("PUSH", 23, 0, 1, 3, "Place 23-byte item on stack."),
    0x77: ("PUSH", 24, 0, 1, 3, "Place 24-byte item on stack."),
    0x78: ("PUSH", 25, 0, 1, 3, "Place 25-byte item on stack."),
    0x79: ("PUSH", 26, 0, 1, 3, "Place 26-byte item on stack."),
    0x7A: ("PUSH", 27, 0, 1, 3, "Place 27-byte item on stack."),
    0x7B: ("PUSH", 28, 0, 1, 3, "Place 28-byte item on stack."),
    0x7C: ("PUSH", 29, 0, 1, 3, "Place 29-byte item on stack."),
    0x7D: ("PUSH", 30, 0, 1, 3, "Place 30-byte item on stack."),
    0x7E: ("PUSH", 31, 0, 1, 3, "Place 31-byte item on stack."),
    0x7F: ("PUSH", 32, 0, 1, 3, "Place 32-byte (full word) item on stack."),
    0x80: ("DUP", 0, 1, 2, 3, "Duplicate 1st stack item."),
    0x81: ("DUP", 0, 2, 3, 3, "Duplicate 2nd stack item."),
    0x82: ("DUP", 0, 3, 4, 3, "Duplicate 3rd stack item."),
    0x83: ("DUP", 0, 4, 5, 3, "Duplicate 4th stack item."),
    0x84: ("DUP", 0, 5, 6, 3, "Duplicate 5th stack item."),
    0x85: ("DUP", 0, 6, 7, 3, "Duplicate 6th stack item."),
    0x86: ("DUP", 0, 7, 8, 3, "Duplicate 7th stack item."),
    0x87: ("DUP", 0, 8, 9, 3, "Duplicate 8th stack item."),
    0x88: ("DUP", 0, 9, 10, 3, "Duplicate 9th stack item."),
    0x89: ("DUP", 0, 10, 11, 3, "Duplicate 10th stack item."),
    0x8A: ("DUP", 0, 11, 12, 3, "Duplicate 11th stack item."),
    0x8B: ("DUP", 0, 12, 13, 3, "Duplicate 12th stack item."),
    0x8C: ("DUP", 0, 13, 14, 3, "Duplicate 13th stack item."),
    0x8D: ("DUP", 0, 14, 15, 3, "Duplicate 14th stack item."),
    0x8E: ("DUP", 0, 15, 16, 3, "Duplicate 15th stack item."),
    0x8F: ("DUP", 0, 16, 17, 3, "Duplicate 16th stack item."),
    0x90: ("SWAP", 0, 2, 2, 3, "Exchange 1st and 2nd stack items."),
    0x91: ("SWAP", 0, 3, 3, 3, "Exchange 1st and 3rd stack items."),
    0x92: ("SWAP", 0, 4, 4, 3, "Exchange 1st and 4th stack items."),
    0x93: ("SWAP", 0, 5, 5, 3, "Exchange 1st and 5th stack items."),
    0x94: ("SWAP", 0, 6, 6, 3, "Exchange 1st and 6th stack items."),
    0x95: ("SWAP", 0, 7, 7, 3, "Exchange 1st and 7th stack items."),
    0x96: ("SWAP", 0, 8, 8, 3, "Exchange 1st and 8th stack items."),
    0x97: ("SWAP", 0, 9, 9, 3, "Exchange 1st and 9th stack items."),
    0x98: ("SWAP", 0, 10, 10, 3, "Exchange 1st and 10th stack items."),
    0x99: ("SWAP", 0, 11, 11, 3, "Exchange 1st and 11th stack items."),
    0x9A: ("SWAP", 0, 12, 12, 3, "Exchange 1st and 12th stack items."),
    0x9B: ("SWAP", 0, 13, 13, 3, "Exchange 1st and 13th stack items."),
    0x9C: ("SWAP", 0, 14, 14, 3, "Exchange 1st and 14th stack items."),
    0x9D: ("SWAP", 0, 15, 15, 3, "Exchange 1st and 15th stack items."),
    0x9E: ("SWAP", 0, 16, 16, 3, "Exchange 1st and 16th stack items."),
    0x9F: ("SWAP", 0, 17, 17, 3, "Exchange 1st and 17th stack items."),
    0xA0: ("LOG", 0, 2, 0, 375, "Append log record with no topics."),
    0xA1: ("LOG", 0, 3, 0, 750, "Append log record with one topic."),
    0xA2: ("LOG", 0, 4, 0, 1125, "Append log record with two topics."),
    0xA3: ("LOG", 0, 5, 0, 1500, "Append log record with three topics."),
    0xA4: ("LOG", 0, 6, 0, 1875, "Append log record with four topics."),
    0xF0: ("CREATE", 0, 3, 1, 32000, "Create a new account with associated code."),
    0xF1: ("CALL", 0, 7, 1, 40, "Message-call into an account."),
    0xF2: (
        "CALLCODE",
        0,
        7,
        1,
        40,
        "Message-call into this account with alternative account's code.",
    ),
    0xF3: ("RETURN", 0, 2, 0, 0, "Halt execution returning output data."),
    0xFE: ("INVALID", 0, 0, 0, 0, "Designated invalid instruction."),
    0xFF: ("SELFDESTRUCT", 0, 1, 0, 0, "Halt execution and register account for later deletion."),
}
frontier_instruction_table = InstructionTable(frontier_instruction_table)  # type: ignore

homestead_instruction_table = {
    0xF4: (
        "DELEGATECALL",
        0,
        6,
        1,
        40,
        "Message-call into this account with an alternative account's code, but persisting into this account with an alternative account's code.",
    )
}
homestead_instruction_table = InstructionTable(
    homestead_instruction_table, previous_fork=frontier_instruction_table
)  # type: ignore

tangerine_whistle_instruction_table = {
    0x3B: ("EXTCODESIZE", 0, 1, 1, 700, "Get size of an account's code."),
    0x3C: ("EXTCODECOPY", 0, 4, 0, 700, "Copy an account's code to memory."),
    0x31: ("BALANCE", 0, 1, 1, 400, "Get balance of the given account."),
    0x54: ("SLOAD", 0, 1, 1, 200, "Load word from storage."),
    0xF0: ("CREATE", 0, 3, 1, 32000, "Create a new account with associated code."),
    0xF1: ("CALL", 0, 7, 1, 700, "Message-call into an account."),
    0xF2: (
        "CALLCODE",
        0,
        7,
        1,
        700,
        "Message-call into this account with alternative account's code.",
    ),
    0xF4: (
        "DELEGATECALL",
        0,
        6,
        1,
        700,
        "Message-call into this account with an alternative account's code, but persisting into this account with an alternative account's code.",
    ),
    0xFF: (
        "SELFDESTRUCT",
        0,
        1,
        0,
        5000,
        "Halt execution and register account for later deletion.",
    ),
}
tangerine_whistle_instruction_table = InstructionTable(  # type: ignore
    tangerine_whistle_instruction_table, previous_fork=homestead_instruction_table
)

spurious_dragon_instruction_table = {}  # type: ignore
spurious_dragon_instruction_table = InstructionTable(  # type: ignore
    spurious_dragon_instruction_table, previous_fork=tangerine_whistle_instruction_table
)

byzantium_instruction_table = {
    0x3D: (
        "RETURNDATASIZE",
        0,
        0,
        1,
        2,
        "Get size of output data from the previous call from the current environment.",
    ),
    0x3E: ("RETURNDATACOPY", 0, 3, 0, 3, "Copy output data from the previous call to memory."),
    0xFA: ("STATICCALL", 0, 6, 1, 40, "Static message-call into an account."),
    0xFD: (
        "REVERT",
        0,
        2,
        0,
        0,
        "Stop execution and revert state changes, without consuming all provided gas and providing a reason.",
    ),
}
byzantium_instruction_table = InstructionTable(  # type: ignore
    byzantium_instruction_table, previous_fork=spurious_dragon_instruction_table
)

constantinople_instruction_table = {
    0x1B: ("SHL", 0, 2, 1, 3, "Shift left."),
    0x1C: ("SHR", 0, 2, 1, 3, "Logical shift right."),
    0x1D: ("SAR", 0, 2, 1, 3, "Arithmetic shift right"),
    0x3F: ("EXTCODEHASH", 0, 1, 1, 400, "Get hash of code"),
    0xF5: (
        "CREATE2",
        0,
        3,
        1,
        32000,
        "Behaves identically to CREATE, except using keccak256( 0xff ++ address ++ salt ++ keccak256(init_code)))[12:] as the address where the contract is initialized at",
    ),
}
constantinople_instruction_table = InstructionTable(  # type: ignore
    constantinople_instruction_table, previous_fork=byzantium_instruction_table
)

serenity_instruction_table = InstructionTable({}, previous_fork=constantinople_instruction_table)

istanbul_instruction_table = {
    0x31: ("BALANCE", 0, 1, 1, 700, "Get balance of the given account."),
    0x3F: ("EXTCODEHASH", 0, 1, 1, 700, "Get hash of code"),
    0x46: ("CHAINID", 0, 0, 1, 2, "Get current chainid."),
    0x47: ("SELFBALANCE", 0, 0, 1, 5, "Balance of the current address."),
    0x54: ("SLOAD", 0, 1, 1, 800, "Load word from storage."),
}
istanbul_instruction_table = InstructionTable(  # type: ignore
    istanbul_instruction_table, previous_fork=serenity_instruction_table
)

accepted_forks = (
    "frontier",
    "homestead",
    "tangerine_whistle",
    "spurious_dragon",
    "byzantium",
    "constantinople",
    "petersburg",
    "serenity",
    "istanbul",
)


instruction_tables = {
    "frontier": frontier_instruction_table,
    "homestead": homestead_instruction_table,
    "tangerine_whistle": tangerine_whistle_instruction_table,
    "spurious_dragon": spurious_dragon_instruction_table,
    "byzantium": byzantium_instruction_table,
    "constantinople": constantinople_instruction_table,
    "petersburg": constantinople_instruction_table,  # constantinople table is intentional here: those two are aliases
    "serenity": serenity_instruction_table,
    "istanbul": istanbul_instruction_table,
}


def block_to_fork(block_number):
    """ Convert block number to fork name.

        :param block_number: block number
        :type block_number: int
        :return: fork name
        :rtype: str

        Example use::

            >>> block_to_fork(0)
            ...
            "frontier"
            >>> block_to_fork(4370000)
            ...
            "byzantium"
            >>> block_to_fork(4370001)
            ...
            "byzantium"
    """
    forks_by_block = {
        0: "frontier",
        1150000: "homestead",
        # 1920000 Dao
        2463000: "tangerine_whistle",
        2675000: "spurious_dragon",
        4370000: "byzantium",
        # 7280000: "constantinople", # Same Block as petersburg, commented to avoid conflicts
        7280000: "petersburg",
        9999999: "serenity",  # to be replaced after Serenity launch
    }
    fork_names = list(forks_by_block.values())
    fork_blocks = list(forks_by_block.keys())
    return fork_names[bisect(fork_blocks, block_number) - 1]
