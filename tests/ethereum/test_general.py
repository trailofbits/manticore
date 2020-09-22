import binascii
import unittest
import subprocess
import pkg_resources
from contextlib import contextmanager
from pathlib import Path

import os
import pyevmasm as EVMAsm
import re
import shutil
import struct
import tempfile

from manticore import ManticoreError
from manticore.core.plugin import Plugin
from manticore.core.smtlib import ConstraintSet, operators
from manticore.core.smtlib import Z3Solver
from manticore.core.smtlib.expression import BitVec
from manticore.core.smtlib.visitors import to_constant
from manticore.core.state import TerminateState
from manticore.ethereum import (
    ManticoreEVM,
    State,
    DetectExternalCallAndLeak,
    DetectIntegerOverflow,
    Detector,
    NoAliveStates,
    ABI,
    EthereumError,
    EVMContract,
    verifier,
)
from manticore.ethereum.plugins import FilterFunctions
from manticore.ethereum.solidity import SolidityMetadata
from manticore.platforms import evm
from manticore.platforms.evm import EVMWorld, ConcretizeArgument, concretized_args, Return, Stop
from manticore.utils.deprecated import ManticoreDeprecationWarning
from manticore.utils import config
import io
import contextlib


solver = Z3Solver.instance()

THIS_DIR = os.path.dirname(os.path.abspath(__file__))


@contextmanager
def disposable_mevm(*args, **kwargs):
    mevm = ManticoreEVM(*args, **kwargs)
    try:
        yield mevm
    finally:
        shutil.rmtree(mevm.workspace)


class EthDetectorsIntegrationTest(unittest.TestCase):
    def test_int_ovf(self):
        mevm = ManticoreEVM()
        mevm.register_detector(DetectIntegerOverflow())
        filename = os.path.join(THIS_DIR, "contracts/int_overflow.sol")
        mevm.multi_tx_analysis(filename, tx_limit=1)
        mevm.finalize()
        self.assertEqual(len(mevm.global_findings), 3)
        all_findings = "".join([x[2] for x in mevm.global_findings])
        self.assertIn("Unsigned integer overflow at SUB instruction", all_findings)
        self.assertIn("Unsigned integer overflow at ADD instruction", all_findings)
        self.assertIn("Unsigned integer overflow at MUL instruction", all_findings)


class EthVerifierIntegrationTest(unittest.TestCase):
    def test_propverif(self):
        smtcfg = config.get_group("smt")
        with smtcfg.temp_vals():
            smtcfg.solver = smtcfg.solver.yices

            filename = os.path.join(THIS_DIR, "contracts/prop_verifier.sol")
            f = io.StringIO()
            with contextlib.redirect_stdout(f):
                verifier.manticore_verifier(filename, "TestToken")
            output = f.getvalue()
            self.assertIsNotNone(
                re.compile(
                    r".*crytic_test_balance\s*\|\s*failed\s*\([0-9a-f]+\).*", re.DOTALL
                ).match(output)
            )
            self.assertIsNotNone(
                re.compile(r".*crytic_test_must_revert\s*\|\s*passed.*", re.DOTALL).match(output)
            )

    def test_propverif_external(self) -> None:
        cli_version = subprocess.check_output(("manticore-verifier", "--version")).decode("utf-8")
        cli_version = cli_version.split(
            "Manticore is only supported on Linux. Proceed at your own risk!\n"
        )[-1]
        py_version = f"Manticore {pkg_resources.get_distribution('manticore').version}\n"
        self.assertEqual(cli_version, py_version)


class EthAbiTests(unittest.TestCase):
    _multiprocess_can_split = True

    @staticmethod
    def _pack_int_to_32(x):
        return b"\x00" * 28 + struct.pack(">I", x)

    def test_str_for_string_bytesM_arg(self):
        self.assertEqual(
            ABI.serialize("(string,bytes32)", "hi", "qq"),
            bytearray(
                b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00@qq\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02hi\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"
            ),
        )
        self.assertEqual(
            ABI.serialize("string", "hi"),
            bytearray(
                b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00 \x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02hi\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"
            ),
        )

    def test_parse_tx(self):
        m = ManticoreEVM()
        source_code = """
        contract C{
            mapping(address => uint) balances;
            function test1(address to, uint val){
                balances[to] = val;
            }
        }
        """
        user_account = m.create_account(balance=10 ** 10, name="user_account")
        contract_account = m.solidity_create_contract(
            source_code, owner=user_account, name="contract_account", gas=36225
        )
        calldata = binascii.unhexlify(
            b"9de4886f9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d"
        )
        returndata = b""
        md = m.get_metadata(contract_account)
        self.assertEqual(
            md.parse_tx(calldata, returndata),
            "test1(899826498278242188854817720535123270925417291165, 71291600040229971300002528024956868756719167029433602173313100742126907268509)",
        )

    def test_dyn_address(self):
        d = [
            b"AAAA",  # function hash
            self._pack_int_to_32(32),  # offset to data start
            self._pack_int_to_32(2),  # data start; # of elements
            self._pack_int_to_32(42),  # element 1
            self._pack_int_to_32(43),  # element 2
        ]
        d = b"".join(d)

        func_id, dynargs = ABI.deserialize(type_spec="func(address[])", data=d)

        self.assertEqual(func_id, b"AAAA")
        self.assertEqual(dynargs, ([42, 43],))

    def test_dyn_bytes(self):
        d = [
            b"AAAA",  # function hash
            self._pack_int_to_32(32),  # offset to data start
            self._pack_int_to_32(30),  # data start; # of elements
            b"Z" * 30,
            b"\x00" * 2,
        ]
        d = b"".join(d)

        funcname, dynargs = ABI.deserialize(type_spec="func(bytes)", data=d)

        self.assertEqual(funcname, b"AAAA")
        self.assertEqual(dynargs, (b"Z" * 30,))

    def test_simple_types0(self):
        d = [b"AAAA", self._pack_int_to_32(32), b"\xff" * 32]  # function hash
        d = b"".join(d)
        funcname, dynargs = ABI.deserialize(type_spec="func(uint256,uint256)", data=d)
        # self.assertEqual(funcname, 'AAAA')
        self.assertEqual(dynargs, (32, 2 ** 256 - 1))

    def test_simple_types1(self):
        d = [
            b"AAAA",  # function hash
            self._pack_int_to_32(32),
            b"\xff" * 32,
            b"\xff".rjust(32, b"\0"),
            self._pack_int_to_32(0x424242),
        ]
        d = b"".join(d)
        funcname, dynargs = ABI.deserialize(type_spec="func(uint256,uint256,bool,address)", data=d)
        # self.assertEqual(funcname, 'AAAA')
        self.assertEqual(dynargs, (32, 2 ** 256 - 1, 0xFF, 0x424242))

    def test_simple_types_ints(self):
        d = [
            b"AAAA",  # function hash
            b"\x7f" + b"\xff" * 31,  # int256 max
            b"\x80".ljust(32, b"\0"),  # int256 min
        ]
        d = b"".join(d)
        func_id, dynargs = ABI.deserialize(type_spec="func(int256,int256)", data=d)
        self.assertEqual(func_id, b"AAAA")
        self.assertEqual(dynargs, (2 ** 255 - 1, -(2 ** 255)))

    def test_simple_types_ints_symbolic(self):
        cs = ConstraintSet()
        x = cs.new_bitvec(256, name="x")
        y = cs.new_bitvec(256, name="y")
        # Something is terribly wrong x,y = 10,20
        my_ser = ABI.serialize("(uint,uint)", x, y)
        x_, y_ = ABI.deserialize("(uint,uint)", my_ser)
        self.assertTrue(solver.must_be_true(cs, x == x_))
        self.assertTrue(solver.must_be_true(cs, y == y_))

    def test_simple_types_ints_symbolic1(self):
        cs = ConstraintSet()
        x = cs.new_bitvec(256, name="x")
        # Something is terribly wrong x,y = 10,20
        my_ser = ABI.serialize("uint", x)
        self.assertTrue(solver.must_be_true(cs, my_ser[0] == operators.EXTRACT(x, 256 - 8, 8)))

    def test_address0(self):
        data = f"{chr(0) * 11}\x01\x55{chr(0) * 19}"
        parsed = ABI.deserialize("address", data)
        self.assertEqual(parsed, 0x55 << (8 * 19))

    def test_mult_dyn_types(self):
        d = [
            b"AAAA",  # function hash
            self._pack_int_to_32(0x40),  # offset to data 1 start
            self._pack_int_to_32(0x80),  # offset to data 2 start
            self._pack_int_to_32(10),  # data 1 size
            b"helloworld".ljust(32, b"\x00"),  # data 1
            self._pack_int_to_32(3),  # data 2 size
            self._pack_int_to_32(3),  # data 2
            self._pack_int_to_32(4),
            self._pack_int_to_32(5),
        ]
        d = b"".join(d)

        func_id, dynargs = ABI.deserialize(type_spec="func(bytes,address[])", data=d)

        self.assertEqual(func_id, b"AAAA")
        self.assertEqual(dynargs, (b"helloworld", [3, 4, 5]))

    def test_self_make_and_parse_multi_dyn(self):
        d = ABI.function_call("func(bytes,address[])", b"h" * 50, [1, 1, 2, 2, 3, 3])
        funcid, dynargs = ABI.deserialize(type_spec="func(bytes,address[])", data=d)
        self.assertEqual(funcid, b"\x83}9\xe8")
        self.assertEqual(dynargs, (b"h" * 50, [1, 1, 2, 2, 3, 3]))

    def test_serialize_tuple(self):
        self.assertEqual(ABI.serialize("(int256)", 0x10), b"\0" * 31 + b"\x10")
        self.assertEqual(
            ABI.serialize("(int256,int256)", 0x10, 0x20),
            b"\0" * 31 + b"\x10" + b"\0" * 31 + b"\x20",
        )
        self.assertEqual(
            ABI.serialize("(int256,(int256,int256))", 0x10, (0x20, 0x30)),
            b"\0" * 31 + b"\x10" + b"\0" * 31 + b"\x20" + b"\0" * 31 + b"\x30",
        )

    def test_serialize_basic_types_int(self):
        self.assertEqual(ABI.serialize("int256", 0x10), b"\0" * 31 + b"\x10")
        self.assertEqual(ABI.deserialize("int256", b"\0" * 31 + b"\x10"), 0x10)

        self.assertEqual(ABI.serialize("int256", -0x10), b"\xff" * 31 + b"\xf0")
        self.assertEqual(ABI.deserialize("int256", b"\xff" * 31 + b"\xf0"), -0x10)

    def test_serialize_basic_types_int8(self):
        self.assertEqual(ABI.serialize("int8", 0x10), b"\0" * 31 + b"\x10")
        self.assertEqual(ABI.deserialize("int8", b"\0" * 31 + b"\x10"), 0x10)

        self.assertEqual(ABI.serialize("int8", -0x10), b"\x00" * 31 + b"\xf0")
        self.assertEqual(ABI.deserialize("int8", b"\x00" * 31 + b"\xf0"), -0x10)

    def test_serialize_basic_types_int16(self):
        self.assertEqual(ABI.serialize("int16", 0x100), b"\0" * 30 + b"\x01\x00")
        self.assertEqual(ABI.deserialize("int16", b"\0" * 30 + b"\x01\x00"), 0x100)

        self.assertEqual(ABI.serialize("int16", -0x10), b"\x00" * 30 + b"\xff\xf0")
        self.assertEqual(ABI.deserialize("int16", b"\x00" * 30 + b"\xff\xf0"), -0x10)

    def test_serialize_basic_types_uint(self):
        self.assertEqual(ABI.serialize("uint256", 0x10), b"\0" * 31 + b"\x10")
        self.assertEqual(ABI.deserialize("uint256", b"\0" * 31 + b"\x10"), 0x10)

        self.assertEqual(ABI.serialize("uint256", -0x10), b"\xff" * 31 + b"\xf0")
        self.assertEqual(
            ABI.deserialize("uint256", b"\xff" * 31 + b"\xf0"),
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF0,
        )
        self.assertEqual(
            ABI.deserialize("uint256", b"\xff" * 31 + b"\xf0"),
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF0,
        )
        self.assertNotEqual(ABI.deserialize("uint256", b"\xff" * 31 + b"\xf0"), -0x10)

    def test_parse_invalid_int(self):
        with self.assertRaises(EthereumError):
            ABI.deserialize("intXXX", "\xFF")
            ABI.deserialize("uintXXX", "\xFF")

    def test_parse_invalid_int_too_big(self):
        with self.assertRaises(EthereumError):
            ABI.deserialize("int3000", "\xFF")
            ABI.deserialize("uint3000", "\xFF")

    def test_parse_invalid_int_negative(self):
        with self.assertRaises(EthereumError):
            ABI.deserialize("int-8", "\xFF")
            ABI.deserialize("uint-8", "\xFF")

    def test_parse_invalid_int_not_pow_of_two(self):
        with self.assertRaises(EthereumError):
            ABI.deserialize("int31", "\xFF")
            ABI.deserialize("uint31", "\xFF")

    def test_parse_valid_int0(self):
        ret = ABI.deserialize("int8", "\x10" * 32)
        self.assertEqual(ret, 0x10)

    def test_parse_valid_int1(self):
        ret = ABI.deserialize("int", "\x10".ljust(32, "\0"))
        self.assertEqual(ret, 1 << 252)

    def test_parse_valid_int2(self):
        ret = ABI.deserialize("int40", "\x40\x00\x00\x00\x00".rjust(32, "\0"))
        self.assertEqual(ret, 1 << 38)

    def test_valid_uint(self):
        data = b"\xFF" * 32

        parsed = ABI.deserialize("uint", data)
        self.assertEqual(parsed, 2 ** 256 - 1)

        for i in range(8, 257, 8):
            parsed = ABI.deserialize(f"uint{i}", data)
            self.assertEqual(parsed, 2 ** i - 1)

    def test_empty_types(self):
        name, args = ABI.deserialize("func()", "\0" * 32)
        self.assertEqual(name, b"\x00\x00\x00\x00")
        self.assertEqual(args, tuple())

    def test_function_type(self):
        # setup ABI for function with one function param
        spec = "func(function)"
        func_id = ABI.function_selector(spec)
        # build bytes24 data for function value (address+selector)
        # calls member id lookup on 'Ethereum Foundation Tip Box' (see https://www.ethereum.org/donate)
        address = ABI._serialize_uint(0xFB6916095CA1DF60BB79CE92CE3EA74C37C5D359, 20, padding=0)
        selector = ABI.function_selector("memberId(address)")
        function_ref_data = address + selector + b"\0" * 8
        # build tx call data
        call_data = func_id + function_ref_data
        parsed_func_id, args = ABI.deserialize(spec, call_data)
        self.assertEqual(parsed_func_id, func_id)
        self.assertEqual(((0xFB6916095CA1DF60BB79CE92CE3EA74C37C5D359, selector),), args)

    def test_serialize_fixed_bytes32(self):
        ret = ABI.serialize("bytes32", b"hi")
        self.assertEqual(ret, b"hi".ljust(32, b"\x00"))

    def test_serialize_fixed_bytes2(self):
        ret = ABI.serialize("bytes2", b"aa")
        self.assertEqual(ret, b"aa".ljust(32, b"\x00"))

    def test_serialize_fixed_bytes_less_data(self):
        ret = ABI.serialize("bytes4", b"aa")
        self.assertEqual(ret, b"aa".ljust(32, b"\x00"))

    def test_serialize_fixed_bytes_too_big(self):
        with self.assertRaises(EthereumError):
            ABI.serialize("bytes2", b"hii")

    # test serializing symbolic buffer with bytesM
    def test_serialize_bytesM_symbolic(self):
        cs = ConstraintSet()
        buf = cs.new_array(index_max=17)
        ret = ABI.serialize("bytes32", buf)
        self.assertEqual(solver.minmax(cs, ret[0]), (0, 255))
        self.assertEqual(solver.minmax(cs, ret[17]), (0, 0))

    # test serializing symbolic buffer with bytes
    def test_serialize_bytes_symbolic(self):
        cs = ConstraintSet()
        buf = cs.new_array(index_max=17)
        ret = ABI.serialize("bytes", buf)

        # does the offset field look right?
        self.assertTrue(solver.must_be_true(cs, ret[0:32] == bytearray(b"\x00" * 31 + b"\x20")))

        # does the size field look right?
        self.assertTrue(solver.must_be_true(cs, ret[32:64] == bytearray(b"\x00" * 31 + b"\x11")))

        # does the data field look right?
        self.assertTrue(solver.must_be_true(cs, ret[64 : 64 + 32] == buf + bytearray(b"\x00" * 15)))


class EthInstructionTests(unittest.TestCase):
    def _make(self):
        # Make the constraint store
        constraints = ConstraintSet()
        # make the ethereum world state
        world = evm.EVMWorld(constraints)

        address = 0x222222222222222222222222222222222222200
        caller = origin = 0x111111111111111111111111111111111111100
        price = 0
        value = 10000
        bytecode = b"\x05"
        data = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        return constraints, world, new_vm

    def test_str(self):
        constraints, world, vm = self._make()
        vm_str = """0x222222222222222222222222222222222222200: ---------------------------------------------------------------------------------------------------------------------------------------------------\n0x222222222222222222222222222222222222200: 0x0000: SDIV  Signed integer division operation (truncated).\n0x222222222222222222222222222222222222200: Stack                                                                           Memory\n0x222222222222222222222222222222222222200:                                                                                 0000  00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00   ................\n0x222222222222222222222222222222222222200:                                                                                 0010  00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00   ................\n0x222222222222222222222222222222222222200:                                                                                 0020  00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00   ................\n0x222222222222222222222222222222222222200:                                                                                 0030  00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00   ................\n0x222222222222222222222222222222222222200:                                                                                 0040  00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00   ................\n0x222222222222222222222222222222222222200:                                                                                 0050  00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00   ................\n0x222222222222222222222222222222222222200:                                                                                 0060  00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00   ................\n0x222222222222222222222222222222222222200:                                                                                 0070  00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00   ................\n0x222222222222222222222222222222222222200: Gas: 1000000"""

        self.assertEqual(str(vm), vm_str)

    def test_SDIV(self):
        constraints, world, vm = self._make()
        result = vm.SDIV(
            115792089237316182568066630936765703517573245936339743861833633745570447228928,
            200867255532373784442745261542645325315275374222849104412672,
        )
        self.assertEqual(-64, result)

    def test_SDIVS1(self):
        constraints, world, vm = self._make()
        xx = constraints.new_bitvec(256, name="x")
        yy = constraints.new_bitvec(256, name="y")
        constraints.add(xx == 0x20)
        constraints.add(yy == 1)
        result = vm.SDIV(xx, yy)
        self.assertListEqual(solver.get_all_values(constraints, result), [0x20])

    def test_SDIVS2(self):
        constraints, world, vm = self._make()
        xx = constraints.new_bitvec(256, name="x")
        yy = constraints.new_bitvec(256, name="y")
        constraints.add(xx == 0x20)
        constraints.add(yy == 2)
        result = vm.SDIV(xx, yy)
        self.assertListEqual(solver.get_all_values(constraints, result), [0x10])

    def test_SDIVS3(self):
        constraints, world, vm = self._make()
        xx = constraints.new_bitvec(256, name="x")
        yy = constraints.new_bitvec(256, name="y")
        constraints.add(xx == 0x20)
        constraints.add(yy == -1)
        result = vm.SDIV(xx, yy)
        self.assertListEqual(
            list(map(evm.to_signed, solver.get_all_values(constraints, result))), [-0x20]
        )

    def test_SDIVSx(self):
        x, y = 0x20000000000000000000000000000000000000000000000000, -0x40
        constraints, world, vm = self._make()
        xx = constraints.new_bitvec(256, name="x")
        yy = constraints.new_bitvec(256, name="y")
        constraints.add(xx == x)
        constraints.add(yy == y)

        result = vm.SDIV(xx, yy)
        self.assertListEqual(
            list(map(evm.to_signed, solver.get_all_values(constraints, result))), [vm.SDIV(x, y)]
        )


class EthTests(unittest.TestCase):
    def setUp(self):
        self.mevm = ManticoreEVM()

    def tearDown(self):
        workspace = self.mevm.workspace
        del self.mevm
        shutil.rmtree(workspace)

    def test_solidity_create_contract_no_args(self):
        source_code = "contract A { constructor() {} }"
        owner = self.mevm.create_account(balance=10 ** 10)

        # The default `args=()` makes it pass no arguments
        contract1 = self.mevm.solidity_create_contract(source_code, owner=owner)
        contract2 = self.mevm.solidity_create_contract(source_code, owner=owner)

        self.assertNotEqual(contract1, contract2)

    def test_solidity_create_contract_with_not_payable_constructor_and_balance(self):
        source_code = "contract A { constructor() {} }"
        owner = self.mevm.create_account()

        with self.assertRaises(EthereumError) as e:
            self.mevm.solidity_create_contract(source_code, owner=owner, balance=1)

        expected_exception = (
            "Can't create solidity contract with balance (1) different "
            "than 0 because the contract's constructor is not payable."
        )
        self.assertEqual(str(e.exception), expected_exception)

    def test_solidity_create_contract_with_payable_constructor_and_balance_owner_insufficient_founds(
        self,
    ):
        source_code = "contract A { constructor() public payable {} }"
        owner = self.mevm.create_account(balance=1)

        with self.assertRaises(EthereumError) as e:
            self.mevm.solidity_create_contract(source_code, owner=owner, balance=2)

        expected_exception = (
            f"Can't create solidity contract with balance (2) because "
            f"the owner account ({owner}) has insufficient balance."
        )
        self.assertEqual(str(e.exception), expected_exception)

    def test_solidity_create_contract_with_payable_constructor(self):
        source_code = "contract A { constructor() public payable {} }"
        owner = self.mevm.create_account(balance=10 ** 10)

        contract = self.mevm.solidity_create_contract(source_code, owner=owner, balance=100)

        self.assertIsInstance(contract, EVMContract)

    def test_solidity_create_contract_with_missing_args(self):
        source_code = "contract A { constructor(uint arg) {} }"
        owner = self.mevm.create_account()

        # TODO / FIXME: Probably change ValueError to another one and inform that bad arguments have been passed?
        with self.assertRaises(ValueError) as e:
            self.mevm.solidity_create_contract(source_code, owner=owner)

        self.assertEqual(
            str(e.exception), "The number of values to serialize is less than the number of types"
        )

    def test_create_contract_with_too_much_args(self):
        source_code = "contract A { constructor(uint arg) {} }"
        owner = self.mevm.create_account()

        with self.assertRaises(ValueError) as e:
            self.mevm.solidity_create_contract(source_code, owner=owner, args="(uint32,uint32)")

        self.assertEqual(
            str(e.exception),
            "The number of values to serialize is greater than the number of types",
        )

    def test_create_contract_with_string_args(self):
        source_code = (
            "contract DontWork1{ string s; constructor(string memory s_) public{ s = s_;} }"
        )
        owner = self.mevm.create_account(balance=200000000)

        sym_args = self.mevm.make_symbolic_arguments("(string)")
        contract = self.mevm.solidity_create_contract(source_code, owner=owner, args=sym_args)
        self.assertIsNotNone(contract)
        self.assertEqual(self.mevm.count_states(), 1)

    def test_create_contract_two_instances(self):
        source_code = "contract A { constructor(uint32 arg) {} }"
        owner = self.mevm.create_account(6000000)

        contracts = [
            # When we pass no `args`, the default is `()` so it ends up with `b''` as constructor data
            self.mevm.solidity_create_contract(source_code, owner=owner, args=[1234]),
            self.mevm.solidity_create_contract(source_code, owner=owner, args=[1234]),
            # When we pass args=None, the arguments end up being symbolic
            # NOTE: This is what CLI does
            self.mevm.solidity_create_contract(source_code, owner=owner, args=None),
            self.mevm.solidity_create_contract(source_code, owner=owner, args=None),
        ]

        # They must have unique address and name
        self.assertEqual(len(contracts), len(set(c.address for c in contracts)))
        self.assertEqual(len(contracts), len(set(c.name_ for c in contracts)))

    def test_contract_create_and_call_underscore_function(self):
        source_code = "contract A { function _f(uint x) returns (uint) { return x + 0x1234; } }"

        owner = self.mevm.create_account(balance=300000000)
        contract = self.mevm.solidity_create_contract(source_code, owner=owner, args=[])

        contract._f(123)

    def test_contract_create_and_access_non_existing_function(self):
        source_code = "contract A {}"

        owner = self.mevm.create_account(balance=10000000)
        contract = self.mevm.solidity_create_contract(source_code, owner=owner, args=[])

        with self.assertRaises(AttributeError) as e:
            _ = contract.xyz

        self.assertEqual(str(e.exception), "The contract contract0 doesn't have xyz function.")

    def test_invalid_function_signature(self):
        source_code = """
        contract Test{

            function ret(uint256) returns(uint256){
                return 1;
            }

        }
        """
        user_account = self.mevm.create_account(balance=10 ** 10)
        contract_account = self.mevm.solidity_create_contract(source_code, owner=user_account)
        with self.assertRaises(EthereumError) as ctx:
            contract_account.ret(self.mevm.make_symbolic_value(), signature="(uint8)")
        self.assertTrue(str(ctx.exception))

    def test_selfdestruct_decoupled_account_delete(self):
        source_code = """
            contract C{
                function d( ){
                    selfdestruct(0);
                }
                function g() returns(uint) {
                    return 42 ;
                }
            }

            contract D{
                C c;
                constructor () {
                    c = new C();
                }
                function t () returns(uint){
                    c.d();
                    return c.g();
                }
            }
        """

        user_account = self.mevm.create_account(balance=1000000000000000000000)
        contract_account = self.mevm.solidity_create_contract(
            source_code, owner=user_account, contract_name="D", gas=900000
        )
        contract_account.t(
            gas=9000000
        )  # this does not return nothing as it may create several states

        # nothing reverted and we end up with a single state
        self.assertEqual(self.mevm.count_states(), 1)

        # Check that calling t() returned a 42
        # That is that calling a selfdestructed contract works as the account
        # is actually deleted at the end of the human tx
        self.assertEqual(
            ABI.deserialize("uint", to_constant(self.mevm.world.transactions[-1].return_data)), 42
        )

    def test_create_bytecode_contract(self):
        account = self.mevm.create_account(code="0x00AAFF")
        self.assertIsNotNone(account)

        account = self.mevm.create_account(code=bytes("0x00AAFF", "utf-8"))
        self.assertIsNotNone(account)

        with self.assertRaises(EthereumError) as ctx:
            self.mevm.create_account(code=bytearray("0x00AAFF", "utf-8"))

    def test_states_querying_1325(self):
        """
        Tests issue 1325.
        """
        owner = self.mevm.create_account(balance=10 ** 10)
        A = self.mevm.solidity_create_contract(
            "contract A { function foo() { revert(); } }", owner=owner
        )

        self.assertEqual(self.mevm.count_ready_states(), 1)
        self.assertEqual(self.mevm.count_terminated_states(), 0)
        self.assertEqual(self.mevm.count_states(), 1)

        A.foo()

        def assert_all():
            self.assertEqual(self.mevm.count_ready_states(), 0)
            self.assertEqual(self.mevm.count_terminated_states(), 1)
            self.assertEqual(self.mevm.count_states(), 1)

        list(self.mevm.ready_states)
        assert_all()

        list(self.mevm.terminated_states)
        assert_all()

        list(self.mevm.all_states)
        assert_all()

    def test_function_name_collision(self):
        source_code = """
        contract Test{

            function ret(uint) returns(uint){
                return 1;
            }

            function ret(uint,uint) returns(uint){
                return 2;
            }

        }
        """
        user_account = self.mevm.create_account(balance=1000000000)
        contract_account = self.mevm.solidity_create_contract(source_code, owner=user_account)
        with self.assertRaises(EthereumError):
            contract_account.ret(self.mevm.make_symbolic_value())

    def test_check_jumpdest_symbolic_pc(self):
        """
        In Manticore 0.2.4 (up to 6804661) when run with DetectIntegerOverflow,
        the EVM.pc is tainted and so it becomes a Constant and so a check in EVM._need_check_jumpdest:
            self.pc in self._valid_jumpdests
        failed (because we checked if the object is in a list of integers...).

        This test checks the fix for this issue.
        """
        self.mevm.register_detector(DetectIntegerOverflow())
        c = self.mevm.solidity_create_contract(
            """
        contract C {
            function mul(int256 a, int256 b) {
                int256 c = a * b;
                require(c / a == b);
            }
        }
        """,
            owner=self.mevm.create_account(balance=10000000),
        )

        c.mul(1, 2)

        self.assertEqual(self.mevm.count_ready_states(), 1)
        self.assertEqual(self.mevm.count_terminated_states(), 0)

    def test_gen_testcase_only_if(self):
        source_code = """
        contract Test {
            function f(uint x) returns(uint) {
                return x-2;
            }
        }
        """
        user_account = self.mevm.create_account(balance=10 ** 10)
        contract_account = self.mevm.solidity_create_contract(source_code, owner=user_account)
        input_sym = self.mevm.make_symbolic_value()
        contract_account.f(input_sym)
        self.assertEqual(self.mevm.count_ready_states(), 1)

        state = next(self.mevm.ready_states)
        retval_array = state.platform.human_transactions[-1].return_data
        retval = operators.CONCAT(256, *retval_array)

        # Test 1: Generate a testcase (since the condition/constrain can be met/solved)
        did_gen = self.mevm.generate_testcase(state, "return can be 0", only_if=retval == 0)
        self.assertTrue(did_gen)

        with state as tmp:
            tmp.constrain(retval == 0)
            inp = tmp.solve_one(input_sym)
            self.assertEqual(inp, 2)

        expected_files = {
            "user_00000000." + ext
            for ext in ("summary", "constraints", "pkl", "tx.json", "tx", "trace", "logs")
        }

        expected_files.add("state_00000001.pkl")

        actual_files = set((fn for fn in os.listdir(self.mevm.workspace) if not fn.startswith(".")))
        self.assertEqual(actual_files, expected_files)

        summary_path = os.path.join(self.mevm.workspace, "user_00000000.summary")
        with open(summary_path) as summary:
            self.assertIn("return can be 0", summary.read())

        # Test 2: Don't generate a testcase (since the condition/constrain can't be met/solved)
        did_gen = self.mevm.generate_testcase(
            state, "return can be 0 again?", only_if=operators.AND(retval != 0, retval == 0)
        )
        self.assertFalse(did_gen)

        # Just a sanity check: a generate testcase with not met condition shouldn't add any more files
        self.assertEqual(actual_files, expected_files)

        # Since the condition was not met there should be no testcase in the summary
        with open(summary_path) as summary:
            self.assertNotIn("return can be 0 again?", summary.read())

    def test_function_name_with_signature(self):
        source_code = """
        contract Test {
            function ret(uint) returns(uint) {
                return 1;
            }

            function ret(uint,uint) returns(uint) {
                return 2;
            }
        }
        """
        user_account = self.mevm.create_account(balance=10 ** 10)
        contract_account = self.mevm.solidity_create_contract(source_code, owner=user_account)
        contract_account.ret(
            self.mevm.make_symbolic_value(),
            self.mevm.make_symbolic_value(),
            signature="(uint256,uint256)",
        )
        for st in self.mevm.all_states:
            z = st.solve_one(st.platform.transactions[1].return_data)
            break
        self.assertEqual(ABI.deserialize("(uint256)", z)[0], 2)

    def test_migrate_integration(self):
        m = self.mevm

        contract_src = """
        contract Overflow {
          uint public sellerBalance=0;

          function add(uint value)public  returns (bool){
              sellerBalance += value;
          }
        }
        """

        owner_account = m.create_account(balance=10 ** 10)
        attacker_account = m.create_account(balance=10 ** 10)
        contract_account = m.solidity_create_contract(contract_src, owner=owner_account, balance=0)

        # Some global expression `sym_add1`
        sym_add1 = m.make_symbolic_value(name="sym_add1")
        # Let's constrain it on the global fake constraintset
        m.constrain(sym_add1 > 0)
        m.constrain(sym_add1 < 10)
        # Symb tx 1
        contract_account.add(sym_add1, caller=attacker_account)

        # A new!? global expression
        sym_add2 = m.make_symbolic_value(name="sym_add2")
        # constraints involve old expression.  Some states may get invalidated by this. Should this be accepted?
        m.constrain(sym_add1 > sym_add2)
        # Symb tx 2
        contract_account.add(sym_add2, caller=attacker_account)

        # random concrete tx
        contract_account.sellerBalance(caller=attacker_account)

        # another constraining on the global constraintset. Yet more running states could get unfeasible by this.
        m.constrain(sym_add1 > 8)

        for state_num, state in enumerate(m.all_states):
            if state.is_feasible():
                self.assertTrue(state.can_be_true(sym_add1 == 9))
                self.assertTrue(state.can_be_true(sym_add2 == 8))

    def test_account_names(self):
        m = self.mevm
        user_account = m.create_account(name="user_account")
        self.assertEqual(m.accounts["user_account"], user_account)
        self.assertEqual(len(m.accounts), 1)

        user_account1 = m.create_account(name="user_account1")
        self.assertEqual(m.accounts["user_account1"], user_account1)
        self.assertEqual(len(m.accounts), 2)
        user_accounts = []
        for i in range(10):
            user_accounts.append(m.create_account())
        self.assertEqual(len(m.accounts), 12)
        for i in range(10):
            self.assertEqual(m.accounts[f"normal{i}"], user_accounts[i])

    def test_regression_internal_tx(self):
        m = self.mevm
        owner_account = m.create_account(balance=10 ** 10)
        c = """
        contract C1 {
          function g() returns (uint) {
            return 1;
          }
        }

        contract C2 {
          address c;
          function C2(address x) {
            c = x;
          }
          function f() returns (uint) {
            return C1(c).g();
          }
        }
        """

        c1 = m.solidity_create_contract(c, owner=owner_account, contract_name="C1")
        self.assertEqual(m.count_states(), 1)
        c2 = m.solidity_create_contract(
            c, owner=owner_account, contract_name="C2", args=[c1.address]
        )
        self.assertEqual(m.count_states(), 1)
        c2.f()
        self.assertEqual(m.count_states(), 1)
        c2.f()
        self.assertEqual(m.count_states(), 1)

        for state in m.all_states:
            world = state.platform
            self.assertEqual(len(world.transactions), 6)
            self.assertEqual(len(world.all_transactions), 6)
            self.assertEqual(len(world.human_transactions), 4)
            self.assertListEqual(
                ["CREATE", "CREATE", "CALL", "CALL", "CALL", "CALL"],
                [x.sort for x in world.all_transactions],
            )
            for tx in world.all_transactions[-4:]:
                self.assertEqual(tx.result, "RETURN")
                self.assertEqual(
                    state.solve_one(tx.return_data),
                    b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01",
                )

    def test_emit_did_execute_end_instructions(self):
        """
        Tests whether the did_evm_execute_instruction event is fired for instructions that internally trigger
        an exception
        """

        class TestDetector(Detector):
            def did_evm_execute_instruction_callback(self, state, instruction, arguments, result):
                if instruction.is_endtx:
                    with self.locked_context("endtx_instructions", set) as d:
                        d.add(instruction.name)

        mevm = self.mevm
        p = TestDetector()
        mevm.register_detector(p)

        filename = os.path.join(THIS_DIR, "contracts/simple_int_overflow.sol")
        mevm.multi_tx_analysis(filename, tx_limit=2, tx_preconstrain=True)

        self.assertIn("endtx_instructions", p.context)
        self.assertSetEqual(
            p.context["endtx_instructions"], {"INVALID", "RETURN", "STOP", "REVERT"}
        )

    def test_call_with_concretized_args(self):
        """Test a CALL with symbolic arguments that will to be concretized.

        https://github.com/trailofbits/manticore/issues/1237
        """
        m = self.mevm

        contract_src = """
        contract C {
          function transferHalfTo(address receiver) public payable {
              receiver.transfer(address(this).balance/2);
          }
        }
        """

        owner = m.create_account(balance=20 ** 10)
        contract = m.solidity_create_contract(contract_src, owner=owner)
        receiver = m.create_account(balance=0)
        symbolic_address = m.make_symbolic_address()
        m.constrain(symbolic_address == receiver.address)
        self.assertTrue(m.count_ready_states() > 0)
        contract.transferHalfTo(symbolic_address, caller=owner, value=1000000, gas=9999999999)

        self.assertTrue(
            any(
                state.can_be_true(state.platform.get_balance(receiver.address) > 0)
                for state in m.ready_states
            )
        )

    def test_make_symbolic_address(self):
        for init_state in self.mevm.ready_states:
            symbolic_address1 = self.mevm.make_symbolic_address()
            self.assertEqual(symbolic_address1.name, "TXADDR")

            # TEST 1: the 1st symbolic address should be constrained only to 0 (as there are no other accounts yet!)
            possible_addresses1 = init_state.solve_n(symbolic_address1, 10)
            self.assertEqual(possible_addresses1, [0])

        owner = self.mevm.create_account(balance=1)

        for state in self.mevm.ready_states:
            # TEST 2: the 2nd symbolic address should be constrained to OR(owner_address, 0)
            symbolic_address2 = self.mevm.make_symbolic_address()
            self.assertEqual(symbolic_address2.name, "TXADDR_1")

            self.assertCountEqual(state.solve_n(symbolic_address2, 10), [0, int(owner)])

        contract = self.mevm.solidity_create_contract("contract C {}", owner=owner)
        # TEST 3: the 3rd symbolic address should be constrained to OR(contract_address, 0, owner_address)
        symbolic_address3 = self.mevm.make_symbolic_address()
        self.assertEqual(symbolic_address3.name, "TXADDR_2")

        for state in self.mevm.ready_states:

            self.assertCountEqual(
                state.solve_n(symbolic_address3, 10), [int(contract), 0, int(owner)]
            )

            # NOTE: The 1st and 2nd symbolic addresses are still constrained to 0 and OR(owner_address, 0)
            # as the constrains are not reevaluated. They are created/assigned only once: when we create symbolic address.
            self.assertCountEqual(state.solve_n(symbolic_address1, 10), [0])
            self.assertCountEqual(state.solve_n(symbolic_address2, 10), [int(owner), 0])

    def test_end_instruction_trace(self):
        """
        Make sure that the trace files are correct, and include the end instructions.
        Also, make sure we produce a valid function call in trace.
        """

        class TestPlugin(Plugin):
            """
            Record the pcs of all end instructions encountered. Source of truth.
            """

            def did_evm_execute_instruction_callback(self, state, instruction, arguments, result):
                world = state.platform
                if world.current_transaction.sort == "CREATE":
                    name = "init"
                else:
                    name = "rt"

                # collect all end instructions based on whether they are in init or rt
                if instruction.is_endtx:
                    with self.locked_context(name) as d:
                        d.append(instruction.pc)

        mevm = self.mevm
        p = TestPlugin()
        mevm.register_plugin(p)

        filename = os.path.join(THIS_DIR, "contracts/int_overflow.sol")

        mevm.multi_tx_analysis(filename, tx_limit=1)
        mevm.finalize()

        worksp = mevm.workspace
        listdir = os.listdir(worksp)

        def get_concatenated_files(directory, suffix, init):
            paths = [Path(directory, f) for f in listdir if f.endswith(suffix)]
            concatenated = "".join(path.read_text() for path in paths)
            result = set()
            for x in concatenated.split("\n"):
                if ":" in x:
                    address = int(x.split(":")[0], 16)
                    pc = int(x.split(":")[1].split(" ")[0], 16)
                    at_init = "*" in x
                    if at_init == init:
                        result.add(pc)
            return result

        all_init_traces = get_concatenated_files(worksp, "trace", init=True)
        all_rt_traces = get_concatenated_files(worksp, "trace", init=False)

        # make sure all init end insns appear somewhere in the init traces
        for pc in p.context["init"]:
            self.assertIn(pc, all_init_traces)

        # and all rt end insns appear somewhere in the rt traces
        for pc in p.context["rt"]:
            self.assertIn(pc, all_rt_traces)

        # Make sure the function call is correctly produced

        # Extract all valid function names, and make sure we have at least one
        existing_functions = []
        with open(filename, "r") as src:
            for line in src:
                m = re.match(r"\s*function (\w+).*", line)
                if m:
                    existing_functions.append(m.group(1))

        self.assertGreater(len(existing_functions), 0)

        tx = next(f for f in listdir if f.endswith("0.tx"))
        with open(os.path.join(worksp, tx), "r") as tx_f:
            lines = tx_f.readlines()

            # implicitly assert the following doesn't throw
            header_idx = lines.index("Function call:\n")
            func_call_summary = lines[header_idx + 1]

            for f in existing_functions:
                if func_call_summary.startswith(f) or func_call_summary.startswith("Constructor"):
                    break
            else:
                self.fail("Could not find a function call summary in workspace output")

    def test_event_forwarding_after_state_fork_during_message_call(self):
        # https://github.com/trailofbits/manticore/issues/1255
        source_code = """
        pragma solidity ^0.4.24;

        contract Lib {
           function isSeven(uint a) public pure returns (bool) {
               if (a == 7) {
                   return true;
               } else {
                   return false;
               }
           }
        }

        contract Wallet {
           Lib private lib;

           constructor() public payable {
               lib = new Lib();
           }

           function luckyNumber(uint a) public {
               if (lib.isSeven(a)) {
                   msg.sender.transfer(address(this).balance);
               }
           }
        }
        """

        m = self.mevm
        m.register_detector(DetectExternalCallAndLeak())

        owner = m.create_account(name="owner", balance=30000000000000000)
        wallet = m.solidity_create_contract(
            source_code,
            name="wallet",
            contract_name="Wallet",
            owner=owner,
            balance=10000000000000000,
        )
        attacker = m.create_account(name="attacker", balance=30000000000000000)
        wallet.luckyNumber(m.make_symbolic_value(), caller=attacker, gas=2312312312222)
        m.finalize()

        self.assertListEqual([x[2] for x in m.global_findings], ["Reachable ether leak to sender"])

    def test_graceful_handle_no_alive_states(self):
        """
        If there are no alive states, or no initial states, we should not crash. issue #795
        """
        # initiate the blockchain
        m = self.mevm
        source_code = """
        contract Simple {
            function f(uint a) payable public {
                if (a == 65) {
                    revert();
                }
            }
        }
        """

        # Initiate the accounts
        user_account = m.create_account(balance=10 ** 10)
        contract_account = m.solidity_create_contract(source_code, owner=user_account, balance=0)

        contract_account.f(1)  # it works
        contract_account.f(65)  # it works
        with self.assertRaises(NoAliveStates):
            contract_account.f(1)  # no alive states, but try to run a tx anyway

    @unittest.skip("reason")
    def test_reachability(self):
        class StopAtFirstJump414141(Detector):
            def will_decode_instruction_callback(self, state, pc):
                TRUE = bytearray(
                    (
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        1,
                    )
                )
                FALSE = bytearray(
                    (
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                    )
                )
                # print pc, state.platform.current_vm.instruction
                # Once this address is reached the challenge is won
                if pc == 0x4141414141414141414141414141414141414141:
                    func_id = to_constant(state.platform.current_transaction.data[:4])
                    if func_id == ABI.function_selector("print(string)"):
                        func_name, args = ABI.deserialize(
                            "print(string)", state.platform.current_transaction.data
                        )
                        raise Return()
                    elif func_id == ABI.function_selector("terminate(string)"):
                        func_name, args = ABI.deserialize(
                            "terminate(string)", state.platform.current_transaction.data
                        )
                        self.manticore.shutdown()
                        raise Return(TRUE)
                    elif func_id == ABI.function_selector("assume(bool)"):
                        func_name, args = ABI.deserialize(
                            "assume(bool)", state.platform.current_transaction.data
                        )
                        state.add(args[0])
                        raise Return(TRUE)
                    elif func_id == ABI.function_selector("is_symbolic(bytes)"):
                        func_name, args = ABI.deserialize(
                            "is_symbolic(bytes)", state.platform.current_transaction.data
                        )
                        try:
                            arg = to_constant(args[0])
                        except Exception:
                            raise Return(TRUE)
                        raise Return(FALSE)
                    elif func_id == ABI.function_selector("is_symbolic(uint256)"):
                        func_name, args = ABI.deserialize(
                            "is_symbolic(uint256)", state.platform.current_transaction.data
                        )
                        try:
                            arg = to_constant(args[0])
                        except Exception as e:
                            raise Return(TRUE)
                        raise Return(FALSE)
                    elif func_id == ABI.function_selector("shutdown(string)"):
                        func_name, args = ABI.deserialize(
                            "shutdown(string)", state.platform.current_transaction.data
                        )
                        print("Shutdown", to_constant(args[0]))
                        self.manticore.shutdown()
                    elif func_id == ABI.function_selector("can_be_true(bool)"):
                        func_name, args = ABI.deserialize(
                            "can_be_true(bool)", state.platform.current_transaction.data
                        )
                        result = solver.can_be_true(state.constraints, args[0] != 0)
                        if result:
                            raise Return(TRUE)
                        raise Return(FALSE)

                    raise Stop()

                # otherwise keep exploring

        mevm = self.mevm
        p = StopAtFirstJump414141()
        mevm.register_detector(p)

        filename = os.path.join(THIS_DIR, "contracts/reached.sol")
        mevm.multi_tx_analysis(filename, tx_limit=2, contract_name="Reachable")

        context = p.context.get("flags", {})
        self.assertTrue(context.get("found", False))

    def test_preconstraints(self):
        source_code = """
        contract C {
            constructor() public {}
            function f0() public {}
            function f1(uint a) public payable {}
        }
        """
        m: ManticoreEVM = self.mevm

        creator_account = m.create_account(balance=10 ** 10)
        contract_account = m.solidity_create_contract(source_code, owner=creator_account, balance=0)

        data = m.make_symbolic_buffer(320)
        value = m.make_symbolic_value()
        m.constrain(
            m.preconstraint_for_call_transaction(address=contract_account, data=data, value=value)
        )
        m.transaction(caller=creator_account, address=contract_account, data=data, value=value)

        results = [state.platform.all_transactions[-1].result for state in m.all_states]
        self.assertListEqual(sorted(results), ["STOP", "STOP"])

    def test_plugins_enable(self):
        # test enable/disable plugin and sync vs contextmanager
        source_code = """
        contract C {
            constructor() public payable {}
            function f1(uint a) public payable {}
        }
        """

        class examplePlugin(Plugin):
            def will_evm_execute_instruction_callback(self, state, i, *args, **kwargs):
                with self.locked_context() as ctx:
                    if "xcount" in ctx:
                        ctx["xcount"] = ctx["xcount"] + 1
                    else:
                        ctx["xcount"] = 1

        aplug = examplePlugin()

        m: ManticoreEVM = ManticoreEVM()
        m.register_plugin(aplug)

        creator_account = m.create_account(balance=10000000000)
        contract_account = m.solidity_create_contract(source_code, owner=creator_account, balance=0)
        self.assertEqual(aplug.context.get("xcount", 0), 10)  # 22 if revert?

        data = m.make_symbolic_buffer(320)
        value = m.make_symbolic_value()
        m.transaction(caller=creator_account, address=contract_account, data=data, value=value)
        with aplug.locked_context() as ctx:
            self.assertEqual(ctx.get("xcount", 0), 63)
        aplug.disable()
        m.transaction(caller=creator_account, address=contract_account, data=data, value=value)
        self.assertEqual(aplug.context.get("xcount", 0), 63)
        aplug.enable()
        m.transaction(caller=creator_account, address=contract_account, data=data, value=value)
        self.assertEqual(aplug.context.get("xcount", 0), 112)


class EthHelpersTest(unittest.TestCase):
    def setUp(self):
        self.bv = BitVec(256)

    def test_concretizer(self):
        policy = "SOME_NONSTANDARD_POLICY"

        @concretized_args(a=policy)
        def inner_func(self, a, b):
            return a, b

        class X:
            class Y:
                class Z:
                    instruction = "instruction"

                current_vm = Z()

            world = Y()

        with self.assertRaises(ConcretizeArgument) as cm:
            inner_func(X(), self.bv, 34)

        self.assertEqual(cm.exception.pos, 1)
        self.assertEqual(cm.exception.policy, policy)

    def test_concretizer_default(self):
        @concretized_args(b="")
        def inner_func(self, a, b):
            return a, b

        class X:
            class Y:
                class Z:
                    instruction = "instruction"

                current_vm = Z()

            world = Y()

        with self.assertRaises(ConcretizeArgument) as cm:
            inner_func(X(), 34, self.bv)

        self.assertEqual(cm.exception.pos, 2)
        # Make sure the policy isn't blank, i.e. we didn't pass through
        # a falsifiable value, and we selected a default
        self.assertTrue(cm.exception.policy)
        self.assertNotEqual(cm.exception.policy, "")

    def test_concretizer_doesnt_overreach(self):
        @concretized_args(b="")
        def inner_func(self, a, b):
            return a, b

        # Make sure we don't raise when a param is symbolic and its concretization
        # wasn't requested.
        inner_func(None, self.bv, 123)

    def test_account_exists(self):
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints)
        default = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
        empty = world.create_account(nonce=0, balance=0, code=b"")
        has_code = world.create_account(nonce=0, balance=0, code=b"ff")
        has_nonce = world.create_account(nonce=1, balance=0, code=b"")
        has_balance = world.create_account(nonce=0, balance=1, code=b"")
        self.assertTrue(world.account_exists(has_code))
        self.assertTrue(world.account_exists(has_nonce))
        self.assertTrue(world.account_exists(has_balance))
        self.assertFalse(world.account_exists(empty))
        self.assertFalse(world.account_exists(default))


class EthSolidityMetadataTests(unittest.TestCase):
    def test_tuple_signature_for_components(self):
        self.assertEqual(SolidityMetadata.tuple_signature_for_components([]), "()")
        self.assertEqual(
            SolidityMetadata.tuple_signature_for_components(
                [{"type": "uint256"}, {"type": "uint256[]"}]
            ),
            "(uint256,uint256[])",
        )
        self.assertEqual(
            SolidityMetadata.tuple_signature_for_components(
                [
                    {
                        "type": "tuple[2]",
                        "components": [{"type": "uint256"}, {"type": "uint256[]"}],
                    },
                    {
                        "type": "tuple",
                        "components": [
                            {"type": "tuple", "components": [{"type": "string"}]},
                            {"type": "string"},
                            {
                                "type": "tuple[]",
                                "components": [{"type": "uint256"}, {"type": "uint256[2]"}],
                            },
                        ],
                    },
                ]
            ),
            "((uint256,uint256[])[2],((string),string,(uint256,uint256[2])[]))",
        )

    def test_abi_constructor_and_fallback_items(self):
        with disposable_mevm() as m:
            source_code = """
            contract C {
                constructor(uint a) public {}
                function() public payable {}
            }
            """
            user_account = m.create_account(balance=100000000000, name="user_account")
            contract_account = m.solidity_create_contract(
                source_code, owner=user_account, name="contract_account", args=(0,)
            )
            md: SolidityMetadata = m.get_metadata(contract_account)

            self.assertTrue(md.has_non_default_constructor)
            self.assertDictEqual(
                md.constructor_abi,
                {
                    "inputs": [{"name": "a", "type": "uint256"}],
                    "payable": False,
                    "stateMutability": "nonpayable",
                    "type": "constructor",
                },
            )
            self.assertEqual(md.get_constructor_arguments(), "(uint256)")

            self.assertTrue(md.has_non_default_fallback_function)
            self.assertTrue(md.fallback_function_selector, b"\0\0\0\0")
            fallback = md.get_abi(b"")
            self.assertDictEqual(fallback, md.get_abi(md.fallback_function_selector))
            self.assertDictEqual(
                fallback, {"payable": True, "stateMutability": "payable", "type": "fallback"}
            )

            self.assertEqual(md.get_func_signature(md.fallback_function_selector), None)
            self.assertEqual(md.get_func_signature(b""), None)

            self.assertEqual(md.get_func_name(md.fallback_function_selector), "{fallback}")
            self.assertEqual(md.get_func_name(b""), "{fallback}")

            self.assertEqual(md.get_func_argument_types(md.fallback_function_selector), "()")
            self.assertEqual(md.get_func_argument_types(b""), "()")

            self.assertEqual(md.get_func_return_types(md.fallback_function_selector), "()")
            self.assertEqual(md.get_func_return_types(b""), "()")

            self.assertDictEqual(md.signatures, {})
            self.assertSequenceEqual(md.function_selectors, [md.fallback_function_selector])
            self.assertSequenceEqual(md.function_signatures, [])

            with self.assertWarns(ManticoreDeprecationWarning):
                self.assertSequenceEqual(md.hashes, [md.fallback_function_selector])

            with self.assertWarns(ManticoreDeprecationWarning):
                self.assertSequenceEqual(md.functions, ["{fallback}()"])

    def test_overloaded_functions_and_events(self):
        with disposable_mevm() as m:
            source_code = """
            contract C {
                function f() public payable returns (uint) {}
                function f(string a) public {}

                event E(uint);
                event E(uint, string);
            }
            """
            user_account = m.create_account(balance=100000000, name="user_account")
            contract_account = m.solidity_create_contract(
                source_code, owner=user_account, name="contract_account"
            )
            md: SolidityMetadata = m.get_metadata(contract_account)

            f0_sel = ABI.function_selector("f()")
            f1_sel = ABI.function_selector("f(string)")

            with self.assertWarns(ManticoreDeprecationWarning):
                self.assertEqual(md.get_hash("f()"), f0_sel)

            self.assertListEqual(sorted(md.function_selectors), sorted([f0_sel, f1_sel]))
            with self.assertWarns(ManticoreDeprecationWarning):
                self.assertListEqual(
                    sorted(md.hashes), sorted([f0_sel, f1_sel, md.fallback_function_selector])
                )

            e1_sel = ABI.function_selector("E(uint256)")

            f0_abi = md.get_abi(f0_sel)
            f1_abi = md.get_abi(f1_sel)
            self.assertEqual(f0_abi["stateMutability"], "payable")
            self.assertEqual(f1_abi["stateMutability"], "nonpayable")
            self.assertFalse(md.has_non_default_fallback_function)
            fallback_abi = md.get_abi(md.fallback_function_selector)
            self.assertDictEqual(
                fallback_abi,
                {"payable": False, "stateMutability": "nonpayable", "type": "fallback"},
            )
            # get_abi is only for functions, not events.
            self.assertEqual(md.get_abi(e1_sel), fallback_abi)

            self.assertEqual(md.get_func_signature(f0_sel), "f()")
            self.assertEqual(md.get_func_signature(f1_sel), "f(string)")
            self.assertEqual(md.get_func_signature(md.fallback_function_selector), None)
            self.assertEqual(md.get_func_signature(e1_sel), None)

            self.assertDictEqual(md.signatures, {f0_sel: "f()", f1_sel: "f(string)"})

            self.assertListEqual(sorted(md.function_signatures), ["f()", "f(string)"])
            with self.assertWarns(ManticoreDeprecationWarning):
                self.assertListEqual(sorted(md.functions), ["f()", "f(string)", "{fallback}()"])

            self.assertEqual(md.get_func_name(f0_sel), "f")
            self.assertEqual(md.get_func_name(f1_sel), "f")
            self.assertEqual(md.get_func_name(md.fallback_function_selector), "{fallback}")
            self.assertEqual(md.get_func_name(e1_sel), "{fallback}")

            self.assertEqual(md.get_func_argument_types(f0_sel), "()")
            self.assertEqual(md.get_func_argument_types(f1_sel), "(string)")
            self.assertEqual(md.get_func_argument_types(md.fallback_function_selector), "()")
            self.assertEqual(md.get_func_argument_types(e1_sel), "()")

            self.assertEqual(md.get_func_return_types(f0_sel), "(uint256)")
            self.assertEqual(md.get_func_return_types(f1_sel), "()")
            self.assertEqual(md.get_func_return_types(md.fallback_function_selector), "()")
            self.assertEqual(md.get_func_return_types(e1_sel), "()")

            self.assertFalse(md.has_non_default_constructor)
            self.assertDictEqual(
                md.constructor_abi,
                {
                    "inputs": [],
                    "payable": False,
                    "stateMutability": "nonpayable",
                    "type": "constructor",
                },
            )


class EthSpecificTxIntructionTests(unittest.TestCase):
    def test_jmpdest_check(self):
        """
            This test that jumping to a JUMPDEST in the operand of a PUSH should
            be treated as an INVALID instruction.
            https://github.com/trailofbits/manticore/issues/1169
        """

        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints)

        world.create_account(
            address=0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6,
            balance=100000000000000000000000,
            code=EVMAsm.assemble("PUSH1 0x5b\nPUSH1 0x1\nJUMP"),
        )
        address = 0xF572E5295C57F15886F9B263E2F6D2D6C7B5EC6
        price = 0x5AF3107A4000
        data = ""
        caller = 0xCD1722F3947DEF4CF144679DA39C4C32BDC35681
        value = 1000000000000000000
        bytecode = world.get_code(address)
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = ""
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ("RETURN", "REVERT"):
                returndata = e.data

        self.assertEqual(result, "THROW")

    def test_delegatecall_env(self):
        """
            This test that the delegatecalled environment is identicall to the caller
            https://github.com/trailofbits/manticore/issues/1169
        """
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints)
        asm_acc1 = """  CALLER
                        PUSH1 0x0
                        SSTORE
                        ADDRESS
                        PUSH1 0x1
                        SSTORE
                        CALLVALUE
                        PUSH1 0x2
                        SSTORE
                        STOP
                  """
        # delegatecall(gas, address, in_offset, in_size, out_offset, out_size)
        asm_acc2 = """  PUSH1 0x0
                        PUSH2 0X0
                        PUSH1 0x0
                        PUSH2 0X0
                        PUSH32 0x111111111111111111111111111111111111111
                        PUSH32 0x100000
                        DELEGATECALL
                        STOP
            """

        world.create_account(
            address=0x111111111111111111111111111111111111111, code=EVMAsm.assemble(asm_acc1)
        )

        world.create_account(
            address=0x222222222222222222222222222222222222222, code=EVMAsm.assemble(asm_acc2)
        )

        world.create_account(
            address=0x333333333333333333333333333333333333333,
            balance=100000000000000000000000,
            code=EVMAsm.assemble(asm_acc2),
        )

        world.transaction(
            0x222222222222222222222222222222222222222,
            caller=0x333333333333333333333333333333333333333,
            value=10,
            gas=50000000,
        )

        try:
            while True:
                world.execute()
        except TerminateState as e:
            result = str(e)

        self.assertEqual(result, "STOP")

        # Check there is something written to the storage of the contract making
        # the delegatecall
        self.assertTrue(world.has_storage(0x222222222222222222222222222222222222222))

        # Caller at delegatecalled contract must be original caller
        self.assertEqual(
            world.get_storage_data(0x222222222222222222222222222222222222222, 0),
            0x333333333333333333333333333333333333333,
        )
        # address at delegatecalled contract must be original address
        self.assertEqual(
            world.get_storage_data(0x222222222222222222222222222222222222222, 1),
            0x222222222222222222222222222222222222222,
        )
        # value at delegatecalled contract must be original value
        self.assertEqual(world.get_storage_data(0x222222222222222222222222222222222222222, 2), 10)

        # check balances
        self.assertEqual(world.get_balance(0x111111111111111111111111111111111111111), 0)
        self.assertEqual(world.get_balance(0x222222222222222222222222222222222222222), 10)
        self.assertEqual(
            world.get_balance(0x333333333333333333333333333333333333333),
            100000000000000000000000 - 10,
        )

        # check delegated call storage was not touch
        self.assertFalse(world.has_storage(0x111111111111111111111111111111111111111))
        self.assertEqual(world.get_storage_data(0x111111111111111111111111111111111111111, 0), 0)
        self.assertEqual(world.get_storage_data(0x111111111111111111111111111111111111111, 1), 0)
        self.assertEqual(world.get_storage_data(0x111111111111111111111111111111111111111, 2), 0)
        self.assertFalse(world.has_storage(0x333333333333333333333333333333333333333))

    def test_gas_check(self):
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints)
        asm_acc = """  PUSH1 0x0
                       SELFDESTRUCT
                  """
        world.create_account(
            address=0x111111111111111111111111111111111111111, code=EVMAsm.assemble(asm_acc)
        )
        world.create_account(
            address=0x222222222222222222222222222222222222222, balance=10000000000000
        )
        world.transaction(
            0x111111111111111111111111111111111111111,
            caller=0x222222222222222222222222222222222222222,
            gas=50030,
        )
        try:
            while True:
                world.execute()
        except TerminateState as e:
            result = str(e)
        self.assertEqual(result, "SELFDESTRUCT")

    def test_selfdestruct(self):
        with disposable_mevm() as m:
            asm_acc = """  PUSH1 0x0
                           SELFDESTRUCT
                      """
            m.create_account(
                address=0x111111111111111111111111111111111111111, code=EVMAsm.assemble(asm_acc)
            )
            m.create_account(
                address=0x222222222222222222222222222222222222222, balance=1000000000000000000
            )  # Needs eth to pay for the gas.
            symbolic_data = m.make_symbolic_buffer(320)
            m.transaction(
                caller=0x222222222222222222222222222222222222222,
                address=0x111111111111111111111111111111111111111,
                data=symbolic_data,
                value=0,
            )
            self.assertEqual(m.count_ready_states(), 1)

    def test_call_gas(self):
        GCALLSTATIC = 21721  # 21000 + (3 * 7 push ops) + 700 static cost for call
        GCALLVALUE = 9000  # cost added for nonzero callvalue
        GCALLNEW = 25000  # cost added for forcing new acct creation
        GCALLSTIPEND = 2300  # additional gas sent with a call if value > 0

        with disposable_mevm() as m:
            # empty call target
            m.create_account(address=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF)
            # nonempty call target
            m.create_account(
                address=0x111111111111111111111111111111111111111, nonce=1  # nonempty account
            )

            # call(gas, target, value, in_offset, in_size, out_offset, out_size)
            # call to empty acct with value = 0
            asm_call_empty_no_val = """ PUSH1 0x0
                                            PUSH1 0X0
                                            PUSH1 0x0
                                            PUSH1 0X0
                                            PUSH1 0x0
                                            PUSH20 0xfffffffffffffffffffffffffffffffffffffff
                                            PUSH1 0x0
                                            CALL
                                            STOP
                                        """
            # call to existing acct with value > 0
            asm_call_nonempty_w_val = """ PUSH1 0x0
                                            PUSH1 0X0
                                            PUSH1 0x0
                                            PUSH1 0X0
                                            PUSH1 0x1
                                            PUSH20 0x111111111111111111111111111111111111111
                                            PUSH1 0x0
                                            CALL
                                            STOP
                                        """
            # call to empty acct with value > 0, forcing addition to state trie
            asm_call_empty_w_val = """ PUSH1 0x0
                                            PUSH1 0X0
                                            PUSH1 0x0
                                            PUSH1 0X0
                                            PUSH1 0x1
                                            PUSH20 0xfffffffffffffffffffffffffffffffffffffff
                                            PUSH1 0x0
                                            CALL
                                            STOP
                                        """

            call_empty_no_val = m.create_account(code=EVMAsm.assemble(asm_call_empty_no_val))
            call_nonempty_w_val = m.create_account(
                balance=100, code=EVMAsm.assemble(asm_call_nonempty_w_val)
            )
            call_empty_w_val = m.create_account(
                balance=100, code=EVMAsm.assemble(asm_call_empty_w_val)
            )

            caller = m.create_account(
                address=0x222222222222222222222222222222222222222, balance=1000000000000000000
            )

            # call to empty acct with value = 0
            m.transaction(caller=caller, address=call_empty_no_val, data=b"", value=0, gas=50000000)
            self.assertEqual(m.count_ready_states(), 1)
            state = next(m.ready_states)
            txs = state.platform.transactions
            # no value, so no call stipend should be sent
            self.assertEqual(txs[-2].gas, 0)
            # no value, so only static call cost should be charged
            self.assertEqual(txs[-1].used_gas, GCALLSTATIC)

            # call to existing acct with value > 0
            m.transaction(
                caller=caller, address=call_nonempty_w_val, data=b"", value=0, gas=50000000
            )
            self.assertEqual(m.count_ready_states(), 1)
            state = next(m.ready_states)
            txs = state.platform.transactions
            # call stipend should be sent with call
            self.assertEqual(txs[-2].gas, GCALLSTIPEND)
            # cost of call should include value cost, but not new acct cost
            self.assertEqual(txs[-1].used_gas, GCALLSTATIC + GCALLVALUE - GCALLSTIPEND)

            # call to empty acct with value > 0, forcing addition to state trie
            m.transaction(caller=caller, address=call_empty_w_val, data=b"", value=0, gas=50000000)
            self.assertEqual(m.count_ready_states(), 1)
            state = next(m.ready_states)
            txs = state.platform.transactions
            # call stipend should be sent with call
            self.assertEqual(txs[-2].gas, GCALLSTIPEND)
            # cost of call should include value cost and new acct cost
            self.assertEqual(txs[-1].used_gas, GCALLSTATIC + GCALLVALUE + GCALLNEW - GCALLSTIPEND)

    def test_selfdestruct_gas(self):
        GSDSTATIC = 26003  # 21000 + 3 (push op) + 5000 static cost for selfdestruct
        GNEWACCOUNT = 25000
        RSELFDESTRUCT = 24000

        with disposable_mevm() as m:
            # empty call target
            empty = m.create_account(address=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF)
            # nonempty call target
            nonempty = m.create_account(address=0x1111111111111111111111111111111111111111, nonce=1)

            asm_sd_empty = """ PUSH20 0xffffffffffffffffffffffffffffffffffffffff
                                SELFDESTRUCT
                            """
            asm_sd_nonempty = """ PUSH20 0x1111111111111111111111111111111111111111
                                    SELFDESTRUCT
                                """

            caller = m.create_account(
                address=0x222222222222222222222222222222222222222, balance=1000000000000000000
            )

            # selfdestruct to empty acct with no value
            sd_empty = m.create_account(code=EVMAsm.assemble(asm_sd_empty))
            m.transaction(caller=caller, address=sd_empty, data=b"", value=0, gas=50000000)
            self.assertEqual(m.count_ready_states(), 1)
            state = next(m.ready_states)
            txs = state.platform.transactions
            # no value, so only static cost charged and refund is gas_used / 2
            self.assertEqual(txs[-1].used_gas, round(GSDSTATIC - (GSDSTATIC / 2)))

            # selfdestruct to existing acct with value > 0
            sd_nonempty = m.create_account(code=EVMAsm.assemble(asm_sd_nonempty))
            m.transaction(caller=caller, address=sd_nonempty, data=b"", value=1, gas=50000000)
            self.assertEqual(m.count_ready_states(), 1)
            state = next(m.ready_states)
            txs = state.platform.transactions
            # recipient exists, so only static cost charged and refund is gas_used / 2
            self.assertEqual(txs[-1].used_gas, round(GSDSTATIC - (GSDSTATIC / 2)))

            # selfdestruct to empty acct with value > 0, forcing addition to state trie
            sd_empty = m.create_account(code=EVMAsm.assemble(asm_sd_empty))
            m.transaction(caller=caller, address=sd_empty, data=b"", value=1, gas=50000000)
            self.assertEqual(m.count_ready_states(), 1)
            state = next(m.ready_states)
            txs = state.platform.transactions
            # new account gas charged and full refund returned
            self.assertEqual(txs[-1].used_gas, GSDSTATIC + GNEWACCOUNT - RSELFDESTRUCT)


class EthPluginTests(unittest.TestCase):
    def test_FilterFunctions_fallback_function_matching(self):
        """
        Tests that the FilterFunctions plugin matches the fallback function hash correctly. issue #1196
        """
        with disposable_mevm() as m:
            source_code = """
            contract FallbackCounter {
                uint public fallbackCounter = 123;
                uint public otherCounter = 456;

                function other() {
                    otherCounter += 1;
                }
                function() public {
                    fallbackCounter += 1;
                }
            }
            """
            plugin = FilterFunctions(
                regexp=r"^$", fallback=True
            )  # Only matches the fallback function.
            m.register_plugin(plugin)

            creator_account = m.create_account(balance=10000000000000)
            contract_account = m.solidity_create_contract(
                source_code, owner=creator_account, gas=2134322
            )

            symbolic_data = m.make_symbolic_buffer(320)
            m.transaction(
                caller=creator_account, address=contract_account, data=symbolic_data, value=0
            )

            self.assertEqual(m.count_states(), 1)
            self.assertEqual(m.count_ready_states(), 1)

            self.assertEqual(len(m.world.all_transactions), 2)

            # The fallbackCounter value must have been increased by 1.
            self.assertEqual(m.count_ready_states(), 1)
            for st in m.ready_states:
                world = st.platform
                self.assertEqual(len(st.platform.all_transactions), 2)
                self.assertTrue(
                    st.must_be_true(world.get_storage_data(contract_account, 0) == 124)
                )  # 123 + 1
                self.assertTrue(st.must_be_true(world.get_storage_data(contract_account, 1) == 456))

    def test_checkpoint(self):
        # test enable/disable plugin and sync vs contextmanager
        source_code = """
        contract C {
            constructor() public payable {}
            function f1(uint a) public payable {}
            function f2(uint a) public payable {}
        }
        """

        m: ManticoreEVM = ManticoreEVM()

        creator_account = m.create_account(balance=10000000000)
        contract_account = m.solidity_create_contract(source_code, owner=creator_account, balance=0)

        # Can not go to unexistant snapshot
        self.assertRaises(ManticoreError, m.goto_snapshot)
        self.assertEqual(m.count_ready_states(), 1)
        # take the snap
        m.take_snapshot()
        self.assertEqual(m.count_ready_states(), 1)

        data = m.make_symbolic_buffer(320)
        value = m.make_symbolic_value()
        m.transaction(caller=creator_account, address=contract_account, data=data, value=value)
        self.assertEqual(m.count_ready_states(), 2)
        self.assertEqual(m.count_terminated_states(), 1)
        m.goto_snapshot()  # return to have only 1 ready state. (The terminated states remain)

        self.assertEqual(m.count_ready_states(), 1)
        self.assertEqual(m.count_terminated_states(), 1)

        data = m.make_symbolic_buffer(320)
        value = m.make_symbolic_value()
        m.transaction(caller=creator_account, address=contract_account, data=data, value=value)
        self.assertEqual(m.count_ready_states(), 2)
        self.assertEqual(m.count_terminated_states(), 2)

        m.clear_snapshot()
        # Can not go to unexistant snapshot
        self.assertRaises(Exception, m.goto_snapshot)
        self.assertEqual(m.count_terminated_states(), 2)
        m.clear_terminated_states()
        self.assertEqual(m.count_terminated_states(), 0)

        m.clear_snapshot()  # We can double clear it

    def test_is_main(self):
        # test enable/disable plugin and sync vs contextmanager
        source_code = """
        contract C {
            constructor() public payable {}
            function f1(uint a) public payable {}
            function f2(uint a) public payable {}
        }
        """

        class X(Plugin):
            def will_evm_execute_instruction_callback(self, state, instruction, args):
                is_main = self.manticore.is_main()
                is_running = self.manticore.is_running()
                with self.locked_context() as ctx:
                    ctx["is_main"] = ctx.get("is_main", False) or (is_main and not is_running)

        from manticore.utils import config

        consts = config.get_group("core")
        for ty in ("multiprocessing", "threading", "single"):
            consts.mprocessing = ty
            m: ManticoreEVM = ManticoreEVM()
            x = X()
            m.register_plugin(x)
            self.assertTrue(m.is_main())

            creator_account = m.create_account(balance=10000000000)
            contract_account = m.solidity_create_contract(
                source_code, owner=creator_account, balance=0
            )

            self.assertTrue(m.is_main() and not m.is_running())
            # From the plugin callback is never main
            self.assertFalse(x.context.get("is_main", False))


if __name__ == "__main__":
    unittest.main()
