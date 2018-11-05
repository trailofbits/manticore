import binascii
import shutil
import struct
import tempfile
from pathlib import Path
import unittest
import os
import sys
import resource
import re
from contextlib import contextmanager

from manticore.platforms import evm
from manticore.core.plugin import Plugin
from manticore.core.smtlib import ConstraintSet, operators
from manticore.core.smtlib.expression import BitVec
from manticore.core.smtlib import solver
from manticore.core.state import State, TerminateState
from manticore.ethereum import ManticoreEVM, DetectIntegerOverflow, Detector, NoAliveStates, ABI, EthereumError, FilterFunctions
from manticore.ethereum.solidity import SolidityMetadata
from manticore.platforms.evm import EVMWorld, ConcretizeStack, concretized_args, Return, Stop
from manticore.core.smtlib.visitors import pretty_print, translate_to_smtlib, simplify, to_constant
from manticore.utils.deprecated import ManticoreDeprecationWarning
import pyevmasm as EVMAsm


import shutil

THIS_DIR = os.path.dirname(os.path.abspath(__file__))

# FIXME(mark): Remove these two lines when logging works for ManticoreEVM
from manticore.utils.log import init_logging

init_logging()

def make_mock_evm_state():
    cs = ConstraintSet()
    fakestate = State(cs, EVMWorld(cs))
    return fakestate

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
        filename = os.path.join(THIS_DIR, 'binaries/int_overflow.sol')
        mevm.multi_tx_analysis(filename, tx_limit=1)
        self.assertEqual(len(mevm.global_findings), 3)
        all_findings = ''.join([x[2] for x in mevm.global_findings])
        self.assertIn('Unsigned integer overflow at SUB instruction', all_findings)
        self.assertIn('Unsigned integer overflow at ADD instruction', all_findings)
        self.assertIn('Unsigned integer overflow at MUL instruction', all_findings)


class EthAbiTests(unittest.TestCase):
    _multiprocess_can_split = True

    @staticmethod
    def _pack_int_to_32(x):
        return b'\x00' * 28 + struct.pack('>I', x)

    def test_str_for_string_bytesM_arg(self):
        self.assertEqual(ABI.serialize('(string,bytes32)', 'hi', 'qq'), bytearray(b'\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00@qq\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02hi\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'))
        self.assertEqual(ABI.serialize('string', 'hi'), bytearray(b'\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00 \x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02hi\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'))

    def test_parse_tx(self):
        m = ManticoreEVM()
        source_code = '''
        contract C{
            mapping(address => uint) balances;
            function test1(address to, uint val){
                balances[to] = val;
            }
        }
        '''
        user_account = m.create_account(balance=1000, name='user_account')
        contract_account = m.solidity_create_contract(source_code, owner=user_account, name='contract_account')


        calldata = binascii.unhexlify(b'9de4886f9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d9d')
        returndata = b'' 
        md = m.get_metadata(contract_account)
        self.assertEqual(md.parse_tx(calldata, returndata), 'test1(899826498278242188854817720535123270925417291165, 71291600040229971300002528024956868756719167029433602173313100742126907268509)')


    def test_dyn_address(self):
        d = [
            b'AAAA',                    # function hash
            self._pack_int_to_32(32),  # offset to data start
            self._pack_int_to_32(2),   # data start; # of elements
            self._pack_int_to_32(42),  # element 1
            self._pack_int_to_32(43),  # element 2
        ]
        d = b''.join(d)


        func_id, dynargs = ABI.deserialize(type_spec='func(address[])', data=d)


        self.assertEqual(func_id, b'AAAA')
        self.assertEqual(dynargs, ([42, 43],))

    def test_dyn_bytes(self):
        d = [
            b'AAAA',                    # function hash
            self._pack_int_to_32(32),  # offset to data start
            self._pack_int_to_32(30),   # data start; # of elements
            b'Z'*30, b'\x00'*2
        ]
        d = b''.join(d)

        funcname, dynargs = ABI.deserialize(type_spec='func(bytes)', data=d)

        self.assertEqual(funcname, b'AAAA')
        self.assertEqual(dynargs, (b'Z'*30,))

    def test_simple_types0(self):
        d = [
            b'AAAA',                    # function hash
            self._pack_int_to_32(32),
            b'\xff' * 32,
        ]
        d = b''.join(d)
        funcname, dynargs = ABI.deserialize(type_spec='func(uint256,uint256)', data=d)
        #self.assertEqual(funcname, 'AAAA')
        self.assertEqual(dynargs, (32, 2**256 - 1 ))

    def test_simple_types1(self):
        d = [
            b'AAAA',                    # function hash
            self._pack_int_to_32(32),
            b'\xff' * 32,
            b'\xff'.rjust(32, b'\0'),
            self._pack_int_to_32(0x424242),
        ]
        d = b''.join(d)
        funcname, dynargs = ABI.deserialize(type_spec='func(uint256,uint256,bool,address)', data=d)
        #self.assertEqual(funcname, 'AAAA')
        self.assertEqual(dynargs, (32, 2**256 - 1, 0xff, 0x424242 ))


    def test_simple_types_ints(self):
        d = [
            b'AAAA',                    # function hash
            b'\x7f' + b'\xff' *31, # int256 max
            b'\x80'.ljust(32, b'\0'), # int256 min
        ]
        d = b''.join(d)
        func_id, dynargs = ABI.deserialize(type_spec='func(int256,int256)', data=d)
        self.assertEqual(func_id, b"AAAA")
        self.assertEqual(dynargs, ( 2**255 - 1, -(2**255) ))

    def test_simple_types_ints_symbolic(self):
        cs = ConstraintSet()
        x = cs.new_bitvec(256, name="x")
        y = cs.new_bitvec(256, name="y")
        # Something is terribly wrong x,y = 10,20
        my_ser = ABI.serialize('(uint,uint)', x, y)
        x_, y_ = ABI.deserialize('(uint,uint)', my_ser)
        self.assertTrue(solver.must_be_true(cs, x == x_))
        self.assertTrue(solver.must_be_true(cs, y == y_))

    def test_simple_types_ints_symbolic1(self):
        cs = ConstraintSet()
        x = cs.new_bitvec(256, name="x")
        # Something is terribly wrong x,y = 10,20
        my_ser = ABI.serialize('uint', x)
        self.assertTrue(solver.must_be_true(cs, my_ser[0] == operators.EXTRACT(x, 256 - 8, 8)))

    def test_address0(self):
        data = f'{chr(0) * 11}\x01\x55{chr(0) * 19}'
        parsed = ABI.deserialize('address', data)
        self.assertEqual(parsed, 0x55 << (8 * 19))

    def test_mult_dyn_types(self):
        d = [
            b'AAAA',                    # function hash
            self._pack_int_to_32(0x40),  # offset to data 1 start
            self._pack_int_to_32(0x80),  # offset to data 2 start
            self._pack_int_to_32(10),  # data 1 size
            b'helloworld'.ljust(32, b'\x00'),  # data 1
            self._pack_int_to_32(3),  # data 2 size
            self._pack_int_to_32(3),  # data 2
            self._pack_int_to_32(4),
            self._pack_int_to_32(5),
        ]
        d = b''.join(d)

        func_id, dynargs = ABI.deserialize(type_spec='func(bytes,address[])', data=d)

        self.assertEqual(func_id, b'AAAA')
        self.assertEqual(dynargs, (b'helloworld', [3, 4, 5]))

    def test_self_make_and_parse_multi_dyn(self):
        d = ABI.function_call('func(bytes,address[])', b'h'*50, [1, 1, 2, 2, 3, 3] )
        funcid, dynargs = ABI.deserialize(type_spec='func(bytes,address[])', data=d)
        self.assertEqual(funcid, b'\x83}9\xe8')
        self.assertEqual(dynargs, (b'h'*50, [1, 1, 2, 2, 3, 3]))


    def test_serialize_tuple(self):
        self.assertEqual(ABI.serialize('(int256)', 0x10), b'\0' * 31 + b'\x10')
        self.assertEqual(ABI.serialize('(int256,int256)', 0x10, 0x20), b'\0' * 31 + b'\x10' + b'\0' * 31 + b'\x20')
        self.assertEqual(ABI.serialize('(int256,(int256,int256))', 0x10, (0x20, 0x30)),
                         b'\0' * 31 + b'\x10' + b'\0' * 31 + b'\x20' + b'\0' * 31 + b'\x30')

    def test_serialize_basic_types_int(self):
        self.assertEqual(ABI.serialize('int256', 0x10), b'\0' * 31 + b'\x10')
        self.assertEqual(ABI.deserialize('int256', b'\0' * 31 + b'\x10'), 0x10)

        self.assertEqual(ABI.serialize('int256', -0x10), b'\xff' * 31 + b'\xf0')
        self.assertEqual(ABI.deserialize('int256', b'\xff' * 31 + b'\xf0'), -0x10)

    def test_serialize_basic_types_int8(self):
        self.assertEqual(ABI.serialize('int8', 0x10), b'\0' * 31 + b'\x10')
        self.assertEqual(ABI.deserialize('int8', b'\0' * 31 + b'\x10'), 0x10)

        self.assertEqual(ABI.serialize('int8', -0x10), b'\x00' * 31 + b'\xf0')
        self.assertEqual(ABI.deserialize('int8', b'\x00' * 31 + b'\xf0'), -0x10)

    def test_serialize_basic_types_int16(self):
        self.assertEqual(ABI.serialize('int16', 0x100), b'\0' * 30 + b'\x01\x00')
        self.assertEqual(ABI.deserialize('int16', b'\0' * 30 + b'\x01\x00'), 0x100)

        self.assertEqual(ABI.serialize('int16', -0x10), b'\x00' * 30 + b'\xff\xf0')
        self.assertEqual(ABI.deserialize('int16', b'\x00' * 30 + b'\xff\xf0'), -0x10)

    def test_serialize_basic_types_uint(self):
        self.assertEqual(ABI.serialize('uint256', 0x10), b'\0' * 31 + b'\x10')
        self.assertEqual(ABI.deserialize('uint256', b'\0' * 31 + b'\x10'), 0x10)

        self.assertEqual(ABI.serialize('uint256', -0x10), b'\xff' * 31 + b'\xf0')
        self.assertEqual(ABI.deserialize('uint256', b'\xff' * 31 + b'\xf0'),
                         0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0)
        self.assertEqual(ABI.deserialize('uint256', b'\xff' * 31 + b'\xf0'),
                         0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0)
        self.assertNotEqual(ABI.deserialize('uint256', b'\xff' * 31 + b'\xf0'), -0x10)


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
        ret = ABI.deserialize("int8", "\x10"*32)
        self.assertEqual(ret, 0x10)

    def test_parse_valid_int1(self):
        ret = ABI.deserialize("int", "\x10".ljust(32, '\0'))
        self.assertEqual(ret, 1 << 252)

    def test_parse_valid_int2(self):
        ret = ABI.deserialize("int40", "\x40\x00\x00\x00\x00".rjust(32, '\0'))
        self.assertEqual(ret, 1 << 38)

    def test_valid_uint(self):
        data = b"\xFF"*32

        parsed = ABI.deserialize('uint', data)
        self.assertEqual(parsed, 2**256 - 1)

        for i in range(8, 257, 8):
            parsed = ABI.deserialize(f'uint{i}', data)
            self.assertEqual(parsed, 2**i - 1)

    def test_empty_types(self):
        name, args = ABI.deserialize('func()', '\0' * 32)
        self.assertEqual(name, b'\x00\x00\x00\x00')
        self.assertEqual(args, tuple())

    def test_function_type(self):
        # setup ABI for function with one function param
        spec = 'func(function)'
        func_id = ABI.function_selector(spec)
        # build bytes24 data for function value (address+selector)
        # calls member id lookup on 'Ethereum Foundation Tip Box' (see https://www.ethereum.org/donate)
        address = ABI._serialize_uint(0xfB6916095ca1df60bB79Ce92cE3Ea74c37c5d359, 20, padding=0)
        selector = ABI.function_selector('memberId(address)')
        function_ref_data = address + selector + b'\0'*8
        # build tx call data
        call_data = func_id + function_ref_data 
        parsed_func_id, args = ABI.deserialize(spec, call_data)
        self.assertEqual(parsed_func_id, func_id)
        self.assertEqual(((0xfB6916095ca1df60bB79Ce92cE3Ea74c37c5d359, selector),), args)

    def test_serialize_fixed_bytes32(self):
        ret = ABI.serialize('bytes32', b'hi')
        self.assertEqual(ret, b'hi'.ljust(32, b'\x00'))

    def test_serialize_fixed_bytes2(self):
        ret = ABI.serialize('bytes2', b'aa')
        self.assertEqual(ret, b'aa'.ljust(32, b'\x00'))

    def test_serialize_fixed_bytes_less_data(self):
        ret = ABI.serialize('bytes4', b'aa')
        self.assertEqual(ret, b'aa'.ljust(32, b'\x00'))

    def test_serialize_fixed_bytes_too_big(self):
        with self.assertRaises(EthereumError):
            ABI.serialize('bytes2', b'hii')

    # test serializing symbolic buffer with bytesM
    def test_serialize_bytesM_symbolic(self):
        cs = ConstraintSet()
        buf = cs.new_array(index_max=17)
        ret = ABI.serialize('bytes32', buf)
        self.assertEqual(solver.minmax(cs, ret[0]), (0, 255))
        self.assertEqual(solver.minmax(cs, ret[17]), (0, 0))

    # test serializing symbolic buffer with bytes
    def test_serialize_bytes_symbolic(self):
        cs = ConstraintSet()
        buf = cs.new_array(index_max=17)
        ret = ABI.serialize('bytes', buf)

        # does the offset field look right?
        self.assertTrue(solver.must_be_true(cs, ret[0:32] == bytearray(b'\x00'*31 + b'\x20')))

        # does the size field look right?
        self.assertTrue(solver.must_be_true(cs, ret[32:64] == bytearray(b'\x00'*31 + b'\x11')))

        # does the data field look right?
        self.assertTrue(solver.must_be_true(cs, ret[64:64+32] == buf + bytearray(b'\x00'*15)))


class EthInstructionTests(unittest.TestCase):

    def _make(self):
        #Make the constraint store
        constraints = ConstraintSet()
        #make the ethereum world state
        world = evm.EVMWorld(constraints)

        address=0x222222222222222222222222222222222222200
        caller=origin=0x111111111111111111111111111111111111100
        price=0
        value=10000
        bytecode=b'\x05'
        data = 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA'
        gas = 1000000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, gas=gas, world=world)
        return constraints, world, new_vm

    def test_SDIV(self):
        constraints, world, vm = self._make()
        result = vm.SDIV(115792089237316182568066630936765703517573245936339743861833633745570447228928, 200867255532373784442745261542645325315275374222849104412672)
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
        self.assertListEqual(list(map(evm.to_signed, solver.get_all_values(constraints, result))), [-0x20])

    def test_SDIVSx(self):
        x,y = 0x20000000000000000000000000000000000000000000000000, -0x40
        constraints, world, vm = self._make()
        xx = constraints.new_bitvec(256, name="x")
        yy = constraints.new_bitvec(256, name="y")
        constraints.add(xx == x)
        constraints.add(yy == y)

        result = vm.SDIV(xx, yy)
        self.assertListEqual(list(map(evm.to_signed, solver.get_all_values(constraints, result))), [vm.SDIV(x, y)])


class EthTests(unittest.TestCase):
    def setUp(self):
        self.mevm = ManticoreEVM()
        self.worksp = self.mevm.workspace

    def tearDown(self):
        self.mevm=None
        shutil.rmtree(self.worksp)

    def test_invalid_function_signature(self):
        source_code = '''
        contract Test{

            function ret(uint256) returns(uint256){
                return 1;
            }

        }
        '''
        user_account = self.mevm.create_account(balance=1000)
        contract_account = self.mevm.solidity_create_contract(source_code, owner=user_account)
        with self.assertRaises(EthereumError) as ctx:
            contract_account.ret(self.mevm.make_symbolic_value(), signature='(uint8)')
        self.assertTrue(str(ctx.exception))

    def test_selfdestruct_decoupled_account_delete(self):
        source_code = '''
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
        '''
        user_account = self.mevm.create_account(balance=1000)
        contract_account = self.mevm.solidity_create_contract(source_code, owner=user_account, contract_name='D', gas=9000000)
        contract_account.t(gas=9000000) #this does not return nothing as it may create several states

        # nothing reverted and we end up with a single state
        self.assertEqual(self.mevm.count_states(), 1)

        # Check that calling t() returned a 42
        # That is that calling a selfdestructed contract works as the account
        # is actually deleted at the end of the human tx
        self.assertEqual(ABI.deserialize('uint', to_constant(self.mevm.world.transactions[-1].return_data)), 42)

    def test_function_name_collision(self):
        source_code = '''
        contract Test{

            function ret(uint) returns(uint){
                return 1;
            }

            function ret(uint,uint) returns(uint){
                return 2;
            }

        }
        '''
        user_account = self.mevm.create_account(balance=1000)
        contract_account = self.mevm.solidity_create_contract(source_code, owner=user_account)
        with self.assertRaises(EthereumError):
            contract_account.ret(self.mevm.make_symbolic_value())

    def test_gen_testcase_only_if(self):
        source_code = '''
        contract Test{
            function f(uint x) returns(uint){
                return x-2;
            }
        }
        '''
        user_account = self.mevm.create_account(balance=1000)
        contract_account = self.mevm.solidity_create_contract(source_code, owner=user_account)
        input_sym = self.mevm.make_symbolic_value()
        contract_account.f(input_sym)
        self.assertEqual(len(list(self.mevm.running_states)), 1)

        state = next(self.mevm.running_states)
        retval_array = state.platform.human_transactions[-1].return_data
        retval = operators.CONCAT(256, *retval_array)

        did_gen = self.mevm.generate_testcase(state, 'fail', 'return can be 0', only_if=retval == 0)
        self.assertTrue(did_gen)

        with state as tmp:
            tmp.constrain(retval == 0)
            inp = tmp.solve_one(input_sym)
            self.assertEqual(inp, 2)

        did_gen = self.mevm.generate_testcase(state, 'fail', 'return can be 0', only_if=operators.AND(retval != 0, retval == 0))
        self.assertFalse(did_gen)


    def test_function_name_with_signature(self):
        source_code = '''
        contract Test{

            function ret(uint) returns(uint){
                return 1;
            }

            function ret(uint,uint) returns(uint){
                return 2;
            }

        }
        '''
        user_account = self.mevm.create_account(balance=1000)
        contract_account = self.mevm.solidity_create_contract(source_code, owner=user_account)
        contract_account.ret(self.mevm.make_symbolic_value(), self.mevm.make_symbolic_value(),
                             signature='(uint256,uint256)')
        z = list(self.mevm.all_states)[0].solve_one(self.mevm.transactions()[1].return_data)
        self.assertEqual(ABI.deserialize('(uint256)', z)[0], 2)

    def test_migrate_integration(self):
        m = self.mevm

        contract_src='''
        contract Overflow {
          uint public sellerBalance=0;

          function add(uint value)public  returns (bool){
              sellerBalance += value;
          }
        }
        '''

        owner_account=m.create_account(balance=1000)
        attacker_account=m.create_account(balance=1000)
        contract_account=m.solidity_create_contract(contract_src,
                                                    owner=owner_account,
                                                    balance=0)

        #Some global expression `sym_add1` 
        sym_add1 = m.make_symbolic_value(name='sym_add1')
        #Let's constrain it on the global fake constraintset
        m.constrain(sym_add1>0)
        m.constrain(sym_add1<10)
        #Symb tx 1
        contract_account.add(sym_add1, caller=attacker_account)

        # A new!? global expression 
        sym_add2 = m.make_symbolic_value(name='sym_add2')
        #constraints involve old expression.  Some states may get invalidated by this. Should this be accepted?
        m.constrain(sym_add1 > sym_add2)
        #Symb tx 2
        contract_account.add(sym_add2, caller=attacker_account)

        #random concrete tx
        contract_account.sellerBalance(caller=attacker_account)

        #another constraining on the global constraintset. Yet more running states could get unfeasible by this.
        m.constrain(sym_add1 > 8)



        for state_num, state in enumerate(m.all_states):
            if state.is_feasible():
                self.assertTrue(state.can_be_true(sym_add1 == 9))
                self.assertTrue(state.can_be_true(sym_add2 == 8))

    def test_account_names(self):
        m = self.mevm
        user_account = m.create_account(name='user_account')
        self.assertEqual(m.accounts['user_account'], user_account)
        self.assertEqual(len(m.accounts), 1)

        user_account1 = m.create_account(name='user_account1')
        self.assertEqual(m.accounts['user_account1'], user_account1)
        self.assertEqual(len(m.accounts), 2)
        user_accounts = []
        for i in range(10):
            user_accounts.append(m.create_account())
        self.assertEqual(len(m.accounts), 12)
        for i in range(10):
            self.assertEqual(m.accounts[f'normal{i}'], user_accounts[i])

    def test_regression_internal_tx(self):
        m = self.mevm
        owner_account = m.create_account(balance=1000)
        c = '''
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
        '''

        c1 = m.solidity_create_contract(c, owner=owner_account, contract_name='C1')
        self.assertEqual(m.count_states(), 1)
        c2 = m.solidity_create_contract(c, owner=owner_account, contract_name='C2', args=[c1.address])
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
            self.assertListEqual(['CREATE', 'CREATE', 'CALL', 'CALL', 'CALL', 'CALL'], [x.sort for x in world.all_transactions])
            for tx in world.all_transactions[-4:]:
                self.assertEqual(tx.result, 'RETURN')
                self.assertEqual(state.solve_one(tx.return_data), b'\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01')

    def test_emit_did_execute_end_instructions(self):
        """
        Tests whether the did_evm_execute_instruction event is fired for instructions that internally trigger
        an exception
        """
        class TestDetector(Detector):
            def did_evm_execute_instruction_callback(self, state, instruction, arguments, result):
                if instruction.is_endtx:
                    with self.locked_context('endtx_instructions', set) as d:
                        d.add(instruction.name)

        mevm = self.mevm
        p = TestDetector()
        mevm.register_detector(p)

        filename = os.path.join(THIS_DIR, 'binaries/simple_int_overflow.sol')
        mevm.multi_tx_analysis(filename, tx_limit=2)

        self.assertIn('endtx_instructions', p.context)
        self.assertSetEqual(p.context['endtx_instructions'], {'INVALID', 'RETURN', 'STOP'})

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
                try:
                    world = state.platform
                    if world.current_transaction.sort == 'CREATE':
                        name = 'init'
                    else:
                        name = 'rt'

                    # collect all end instructions based on whether they are in init or rt
                    if instruction.is_endtx:
                        with self.locked_context(name) as d:
                            d.append(instruction.pc)
                except Exception as e:
                    raise

        mevm = self.mevm
        p = TestPlugin()
        mevm.register_plugin(p)


        filename = os.path.join(THIS_DIR, 'binaries/int_overflow.sol')

        mevm.multi_tx_analysis(filename, tx_limit=1)
        mevm.finalize()

        worksp = mevm.workspace
        listdir = os.listdir(worksp)

        def get_concatenated_files(directory, suffix, init):
            paths = [Path(directory, f) for f in listdir if f.endswith(suffix)]
            concatenated = ''.join(path.read_text() for path in paths)
            result = set()
            for x in concatenated.split('\n'):
                if ':' in x:
                    address = int(x.split(':')[0],16)
                    pc = int(x.split(':')[1].split(' ')[0],16)
                    at_init = '*' in x
                    if at_init == init:
                        result.add(pc)
            return result

        all_init_traces = get_concatenated_files(worksp, 'trace', init=True)
        all_rt_traces = get_concatenated_files(worksp, 'trace', init=False)

        # make sure all init end insns appear somewhere in the init traces
        for pc in p.context['init']:
            self.assertIn(pc, all_init_traces)

        # and all rt end insns appear somewhere in the rt traces
        for pc in p.context['rt']:
            self.assertIn(pc, all_rt_traces)

        # Make sure the function call is correctly produced

        # Extract all valid function names, and make sure we have at least one
        existing_functions = []
        with open(filename, 'r') as src:
            for line in src:
                m = re.match(r'\s*function (\w+).*', line)
                if m:
                    existing_functions.append(m.group(1))

        self.assertGreater(len(existing_functions), 0)

        tx = next(f for f in listdir if f.endswith('0.tx'))
        with open(os.path.join(worksp, tx), 'r') as tx_f:
            lines = tx_f.readlines()

            # implicitly assert the following doesn't throw
            header_idx = lines.index('Function call:\n')
            func_call_summary = lines[header_idx + 1]

            for f in existing_functions:
                if func_call_summary.startswith(f) or func_call_summary.startswith("Constructor"):
                    break
            else:
                self.fail('Could not find a function call summary in workspace output')


    def test_graceful_handle_no_alive_states(self):
        """
        If there are no alive states, or no initial states, we should not crash. issue #795
        """
        # initiate the blockchain
        m = self.mevm
        source_code = '''
        contract Simple {
            function f(uint a) payable public {
                if (a == 65) {
                    revert();
                }
            }
        }
        '''

        # Initiate the accounts
        user_account = m.create_account(balance=1000)
        contract_account = m.solidity_create_contract(source_code, owner=user_account, balance=0)

        contract_account.f(1)  # it works
        contract_account.f(65)  # it works
        with self.assertRaises(NoAliveStates):
            contract_account.f(1)  # no alive states, but try to run a tx anyway

    @unittest.skip("reason")
    def test_reachability(self):
        class StopAtFirstJump414141(Detector):
            def will_decode_instruction_callback(self, state, pc):
                TRUE = bytearray((0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1))
                FALSE = bytearray((0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0))
                #print pc, state.platform.current_vm.instruction
                #Once this address is reached the challenge is won
                if pc == 0x4141414141414141414141414141414141414141:
                    func_id = to_constant(state.platform.current_transaction.data[:4])
                    if func_id == function_selector("print(string)"):
                        func_name, args = ABI.deserialize("print(string)", state.platform.current_transaction.data)
                        raise Return()
                    elif func_id == function_selector("terminate(string)"):
                        func_name, args = ABI.deserialize("terminate(string)", state.platform.current_transaction.data)
                        self.manticore.shutdown()
                        raise Return(TRUE)
                    elif func_id == function_selector("assume(bool)"):
                        func_name, args = ABI.deserialize("assume(bool)", state.platform.current_transaction.data)
                        state.add(args[0])
                        raise Return(TRUE)
                    elif func_id == function_selector("is_symbolic(bytes)"):
                        func_name, args = ABI.deserialize("is_symbolic(bytes)", state.platform.current_transaction.data)
                        try:
                            arg = to_constant(args[0])
                        except:
                            raise Return(TRUE)
                        raise Return(FALSE)
                    elif func_id == function_selector("is_symbolic(uint256)"):
                        func_name, args = ABI.deserialize("is_symbolic(uint256)", state.platform.current_transaction.data)
                        try:
                            arg = to_constant(args[0])
                        except Exception as e:
                            raise Return(TRUE)
                        raise Return(FALSE)
                    elif func_id == function_selector("shutdown(string)"):
                        func_name, args = ABI.deserialize("shutdown(string)", state.platform.current_transaction.data)
                        print("Shutdown", to_constant(args[0]))
                        self.manticore.shutdown()
                    elif func_id == function_selector("can_be_true(bool)"):
                        func_name, args = ABI.deserialize("can_be_true(bool)", state.platform.current_transaction.data)
                        result = solver.can_be_true(state.constraints, args[0] != 0)
                        if result:
                            raise Return(TRUE)
                        raise Return(FALSE)

                    raise Stop()

                #otherwise keep exploring

        mevm = self.mevm
        p = StopAtFirstJump414141()
        mevm.register_detector(p)

        filename = os.path.join(THIS_DIR, 'binaries/reached.sol')
        mevm.multi_tx_analysis(filename, tx_limit=2, contract_name='Reachable')

        context = p.context.get('flags', {})
        self.assertTrue(context.get('found', False))

    def test_preconstraints(self):
        source_code = '''
        contract C {
            constructor() public {}
            function f0() public {}
            function f1(uint a) public payable {}
        }
        '''
        m: ManticoreEVM = self.mevm

        creator_account = m.create_account(balance=1000)
        contract_account = m.solidity_create_contract(source_code, owner=creator_account,
                                                      balance=m.make_symbolic_value())

        m.transaction(caller=creator_account, address=contract_account,
                      data=m.make_symbolic_buffer(320), value=m.make_symbolic_value())

        self.assertEqual(m.count_states(), 2 + 1)
        self.assertEqual(m.count_running_states(), 2)

        contract_account.f1(m.make_symbolic_value())
        self.assertEqual(m.count_states(), 2 + 1)
        self.assertEqual(m.count_running_states(), 2)

        m.preconstrain_symbolic_tx_data = False

        m.transaction(caller=creator_account, address=contract_account,
                      data=m.make_symbolic_buffer(320), value=m.make_symbolic_value())

        self.assertEqual(m.count_states(), 2*(2 + 3) + 1)
        self.assertEqual(m.count_running_states(), 4)

        results = [state.platform.all_transactions[-1].result for state in m.all_states]
        # The REVERTs are triggered in the function dispatcher due to an invalid function selector
        # or a non-zero value send to a non-payable function. The TXERRORs indicate states where the
        # sent value is greater than the senders budget.
        self.assertListEqual(sorted(results), ['REVERT']*(2*2) + ['STOP']*(2*2) + ['TXERROR']*3)

class EthHelpersTest(unittest.TestCase):
    def setUp(self):
        self.bv = BitVec(256)

    def test_concretizer(self):
        policy = 'SOME_NONSTANDARD_POLICY'

        @concretized_args(a=policy)
        def inner_func(self, a, b):
            return a, b

        with self.assertRaises(ConcretizeStack) as cm:
            inner_func(None, self.bv, 34)

        self.assertEqual(cm.exception.pos, 1)
        self.assertEqual(cm.exception.policy, policy)

    def test_concretizer_default(self):
        @concretized_args(b='')
        def inner_func(self, a, b):
            return a, b

        with self.assertRaises(ConcretizeStack) as cm:
            inner_func(None, 34, self.bv)

        self.assertEqual(cm.exception.pos, 2)
        # Make sure the policy isn't blank, i.e. we didn't pass through
        # a falsifiable value, and we selected a default
        self.assertTrue(cm.exception.policy)
        self.assertNotEqual(cm.exception.policy, '')


    def test_concretizer_doesnt_overreach(self):
        @concretized_args(b='')
        def inner_func(self, a, b):
            return a, b

        # Make sure we don't raise when a param is symbolic and its concretization
        # wasn't requested.
        inner_func(None, self.bv, 123)


class EthSolidityCompilerTest(unittest.TestCase):
    def test_run_solc(self):
        source_a = '''
        import "./B.sol";
        contract A {
            function callB(B _b) public { _b.fromA(); }
            function fromB() public { revert(); }
        }
        '''
        source_b = '''
        import "./A.sol";
        contract B {
            function callA(A _a) public { _a.fromB(); }
            function fromA() public { revert(); }
        }
        '''
        d = tempfile.mkdtemp()
        try:
            with open(os.path.join(d, 'A.sol'), 'w') as a, open(os.path.join(d, 'B.sol'), 'w') as b:
                a.write(source_a)
                a.flush()
                b.write(source_b)
                b.flush()
                output, warnings = ManticoreEVM._run_solc(a)
                source_list = output.get('sourceList', [])
                self.assertIn(os.path.split(a.name)[-1], source_list)
                self.assertIn(os.path.split(b.name)[-1], source_list)
        finally:
            shutil.rmtree(d)


    def test_run_solc_with_remappings(self):
        source_a = '''
        import "test/B.sol";
        contract A {
            function callB(B _b) public { _b.fromA(); }
            function fromB() public { revert(); }
        }
        '''
        source_b = '''
        import "../A.sol";
        contract B {
            function callA(A _a) public { _a.fromB(); }
            function fromA() public { revert(); }
        }
        '''
        d = tempfile.mkdtemp()
        lib_dir = os.path.join(d, 'lib')
        os.makedirs(lib_dir)
        try:
            with open(os.path.join(d, 'A.sol'), 'w') as a, open(os.path.join(lib_dir, 'B.sol'), 'w') as b:
                a.write(source_a)
                a.flush()
                b.write(source_b)
                b.flush()
                output, warnings = ManticoreEVM._run_solc(a, solc_remaps=['test=lib'])
                source_list = output.get('sourceList', [])
                self.assertIn("A.sol", source_list)
                self.assertIn("lib/B.sol", source_list)
        finally:
            shutil.rmtree(d)


class EthSolidityMetadataTests(unittest.TestCase):

    def test_tuple_signature_for_components(self):
        self.assertEqual(SolidityMetadata.tuple_signature_for_components([]), '()')
        self.assertEqual(SolidityMetadata.tuple_signature_for_components(
                             [{'type': 'uint256'}, {'type': 'uint256[]'}]),
                         '(uint256,uint256[])')
        self.assertEqual(SolidityMetadata.tuple_signature_for_components(
                            [{"type": "tuple[2]", "components": [{"type": "uint256"}, {"type": "uint256[]"}]},
                             {"type": "tuple", "components": [
                                 {"type": "tuple", "components": [{"type": "string"}]},
                                 {"type": "string"},
                                 {"type": "tuple[]", "components": [{"type": "uint256"}, {"type": "uint256[2]"}]}
                             ]}]),
                         '((uint256,uint256[])[2],((string),string,(uint256,uint256[2])[]))')

    def test_abi_constructor_and_fallback_items(self):
        with disposable_mevm() as m:
            source_code = '''
            contract C {
                constructor(uint a) public {}
                function() public payable {}
            }
            '''
            user_account = m.create_account(balance=1000, name='user_account')
            contract_account = m.solidity_create_contract(source_code, owner=user_account, name='contract_account', args = (0,))
            md: SolidityMetadata = m.get_metadata(contract_account)

            self.assertTrue(md.has_non_default_constructor)
            self.assertDictEqual(md.constructor_abi,
                                 {'inputs': [{'name': 'a', 'type': 'uint256'}],
                                  'payable': False, 'stateMutability': 'nonpayable', 'type': 'constructor'})
            self.assertEqual(md.get_constructor_arguments(), '(uint256)')

            self.assertTrue(md.has_non_default_fallback_function)
            self.assertTrue(md.fallback_function_selector, b'\0\0\0\0')
            fallback = md.get_abi(b'')
            self.assertDictEqual(fallback, md.get_abi(md.fallback_function_selector))
            self.assertDictEqual(fallback, {'payable': True, 'stateMutability': 'payable', 'type': 'fallback'})

            self.assertEqual(md.get_func_signature(md.fallback_function_selector), None)
            self.assertEqual(md.get_func_signature(b''), None)

            self.assertEqual(md.get_func_name(md.fallback_function_selector), '{fallback}')
            self.assertEqual(md.get_func_name(b''), '{fallback}')

            self.assertEqual(md.get_func_argument_types(md.fallback_function_selector), '()')
            self.assertEqual(md.get_func_argument_types(b''), '()')

            self.assertEqual(md.get_func_return_types(md.fallback_function_selector), '()')
            self.assertEqual(md.get_func_return_types(b''), '()')

            self.assertDictEqual(md.signatures, {})
            self.assertSequenceEqual(md.function_selectors, [md.fallback_function_selector])
            self.assertSequenceEqual(md.function_signatures, [])

            with self.assertWarns(ManticoreDeprecationWarning):
                self.assertSequenceEqual(md.hashes, [md.fallback_function_selector])

            with self.assertWarns(ManticoreDeprecationWarning):
                self.assertSequenceEqual(md.functions, ['{fallback}()'])

    def test_overloaded_functions_and_events(self):
        with disposable_mevm() as m:
            source_code = '''
            contract C {                
                function f() public payable returns (uint) {}
                function f(string a) public {}
                
                event E(uint);
                event E(uint, string);
            }
            '''
            user_account = m.create_account(balance=1000, name='user_account')
            contract_account = m.solidity_create_contract(source_code, owner=user_account, name='contract_account')
            md: SolidityMetadata = m.get_metadata(contract_account)

            f0_sel = ABI.function_selector('f()')
            f1_sel = ABI.function_selector('f(string)')

            with self.assertWarns(ManticoreDeprecationWarning):
                self.assertEqual(md.get_hash('f()'), f0_sel)

            self.assertListEqual(sorted(md.function_selectors), sorted([f0_sel, f1_sel]))
            with self.assertWarns(ManticoreDeprecationWarning):
                self.assertListEqual(sorted(md.hashes), sorted([f0_sel, f1_sel, md.fallback_function_selector]))

            e1_sel = ABI.function_selector('E(uint256)')

            f0_abi = md.get_abi(f0_sel)
            f1_abi = md.get_abi(f1_sel)
            self.assertEqual(f0_abi['stateMutability'], 'payable')
            self.assertEqual(f1_abi['stateMutability'], 'nonpayable')
            self.assertFalse(md.has_non_default_fallback_function)
            fallback_abi = md.get_abi(md.fallback_function_selector)
            self.assertDictEqual(fallback_abi, {'payable': False, 'stateMutability': 'nonpayable', 'type': 'fallback'})
            # get_abi is only for functions, not events.
            self.assertEqual(md.get_abi(e1_sel), fallback_abi)

            self.assertEqual(md.get_func_signature(f0_sel), 'f()')
            self.assertEqual(md.get_func_signature(f1_sel), 'f(string)')
            self.assertEqual(md.get_func_signature(md.fallback_function_selector), None)
            self.assertEqual(md.get_func_signature(e1_sel), None)

            self.assertDictEqual(md.signatures, {f0_sel: 'f()', f1_sel: 'f(string)'})

            self.assertListEqual(sorted(md.function_signatures), ['f()', 'f(string)'])
            with self.assertWarns(ManticoreDeprecationWarning):
                self.assertListEqual(sorted(md.functions), ['f()', 'f(string)', '{fallback}()'])

            self.assertEqual(md.get_func_name(f0_sel), 'f')
            self.assertEqual(md.get_func_name(f1_sel), 'f')
            self.assertEqual(md.get_func_name(md.fallback_function_selector), '{fallback}')
            self.assertEqual(md.get_func_name(e1_sel), '{fallback}')

            self.assertEqual(md.get_func_argument_types(f0_sel), '()')
            self.assertEqual(md.get_func_argument_types(f1_sel), '(string)')
            self.assertEqual(md.get_func_argument_types(md.fallback_function_selector), '()')
            self.assertEqual(md.get_func_argument_types(e1_sel), '()')

            self.assertEqual(md.get_func_return_types(f0_sel), '(uint256)')
            self.assertEqual(md.get_func_return_types(f1_sel), '()')
            self.assertEqual(md.get_func_return_types(md.fallback_function_selector), '()')
            self.assertEqual(md.get_func_return_types(e1_sel), '()')

            self.assertFalse(md.has_non_default_constructor)
            self.assertDictEqual(md.constructor_abi,
                                 {'inputs': [], 'payable': False, 'stateMutability': 'nonpayable', 'type': 'constructor'})


class EthSpecificTxIntructionTests(unittest.TestCase):

    def test_jmpdest_check(self):
        '''
            This test that jumping to a JUMPDEST in the operand of a PUSH should 
            be treated as an INVALID instruction.
            https://github.com/trailofbits/manticore/issues/1169
        '''
    
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints)
    
        world.create_account(address=0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6,
                             balance=100000000000000000000000,
                             code=EVMAsm.assemble('PUSH1 0x5b\nPUSH1 0x1\nJUMP')
                            )
        address = 0xf572e5295c57f15886f9b263e2f6d2d6c7b5ec6
        price = 0x5af3107a4000
        data = ''
        caller = 0xcd1722f3947def4cf144679da39c4c32bdc35681
        value = 1000000000000000000
        bytecode = world.get_code(address)        
        gas = 100000

        new_vm = evm.EVM(constraints, address, data, caller, value, bytecode, world=world, gas=gas)

        result = None
        returndata = ''
        try:
            while True:
                new_vm.execute()
        except evm.EndTx as e:
            result = e.result
            if e.result in ('RETURN', 'REVERT'):
                returndata = e.data

        self.assertEqual(result, 'THROW')
        self.assertEqual(new_vm.gas, 99992)
        

    def test_delegatecall_env(self):
        '''
            This test that the delegatecalled environment is identicall to the caller
            https://github.com/trailofbits/manticore/issues/1169
        '''
        constraints = ConstraintSet()
        world = evm.EVMWorld(constraints)
        asm_acc1 = '''  CALLER
                        PUSH1 0x0
                        SSTORE
                        ADDRESS
                        PUSH1 0x1
                        SSTORE
                        CALLVALUE
                        PUSH1 0x2
                        SSTORE
                        STOP
                  '''
        # delegatecall(gas, address, in_offset, in_size, out_offset, out_size)
        asm_acc2 = '''  PUSH1 0x0
                        PUSH2 0X0
                        PUSH1 0x0
                        PUSH2 0X0
                        PUSH32 0x111111111111111111111111111111111111111
                        PUSH32 0x10000
                        DELEGATECALL
                        STOP
            '''

        world.create_account(address=0x111111111111111111111111111111111111111,
                             code=EVMAsm.assemble(asm_acc1))

        world.create_account(address=0x222222222222222222222222222222222222222,
                             code=EVMAsm.assemble(asm_acc2))

        world.create_account(address=0x333333333333333333333333333333333333333,
                             balance=100000000000000000000000,
                             code=EVMAsm.assemble(asm_acc2))

        world.transaction(0x222222222222222222222222222222222222222, caller=0x333333333333333333333333333333333333333, value=10, gas=5000000)


        try:
            while True:
                world.execute()
        except TerminateState as e:
            result = str(e)

        self.assertEqual(result, 'STOP')

        # Check there is something written to the storage of the contract making
        # the delegatecall
        self.assertTrue(world.has_storage(0x222222222222222222222222222222222222222))

        # Caller at delegatecalled contract must be original caller
        self.assertEqual( world.get_storage_data(0x222222222222222222222222222222222222222, 0), 0x333333333333333333333333333333333333333)
        # address at delegatecalled contract must be original address
        self.assertEqual( world.get_storage_data(0x222222222222222222222222222222222222222, 1), 0x222222222222222222222222222222222222222)
        # value at delegatecalled contract must be original value
        self.assertEqual( world.get_storage_data(0x222222222222222222222222222222222222222, 2), 10)

        # check balances
        self.assertEqual(world.get_balance(0x111111111111111111111111111111111111111), 0)
        self.assertEqual(world.get_balance(0x222222222222222222222222222222222222222), 10)
        self.assertEqual(world.get_balance(0x333333333333333333333333333333333333333), 100000000000000000000000-10)

        #checl delegated call storage was not touch
        self.assertFalse(world.has_storage(0x111111111111111111111111111111111111111))
        self.assertEqual( world.get_storage_data(0x111111111111111111111111111111111111111, 0), 0)
        self.assertEqual( world.get_storage_data(0x111111111111111111111111111111111111111, 1), 0)
        self.assertEqual( world.get_storage_data(0x111111111111111111111111111111111111111, 2), 0)
        self.assertFalse(world.has_storage(0x333333333333333333333333333333333333333))


class EthPluginTests(unittest.TestCase):

    def test_FilterFunctions_fallback_function_matching(self):
        """
        Tests that the FilterFunctions plugin matches the fallback function hash correctly. issue #1196
        """
        with disposable_mevm(procs=1) as m:
            source_code = '''
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
            '''
            plugin = FilterFunctions(regexp=r'^$', fallback=True)  # Only matches the fallback function.
            m.register_plugin(plugin)

            creator_account = m.create_account(balance=1000)
            contract_account = m.solidity_create_contract(source_code, owner=creator_account)

            symbolic_data = m.make_symbolic_buffer(320)
            m.transaction(caller=creator_account, address=contract_account, data=symbolic_data, value=0)

            self.assertEqual(m.count_states(), 1)
            self.assertEqual(m.count_running_states(), 1)

            self.assertEqual(len(m.world.all_transactions), 2)

            # The fallbackCounter value must have been increased by 1.
            contract_account.fallbackCounter()
            self.assertEqual(len(m.world.all_transactions), 3)
            self.assertEqual(ABI.deserialize('uint', to_constant(m.world.transactions[-1].return_data)), 123 + 1)

            # The otherCounter value must not have changed.
            contract_account.otherCounter()
            self.assertEqual(len(m.world.all_transactions), 4)
            self.assertEqual(ABI.deserialize('uint', to_constant(m.world.transactions[-1].return_data)), 456)

if __name__ == '__main__':
    unittest.main()
