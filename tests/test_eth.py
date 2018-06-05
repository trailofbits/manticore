from builtins import *
import tempfile
import struct
import shutil
import unittest
import os

from manticore.core.plugin import Plugin
from manticore.core.smtlib import ConstraintSet, operators
from manticore.core.smtlib.expression import BitVec
from manticore.core.smtlib import solver
from manticore.core.state import State
from manticore.ethereum import ManticoreEVM, IntegerOverflow, Detector, NoAliveStates, ABI, EthereumError
from manticore.platforms.evm import EVMWorld, ConcretizeStack, concretized_args, Return, Stop
from manticore.core.smtlib.visitors import pretty_print, translate_to_smtlib, simplify, to_constant

import shutil

THIS_DIR = os.path.dirname(os.path.abspath(__file__))

# FIXME(mark): Remove these two lines when logging works for ManticoreEVM
from manticore.utils.log import init_logging

init_logging()

def make_mock_evm_state():
    cs = ConstraintSet()
    fakestate = State(cs, EVMWorld(cs))
    return fakestate


class EthDetectorsIntegrationTest(unittest.TestCase):
    def test_int_ovf(self):
        mevm = ManticoreEVM()
        mevm.register_detector(IntegerOverflow())
        filename = os.path.join(THIS_DIR, 'binaries/int_overflow.sol')
        mevm.multi_tx_analysis(filename, tx_limit=1)
        self.assertEqual(len(mevm.global_findings), 3)
        all_findings = ''.join(x[2] for x in mevm.global_findings)
        self.assertIn('underflow at SUB', all_findings)
        self.assertIn('overflow at ADD', all_findings)
        self.assertIn('overflow at MUL', all_findings)


class EthDetectorsTest(unittest.TestCase):
    def setUp(self):
        self.io = IntegerOverflow()
        self.state = make_mock_evm_state()

    def test_mul_no_overflow(self):
        """
        Regression test added for issue 714, where we were using the ADD ovf check for MUL
        """
        arguments = [1 << (8 * 31), self.state.new_symbolic_value(256)]
        self.state.constrain(operators.ULT(arguments[1], 256))

        # TODO(mark) We should actually call into the EVM cpu here, and below, rather than
        # effectively copy pasting what the MUL does
        result = arguments[0] * arguments[1]

        check = self.io._can_mul_overflow(self.state, result, *arguments)
        self.assertFalse(check)

    def test_mul_overflow0(self):
        arguments = [2 << (8 * 31), self.state.new_symbolic_value(256)]
        self.state.constrain(operators.ULT(arguments[1], 256))

        result = arguments[0] * arguments[1]

        check = self.io._can_mul_overflow(self.state, result, *arguments)
        self.assertTrue(check)

    def test_mul_overflow1(self):
        arguments = [1 << 255, self.state.new_symbolic_value(256)]

        result = arguments[0] * arguments[1]

        check = self.io._can_mul_overflow(self.state, result, *arguments)
        self.assertTrue(check)


class EthAbiTests(unittest.TestCase):
    _multiprocess_can_split = True

    @staticmethod
    def _pack_int_to_32(x):
        return b'\x00' * 28 + struct.pack('>I', x)

    def test_dyn_address(self):
        d = [
            b'AAAA',                    # function hash
            self._pack_int_to_32(32),  # offset to data start
            self._pack_int_to_32(2),   # data start; # of elements
            self._pack_int_to_32(42),  # element 1
            self._pack_int_to_32(43),  # element 2
        ]
        d = b''.join(d)

        funcname, dynargs = ABI.parse(type_spec='func(address[])', data=d)

        self.assertEqual(funcname, 'func')
        self.assertEqual(dynargs, ([42, 43],))

    def test_dyn_bytes(self):
        d = [
            b'AAAA',                    # function hash
            self._pack_int_to_32(32),  # offset to data start
            self._pack_int_to_32(30),   # data start; # of elements
            b'Z'*30, b'\x00'*2
        ]
        d = b''.join(d)

        funcname, dynargs = ABI.parse(type_spec='func(bytes)', data=d)

        self.assertEqual(funcname, 'func')
        self.assertEqual(dynargs, (b'Z'*30,))

    def test_simple_types(self):
        d = [
            b'AAAA',                    # function hash
            self._pack_int_to_32(32),
            b'\xff' * 32,
            b'\xff'.rjust(32, b'\0'),
            self._pack_int_to_32(0x424242),
            b'\x7f' + b'\xff' *31, # int256 max
            b'\x80'.ljust(32, b'\0'), # int256 min


        ]
        d = b''.join(d)

        funcname, dynargs = ABI.parse(type_spec='func(uint256,uint256,bool,address,int256,int256)', data=d)

        self.assertEqual(funcname, 'func')
        self.assertEqual(dynargs, (32, 2**256 - 1, 0xff, 0x424242, 2**255 - 1,-(2**255) ))

    def test_address0(self):
        data = '{}\x01\x55{}'.format('\0'*11, '\0'*19)
        parsed = ABI.parse('address', data)
        self.assertEqual(parsed, 0x55 << (8 * 19) )

    def test_mult_dyn_types(self):
        d = [
            b'AAAA',                    # function hash
            self._pack_int_to_32(0x40),  # offset to data 1 start
            self._pack_int_to_32(0x80),  # offset to data 2 start
            self._pack_int_to_32(10),  # data 1 size
            b'helloworld'.ljust(32, b'\x00'), # data 1
            self._pack_int_to_32(3),  # data 2 size
            self._pack_int_to_32(3),  # data 2
            self._pack_int_to_32(4),
            self._pack_int_to_32(5),
        ]
        d = b''.join(d)

        funcname, dynargs = ABI.parse(type_spec='func(bytes,address[])', data=d)

        self.assertEqual(funcname, 'func')
        self.assertEqual(dynargs, (b'helloworld', [3, 4, 5]))

    @unittest.skip("TODO: fix ABI")
    def test_self_make_and_parse_multi_dyn(self):
        d = ABI.make_function_call('func', 'h'*50, [1, 1, 2, 2, 3, 3] )
        d = b''.join(d)
        funcname, dynargs = ABI.parse(type_spec='func(bytes,address[])', data=d)
        self.assertEqual(funcname, 'func')
        self.assertEqual(dynargs, ('h'*50, [1, 1, 2, 2, 3, 3]))

    def test_parse_invalid_int(self):
        with self.assertRaises(EthereumError):
            ABI.parse("intXXX", "\xFF")
            ABI.parse("uintXXX", "\xFF")

    def test_parse_invalid_int_too_big(self):
        with self.assertRaises(EthereumError):
            ABI.parse("int3000", "\xFF")
            ABI.parse("uint3000", "\xFF")

    def test_parse_invalid_int_negative(self):
        with self.assertRaises(EthereumError):
            ABI.parse("int-8", "\xFF")
            ABI.parse("uint-8", "\xFF")

    def test_parse_invalid_int_not_pow_of_two(self):
        with self.assertRaises(EthereumError):
            ABI.parse("int31", "\xFF")
            ABI.parse("uint31", "\xFF")

    def test_parse_valid_int0(self):
        ret = ABI.parse("int8", "\x10"*32)
        self.assertEqual(ret, 0x10)

    def test_parse_valid_int1(self):
        ret = ABI.parse("int", "\x10".ljust(32, '\0'))
        self.assertEqual(ret, 1 << 252)

    def test_parse_valid_int2(self):
        ret = ABI.parse("int40", "\x40\x00\x00\x00\x00".rjust(32, '\0'))
        self.assertEqual(ret, 1 << 38)

    def test_valid_uint(self):
        data = "\xFF"*32

        parsed = ABI.parse('uint', data)
        self.assertEqual(parsed, 2**256 - 1)

        for i in range(8, 257, 8):
            parsed = ABI.parse('uint{}'.format(i), data)
            self.assertEqual(parsed, 2**i - 1)

    def test_empty_types(self):
        name, args = ABI.parse('func()', '\0'*32)
        self.assertEqual(name, 'func')
        self.assertEqual(args, tuple())

    def test_function_type(self):
        # setup ABI for function with one function param
        func_name = 'func'
        spec = func_name+'(function)'
        func_id = ABI.make_function_id(spec)
        # build bytes24 data for function value (address+selector)
        # calls member id lookup on 'Ethereum Foundation Tip Box' (see https://www.ethereum.org/donate)
        address = b''.join(ABI.serialize_uint(0xfB6916095ca1df60bB79Ce92cE3Ea74c37c5d359, 20))
        selector = ABI.make_function_id('memberId(address)')
        function_ref_data = address + selector
        # build tx call data
        call_data = b''.join([
            func_id,
            function_ref_data,
            b'\0'*8
        ])
        name, args = ABI.parse(spec, call_data)
        self.assertEqual(name, func_name)
        self.assertEqual(args, (function_ref_data,))


class EthTests(unittest.TestCase):
    def setUp(self):
        self.mevm = ManticoreEVM(procs=1)
        self.worksp = self.mevm.workspace

    def tearDown(self):
        self.mevm=None
        #shutil.rmtree(self.worksp)

    def test_emit_did_execute_end_instructions(self):
        """
        Tests whether the did_evm_execute_instruction event is fired for instructions that internally trigger
        an exception
        """
        class TestDetector(Detector):
            def did_evm_execute_instruction_callback(self, state, instruction, arguments, result):
                if instruction.is_endtx:
                    with self.locked_context('insns', dict) as d:
                        d[instruction.semantics] = True

        mevm = self.mevm
        p = TestDetector()
        mevm.register_detector(p)

        filename = os.path.join(THIS_DIR, 'binaries/int_overflow.sol')
        mevm.multi_tx_analysis(filename, tx_limit=2)

        self.assertIn('insns', p.context)
        context = p.context['insns']
        self.assertIn('STOP', context)
        self.assertIn('RETURN', context)
        self.assertIn('REVERT', context)

    @unittest.skip("TODO: fix ABI")
    def test_end_instruction_trace(self):
        """
        Make sure that the trace files are correct, and include the end instructions
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
                            d.append(instruction.offset)
                except Exception as e:
                    raise

        mevm = self.mevm
        p = TestPlugin()
        mevm.register_plugin(p)


        filename = os.path.join(THIS_DIR, 'binaries/int_overflow.sol')

        mevm.multi_tx_analysis(filename, tx_limit=1)

        worksp = mevm.workspace
        listdir = os.listdir(worksp)

        def get_concatenated_files(directory, suffix, init):
            paths = [os.path.join(directory, f) for f in listdir if f.endswith(suffix)]
            concatenated = ''.join(open(path).read() for path in paths)
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
            contract_account.f(m.SValue)  # no alive states, but try to run a tx anyway

    @unittest.skip("reason")
    def test_reachability(self):
        class StopAtFirstJump414141(Detector):
            def will_decode_instruction_callback(self, state, pc):
                TRUE = bytearray((0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1))
                FALSE = bytearray((0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0))
                #print(pc, state.platform.current_vm.instruction)
                #Once this address is reached the challenge is won
                if pc == 0x4141414141414141414141414141414141414141:
                    func_id = to_constant(state.platform.current_transaction.data[:4])
                    if func_id == ABI.make_function_id("print(string)"):
                        func_name, args = ABI.parse("print(string)", state.platform.current_transaction.data)
                        raise Return()
                    elif func_id == ABI.make_function_id("terminate(string)"):
                        func_name, args = ABI.parse("terminate(string)", state.platform.current_transaction.data)
                        self.manticore.shutdown()
                        raise Return(TRUE)
                    elif func_id == ABI.make_function_id("assume(bool)"):
                        func_name, args = ABI.parse("assume(bool)", state.platform.current_transaction.data)
                        state.add(args[0])
                        raise Return(TRUE)
                    elif func_id == ABI.make_function_id("is_symbolic(bytes)"):
                        func_name, args = ABI.parse("is_symbolic(bytes)", state.platform.current_transaction.data)
                        try:
                            arg = to_constant(args[0])
                        except:
                            raise Return(TRUE)
                        raise Return(FALSE)
                    elif func_id == ABI.make_function_id("is_symbolic(uint256)"):
                        func_name, args = ABI.parse("is_symbolic(uint256)", state.platform.current_transaction.data)
                        try:
                            arg = to_constant(args[0])
                        except Exception as e:
                            raise Return(TRUE)
                        raise Return(FALSE)
                    elif func_id == ABI.make_function_id("shutdown(string)"):
                        func_name, args = ABI.parse("shutdown(string)", state.platform.current_transaction.data)
                        print("Shutdown", to_constant(args[0]))
                        self.manticore.shutdown()
                    elif func_id == ABI.make_function_id("can_be_true(bool)"):
                        func_name, args = ABI.parse("can_be_true(bool)", state.platform.current_transaction.data)
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

        self.assertEquals(cm.exception.pos, 1)
        self.assertEquals(cm.exception.policy, policy)

    def test_concretizer_default(self):
        @concretized_args(b='')
        def inner_func(self, a, b):
            return a, b

        with self.assertRaises(ConcretizeStack) as cm:
            inner_func(None, 34, self.bv)

        self.assertEquals(cm.exception.pos, 2)
        # Make sure the policy isn't blank, i.e. we didn't pass through
        # a falsifiable value, and we selected a default
        self.assertTrue(cm.exception.policy)
        self.assertNotEquals(cm.exception.policy, '')


    def test_concretizer_doesnt_overreach(self):
        @concretized_args(b='')
        def inner_func(self, a, b):
            return a, b

        # Make sure we don't raise when a param is symbolic and its concretization
        # wasn't requested.
        inner_func(None, self.bv, 123)


class EthSolidityCompilerTest(unittest.TestCase):
    def test_run_solc(self):
        source_a = u'''
        import "./B.sol";
        contract A {
            function callB(B _b) public { _b.fromA(); }
            function fromB() public { revert(); }
        }
        '''
        source_b = u'''
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
