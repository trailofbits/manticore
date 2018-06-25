from __future__ import print_function
import shutil
import struct
import tempfile
import unittest
import os

from manticore.core.plugin import Plugin
from manticore.core.smtlib import ConstraintSet, operators
from manticore.core.smtlib.expression import BitVec
from manticore.core.smtlib import solver
from manticore.core.state import State
from manticore.ethereum import ManticoreEVM, DetectIntegerOverflow, Detector, NoAliveStates, ABI, EthereumError
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
        mevm.register_detector(DetectIntegerOverflow())
        filename = os.path.join(THIS_DIR, 'binaries/int_overflow.sol')
        mevm.multi_tx_analysis(filename, tx_limit=1)
        self.assertEqual(len(mevm.global_findings), 3)
        all_findings = ''.join(map(lambda x: x[2], mevm.global_findings))
        self.assertIn('Unsigned integer overflow at SUB instruction', all_findings)
        self.assertIn('Unsigned integer overflow at ADD instruction', all_findings)
        self.assertIn('Unsigned integer overflow at MUL instruction', all_findings)


class EthDetectorsTest(unittest.TestCase):
    def setUp(self):
        self.io = DetectIntegerOverflow()
        self.state = make_mock_evm_state()

    def test_mul_no_overflow(self):
        """
        Regression test added for issue 714, where we were using the ADD ovf check for MUL
        """
        arguments = [1 << 248, self.state.new_symbolic_value(256)]
        self.state.constrain(operators.ULT(arguments[1], 256))
        
        cond = self.io._unsigned_mul_overflow(self.state, *arguments)
        check = self.state.can_be_true(cond)
        self.assertFalse(check)

    def test_mul_overflow0(self):
        arguments = [1 << 249, self.state.new_symbolic_value(256)]
        self.state.constrain(operators.ULT(arguments[1], 256))

        cond = self.io._unsigned_mul_overflow(self.state, *arguments)
        check = self.state.can_be_true(cond)
        self.assertTrue(check)

    def test_mul_overflow1(self):
        arguments = [1 << 255, self.state.new_symbolic_value(256)]

        cond = self.io._unsigned_mul_overflow(self.state, *arguments)
        check = self.state.can_be_true(cond)
        self.assertTrue(check)


class EthAbiTests(unittest.TestCase):
    _multiprocess_can_split = True

    @staticmethod
    def _pack_int_to_32(x):
        return '\x00' * 28 + struct.pack('>I', x)

    def test_dyn_address(self):
        d = [
            'AAAA',                    # function hash
            self._pack_int_to_32(32),  # offset to data start
            self._pack_int_to_32(2),   # data start; # of elements
            self._pack_int_to_32(42),  # element 1
            self._pack_int_to_32(43),  # element 2
        ]
        d = ''.join(d)


        func_id, dynargs = ABI.deserialize(type_spec='func(address[])', data=d)


        self.assertEqual(func_id, 'AAAA')
        self.assertEqual(dynargs, ([42, 43],))

    def test_dyn_bytes(self):
        d = [
            'AAAA',                    # function hash
            self._pack_int_to_32(32),  # offset to data start
            self._pack_int_to_32(30),   # data start; # of elements
            'Z'*30, '\x00'*2
        ]
        d = ''.join(d)

        funcname, dynargs = ABI.deserialize(type_spec='func(bytes)', data=d)

        self.assertEqual(funcname, 'AAAA')
        self.assertEqual(dynargs, ('Z'*30,))

    def test_simple_types0(self):
        d = [
            'AAAA',                    # function hash
            self._pack_int_to_32(32),
            '\xff' * 32,
        ]
        d = ''.join(d)
        funcname, dynargs = ABI.deserialize(type_spec='func(uint256,uint256)', data=d)
        #self.assertEqual(funcname, 'AAAA')
        self.assertEqual(dynargs, (32, 2**256 - 1 ))

    def test_simple_types1(self):
        d = [
            'AAAA',                    # function hash
            self._pack_int_to_32(32),
            '\xff' * 32,
            '\xff'.rjust(32, '\0'),
            self._pack_int_to_32(0x424242),
        ]
        d = ''.join(d)
        funcname, dynargs = ABI.deserialize(type_spec='func(uint256,uint256,bool,address)', data=d)
        #self.assertEqual(funcname, 'AAAA')
        self.assertEqual(dynargs, (32, 2**256 - 1, 0xff, 0x424242 ))


    def test_simple_types_ints(self):
        d = [
            'AAAA',                    # function hash
            '\x7f' + '\xff' *31, # int256 max
            '\x80'.ljust(32, '\0'), # int256 min
        ]
        d = ''.join(d)
        func_id, dynargs = ABI.deserialize(type_spec='func(int256,int256)', data=d)
        self.assertEqual(func_id, "AAAA")
        self.assertEqual(dynargs, ( 2**255 - 1, -(2**255) ))


    def test_address0(self):
        data = '{}\x01\x55{}'.format('\0'*11, '\0'*19)
        parsed = ABI.deserialize('address', data)
        self.assertEqual(parsed, 0x55 << (8 * 19) )

    def test_mult_dyn_types(self):
        d = [
            'AAAA',                    # function hash
            self._pack_int_to_32(0x40),  # offset to data 1 start
            self._pack_int_to_32(0x80),  # offset to data 2 start
            self._pack_int_to_32(10),  # data 1 size
            'helloworld'.ljust(32, '\x00'), # data 1
            self._pack_int_to_32(3),  # data 2 size
            self._pack_int_to_32(3),  # data 2
            self._pack_int_to_32(4),
            self._pack_int_to_32(5),
        ]
        d = ''.join(d)

        func_id, dynargs = ABI.deserialize(type_spec='func(bytes,address[])', data=d)

        self.assertEqual(func_id, 'AAAA')
        self.assertEqual(dynargs, ('helloworld', [3, 4, 5]))

    def test_self_make_and_parse_multi_dyn(self):
        d = ABI.function_call('func(bytes,address[])', 'h'*50, [1, 1, 2, 2, 3, 3] )
        funcid, dynargs = ABI.deserialize(type_spec='func(bytes,address[])', data=d)
        self.assertEqual(funcid, b'\x83}9\xe8')
        self.assertEqual(dynargs, ('h'*50, [1, 1, 2, 2, 3, 3]))


    def test_serialize_tuple(self):
        self.assertEqual(ABI.serialize('(int256)', 0x10), '\0'*31+'\x10')
        self.assertEqual(ABI.serialize('(int256,int256)', 0x10, 0x20), '\0'*31+'\x10'+'\0'*31+'\x20')
        self.assertEqual(ABI.serialize('(int256,(int256,int256))', 0x10, (0x20, 0x30)), '\0'*31+'\x10'+'\0'*31+'\x20'+'\0'*31+'\x30')

    def test_serialize_basic_types_int(self):
        self.assertEqual(ABI.serialize('int256', 0x10), '\0'*31+'\x10')
        self.assertEqual(ABI.deserialize('int256', '\0'*31+'\x10'), 0x10)

        self.assertEqual(ABI.serialize('int256', -0x10), '\xff'*31+'\xf0')
        self.assertEqual(ABI.deserialize('int256', '\xff'*31+'\xf0'), -0x10)

    def test_serialize_basic_types_int8(self):
        self.assertEqual(ABI.serialize('int8', 0x10), '\0'*31+'\x10')
        self.assertEqual(ABI.deserialize('int8', '\0'*31+'\x10'), 0x10)

        self.assertEqual(ABI.serialize('int8', -0x10), '\x00'*31+'\xf0')
        self.assertEqual(ABI.deserialize('int8', '\x00'*31+'\xf0'), -0x10)

    def test_serialize_basic_types_int16(self):
        self.assertEqual(ABI.serialize('int16', 0x100), '\0'*30+'\x01\x00')
        self.assertEqual(ABI.deserialize('int16', '\0'*30+'\x01\x00'), 0x100)

        self.assertEqual(ABI.serialize('int16', -0x10), '\x00'*30+'\xff\xf0')
        self.assertEqual(ABI.deserialize('int16', '\x00'*30+'\xff\xf0'), -0x10)

    def test_serialize_basic_types_uint(self):
        self.assertEqual(ABI.serialize('uint256', 0x10), '\0'*31+'\x10')
        self.assertEqual(ABI.deserialize('uint256', '\0'*31+'\x10'), 0x10)

        self.assertEqual(ABI.serialize('uint256', -0x10), '\xff'*31+'\xf0')
        self.assertEqual(ABI.deserialize('uint256', '\xff'*31+'\xf0'),  0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0L)
        self.assertEqual(ABI.deserialize('uint256', '\xff'*31+'\xf0'),  0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0L)
        self.assertNotEqual(ABI.deserialize('uint256', '\xff'*31+'\xf0'), -0x10L)


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
        data = "\xFF"*32

        parsed = ABI.deserialize('uint', data)
        self.assertEqual(parsed, 2**256 - 1)

        for i in range(8, 257, 8):
            parsed = ABI.deserialize('uint{}'.format(i), data)
            self.assertEqual(parsed, 2**i - 1)

    def test_empty_types(self):
        name, args = ABI.deserialize('func()', '\0'*32)
        self.assertEqual(name, '\x00\x00\x00\x00')
        self.assertEqual(args, tuple())

    def test_function_type(self):
        # setup ABI for function with one function param
        spec = 'func(function)'
        func_id = ABI.function_selector(spec)
        # build bytes24 data for function value (address+selector)
        # calls member id lookup on 'Ethereum Foundation Tip Box' (see https://www.ethereum.org/donate)
        address = ABI._serialize_uint(0xfB6916095ca1df60bB79Ce92cE3Ea74c37c5d359, 20, padding=0)
        selector = ABI.function_selector('memberId(address)')
        function_ref_data = address + selector + '\0'*8
        # build tx call data
        call_data = func_id + function_ref_data 
        parsed_func_id, args = ABI.deserialize(spec, call_data)
        self.assertEqual(parsed_func_id, func_id)
        self.assertEqual(((0xfB6916095ca1df60bB79Ce92cE3Ea74c37c5d359, selector),), args)


class EthTests(unittest.TestCase):
    def setUp(self):
        self.mevm = ManticoreEVM()
        self.worksp = self.mevm.workspace

    def tearDown(self):
        self.mevm=None
        shutil.rmtree(self.worksp)

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
            self.assertEqual(m.accounts['normal{:d}'.format(i)], user_accounts[i])

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
        self.assertEquals(m.count_states(), 1)
        c2 = m.solidity_create_contract(c, owner=owner_account, contract_name='C2', args=[c1.address])
        self.assertEquals(m.count_states(), 1)
        c2.f();
        self.assertEquals(m.count_states(), 1)
        c2.f();
        self.assertEquals(m.count_states(), 1)

        for state in m.all_states:
            world = state.platform
            self.assertEquals(len(world.transactions), 6)
            self.assertEquals(len(world.all_transactions), 6)
            self.assertEquals(len(world.human_transactions), 4)
            self.assertListEqual(['CREATE', 'CREATE', 'CALL', 'CALL', 'CALL', 'CALL'], [x.sort for x in world.all_transactions])
            for tx in world.all_transactions[-4:]:
                self.assertEquals(tx.result, 'RETURN')
                self.assertEquals(state.solve_one(tx.return_data), b'\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01')

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
