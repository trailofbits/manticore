import unittest
import os

from manticore.core.smtlib import ConstraintSet, operators
from manticore.core.smtlib.expression import BitVec
from manticore.core.state import State
from manticore.ethereum import ManticoreEVM, IntegerOverflow, Detector
from manticore.platforms.evm import EVMWorld, ConcretizeStack, concretized_args


THIS_DIR = os.path.dirname(os.path.abspath(__file__))

# FIXME(mark): Remove these two lines when logging works for ManticoreEVM
from manticore.utils.log import init_logging

init_logging()


class EthDetectorsIntegrationTest(unittest.TestCase):
    def test_int_ovf(self):
        mevm = ManticoreEVM()
        mevm.register_detector(IntegerOverflow())
        filename = os.path.join(THIS_DIR, 'binaries/int_overflow.sol')
        mevm.multi_tx_analysis(filename)
        self.assertEqual(len(mevm.global_findings), 3)
        all_findings = ''.join(map(lambda x: x[2], mevm.global_findings))
        self.assertIn('underflow at SUB', all_findings)
        self.assertIn('overflow at ADD', all_findings)
        self.assertIn('overflow at MUL', all_findings)


class EthDetectors(unittest.TestCase):
    def setUp(self):
        self.io = IntegerOverflow()
        self.state = self.make_mock_evm_state()

    @staticmethod
    def make_mock_evm_state():
        cs = ConstraintSet()
        fakestate = State(cs, EVMWorld(cs))
        return fakestate

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


class EthTests(unittest.TestCase):
    def test_emit_did_execute_end_instructions(self):
        class TestDetector(Detector):
            def did_evm_execute_instruction_callback(self, state, instruction, arguments, result):
                if instruction.is_endtx:
                    with self.locked_context('insns', dict) as d:
                        d[instruction.semantics] = True

        mevm = ManticoreEVM()
        p = TestDetector()
        mevm.register_detector(p)

        filename = os.path.join(THIS_DIR, 'binaries/int_overflow.sol')
        mevm.multi_tx_analysis(filename, tx_limit=2)

        self.assertIn('insns', p.context)
        context = p.context['insns']
        self.assertIn('STOP', context)
        self.assertIn('RETURN', context)
        self.assertIn('REVERT', context)

    def test_can_create(self):
        mevm = ManticoreEVM()
        source_code = """
        contract X { function X(address x) {} }
        contract C { function C(address x) { new X(x); }
        }
        """
        # Make sure that we can can call CREATE without raising an exception
        owner = mevm.create_account(balance=1000)
        x = mevm.create_account(balance=0)
        contract_account = mevm.solidity_create_contract(source_code,
                contract_name="C", owner=owner, args=[x])

    def test_writebuffer_doesnt_raise(self):
        mevm = ManticoreEVM()
        source_code = """
	contract X {
	    mapping(address => uint) private balance;
	    function f(address z) returns (uint) { return balance[z]; }
	}
	contract C {
	  X y;
	  function C() {
	    y = new X();
	    uint z = y.f(0);
	  }
	}"""
        # Make sure that write_buffer (used by RETURN) succeeds without errors
        owner = mevm.create_account(balance=1000)
        x = mevm.create_account(balance=0)
        contract_account = mevm.solidity_create_contract(source_code,
                contract_name="C", owner=owner, args=[x])



    def test_reachability(self):
        class StopAtFirstJump414141(Detector):
            def will_decode_instruction_callback(self, state, pc):
                if pc == 0x4141414141414141414141414141414141414141:
                    print "FOUND!"
                    with self.locked_context('flags', dict) as d:
                        d['found'] = True
                    self.manticore.terminate()

        mevm = ManticoreEVM()
        p = StopAtFirstJump414141()
        mevm.register_detector(p)

        filename = os.path.join(THIS_DIR, 'binaries/reached.sol')
        mevm.multi_tx_analysis(filename, tx_limit=2)

        context = p.context.get('flags', {})
        self.assertTrue(context.get('found', False))


class EthHelpers(unittest.TestCase):
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


