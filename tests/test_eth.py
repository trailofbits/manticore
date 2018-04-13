from builtins import *
import unittest
import os

from manticore.core.plugin import Plugin
from manticore.core.smtlib import ConstraintSet, operators
from manticore.core.smtlib.expression import BitVec
from manticore.core.state import State

from manticore.ethereum import ManticoreEVM, IntegerOverflow, Detector, NoAliveStates
from manticore.platforms.evm import EVMWorld, ConcretizeStack, Create, concretized_args

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
        all_findings = ''.join(x[2] for x in mevm.global_findings)
        self.assertIn('underflow at SUB', all_findings)
        self.assertIn('overflow at ADD', all_findings)
        self.assertIn('overflow at MUL', all_findings)


class EthDetectorsTest(unittest.TestCase):
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
                if instruction.semantics in ('REVERT', 'STOP'):
                    with self.locked_context('insns', set) as s:
                        s.add(instruction.semantics)

        mevm = ManticoreEVM()
        p = TestDetector()
        mevm.register_detector(p)

        filename = os.path.join(THIS_DIR, 'binaries/int_overflow.sol')
        mevm.multi_tx_analysis(filename, tx_limit=1)

        self.assertIn('insns', p.context)
        context = p.context['insns']
        self.assertIn('STOP', context)
        self.assertIn('REVERT', context)

    def test_end_instruction_trace(self):
        """
        Make sure that the trace files are correct, and include the end instructions
        """
        class TestPlugin(Plugin):
            """
            Record the pcs of all end instructions encountered. Source of truth.
            """
            def will_evm_execute_instruction_callback(self, state, instruction, arguments):
                if isinstance(state.platform.current.last_exception, Create):
                    name = 'init'
                else:
                    name = 'rt'

                # collect all end instructions based on whether they are in init or rt
                if instruction.semantics in ('REVERT', 'STOP', 'RETURN'):
                    with self.locked_context(name) as d:
                        d.append(state.platform.current.pc)

        mevm = ManticoreEVM()
        p = TestPlugin()
        mevm.register_plugin(p)

        filename = os.path.join(THIS_DIR, 'binaries/int_overflow.sol')
        mevm.multi_tx_analysis(filename, tx_limit=1)

        worksp = mevm.workspace
        listdir = os.listdir(worksp)



        def get_concatenated_files(directory, suffix):
            paths = [os.path.join(directory, f) for f in listdir if f.endswith(suffix)]
            concatenated = ''.join(open(path).read() for path in paths)
            return concatenated

        all_init_traces = get_concatenated_files(worksp, 'init.trace')
        all_rt_traces = get_concatenated_files(worksp, 'rt.trace')

        # make sure all init end insns appear somewhere in the init traces
        for pc in p.context['init']:
            self.assertIn(':0x{:x}'.format(pc), all_init_traces)

        # and all rt end insns appear somewhere in the rt traces
        for pc in p.context['rt']:
            self.assertIn(':0x{:x}'.format(pc), all_rt_traces)


    def test_graceful_handle_no_alive_states(self):
        """
        If there are no alive states, or no initial states, we should not crash. issue #795
        """
        # initiate the blockchain
        m = ManticoreEVM()
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


