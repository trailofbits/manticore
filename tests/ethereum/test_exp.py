"""
File name is purposefully not test_* to run this test separately.
"""

import inspect
import unittest

import os
import shutil
from manticore.platforms.evm import EVMWorld
from manticore.core.smtlib import operators, ConstraintSet
from manticore.ethereum import ManticoreEVM
from manticore.ethereum.plugins import KeepOnlyIfStorageChanges
from manticore.utils import config

consts = config.get_group("core")
consts.mprocessing = consts.mprocessing.single

config.get_group("smt").solver = 'yices'
THIS_DIR = os.path.dirname(os.path.abspath(__file__))


class EthSha3TestSymbolicate(unittest.TestCase):
    def setUp(self):
        evm_consts = config.get_group("evm")
        evm_consts.sha3 = evm_consts.sha3.symbolicate

        self.mevm = ManticoreEVM()
        self.worksp = self.mevm.workspace

    def tearDown(self):
        self.mevm = None
        shutil.rmtree(self.worksp)

    def ManticoreEVM(self):
        return self.mevm

    def test_example1(self):
        source_code = """
        contract IsThisVulnerable {
            event Log(string);
            function foo(uint base, uint exponent) payable public{
                if (base ** exponent == 0x12341234){
                    emit Log("Found a bug");
                }
            }
        }
        """

        m = self.ManticoreEVM()
        owner = m.create_account(balance=10000000, name="owner")
        attacker = m.create_account(balance=10000000, name="attacker")
        contract = m.solidity_create_contract(source_code, owner=owner, name="contract")

        xbase = m.make_symbolic_value()
        xexponent = m.make_symbolic_value()
        contract.foo(x, xbase, xexponent)


        found = 0
        for st in m.all_states:
            if not m.fix_unsound_symbolication(st):
                m.kill_state(st)
                continue
            found += len(st.platform.logs)

        self.assertEqual(found, 0)  # log is not reachable
        self.assertEqual(m.count_all_states(), 1)

    def test_example2(self):
        source_code = """
        contract IsThisVulnerable {
            event Log(string);
            function foo(uint x, uint base, uint exponent) payable public{
                if (x == base ** exponent){
                    emit Log("Found a bug");
                }
            }
        }
        """

        m = self.ManticoreEVM()
        owner = m.create_account(balance=10000000, name="owner")
        attacker = m.create_account(balance=10000000, name="attacker")
        contract = m.solidity_create_contract(source_code, owner=owner, name="contract")

        x = m.make_symbolic_value()
        xbase = m.make_symbolic_value()
        xexponent = m.make_symbolic_value()
        contract.foo(x, xbase, xexponent)

        found = 0
        for st in m.all_states:
            if not m.fix_unsound_symbolication(st):
                m.kill_state(st)
                continue
            found += len(st.platform.logs)

        self.assertEqual(found, 1)  # log is reachable
        self.assertEqual(m.count_all_states(), 2)

    def test_example3(self):
        source_code = """
        contract IsThisVulnerable {
            event Log(string);
            function foo(uint xbase, uint xexponent, uint ybase, uint yexponent) payable public{
                if (xbase ** xexponent == ybase ** yexponent){
                    emit Log("Found a bug");
                }
            }
        }
        """

        m = self.ManticoreEVM()
        owner = m.create_account(balance=10000000, name="owner")
        attacker = m.create_account(balance=10000000, name="attacker")
        contract = m.solidity_create_contract(source_code, owner=owner, name="contract")

        xbase = m.make_symbolic_value()
        xexponent = m.make_symbolic_value()
        ybase = m.make_symbolic_value()
        yexponent = m.make_symbolic_value()
        contract.foo(xbase, xexponent, ybase, yexponent)


        found = 0
        for st in m.all_states:
            if not m.fix_unsound_symbolication(st):
                m.kill_state(st)
                continue
            found += len(st.platform.logs)

        self.assertEqual(found, 1)
        # x == y #log
        # x != y
        self.assertEqual(m.count_all_states(), 2)

    def test_example4(self):
        source_code = """
        contract IsThisVulnerable {
            event Log(string);
            function foo(uint xbase, uint xexponent, uint ybase, uint yexponent) payable public{
                if (xbase ** xexponent == ybase ** yexponent){
                    if (xbase != 10) {
                        emit Log("Found a bug"); //Reachable 
                    }
                }
            }
        }
        """

        m = self.ManticoreEVM()
        owner = m.create_account(balance=10000000, name="owner")
        attacker = m.create_account(balance=10000000, name="attacker")
        contract = m.solidity_create_contract(source_code, owner=owner, name="contract")

        xbase = m.make_symbolic_value()
        xexponent = m.make_symbolic_value()
        ybase = m.make_symbolic_value()
        yexponent = m.make_symbolic_value()
        contract.foo(xbase, xexponent, ybase, yexponent)

        found = 0
        for st in m.all_states:
            if not m.fix_unsound_symbolication(st):
                m.kill_state(st)
                continue
            found += len(st.platform.logs)

        self.assertEqual(found, 1)  # log is reachable

        # x==10 && y == 10
        # x==C  && y == C && C != 10   #log
        # x != y
        self.assertEqual(m.count_all_states(), 3)

    def test_example5(self):
        source_code = """
        contract IsThisVulnerable {
            event Log(string);
            function foo(uint xbase, uint xexponent, uint ybase, uint yexponent) payable public{
                if (xbase ** xexponent == ybase ** yexponent){
                    if (xbase != 10 && xexponent == 10 && ybase != 10 && yexponent == 10) {
                        emit Log("Found a bug"); //Reachable 
                    }
                }
            }
        }
        """

        m = self.ManticoreEVM()
        owner = m.create_account(balance=10000000, name="owner")
        attacker = m.create_account(balance=10000000, name="attacker")
        contract = m.solidity_create_contract(source_code, owner=owner, name="contract")

        x = m.make_symbolic_value()
        xbase = m.make_symbolic_value()
        xexponent = m.make_symbolic_value()
        ybase = m.make_symbolic_value()
        yexponent = m.make_symbolic_value()
        contract.foo(x, xbase, xexponent, ybase, yexponent)

        found = 0
        for st in m.all_states:
            if not m.fix_unsound_symbolication(st):
                m.kill_state(st)
                continue
            found += len(st.platform.logs)

        self.assertEqual(found, 1)  # log is reachable
        # x==10 && y == 10
        # x==C  && y == C && C != 10 #log
        # x != y
        self.assertEqual(m.count_all_states(), 3)

    def test_example6(self):
        source_code = """
        contract IsThisVulnerable {
            event Log(string);
            function foo(uint x, uint base, uint exponent) payable public{
                if (x == uint256(sha3(base, exponent))){
                    if(base == 10 && exponent == 10){
                        emit Log("Found a bug");
                    }
                }
            }
        }
        """

        m = self.ManticoreEVM()
        owner = m.create_account(balance=10000000, name="owner")
        attacker = m.create_account(balance=10000000, name="attacker")
        contract = m.solidity_create_contract(source_code, owner=owner, name="contract")

        x = m.make_symbolic_value()
        xbase = m.make_symbolic_value()
        xexponent = m.make_symbolic_value()
        contract.foo(x, xbase, xexponent)
 
        found = 0
        for st in m.all_states:
            if not m.fix_unsound_symbolication(st):
                m.kill_state(st)
                continue
            found += len(st.platform.logs)

        self.assertEqual(found, 1)  # log is reachable

        # x==sha3(10) && y == 10
        # x==sha3(C) && y == C  && C!=10
        # x==sha3(C)  && y != C
        self.assertEqual(m.count_all_states(), 3)

    def test_example7(self):
        source_code = """
        contract IsThisVulnerable {
            event Log(string);
            function foo(uint xbase, uint xexponent, uint ybase, uint yexponent) payable public{
                if (xbase ** xexponent == ybase ** yexponent){
                    if (xbase == 10 && xexponent == 10) {
                        emit Log("Found a bug"); //Reachable 
                    }
                }
            }
        }
        """

        m = self.ManticoreEVM()
        owner = m.create_account(balance=10000000, name="owner")
        attacker = m.create_account(balance=10000000, name="attacker")
        contract = m.solidity_create_contract(source_code, owner=owner, name="contract")

        xbase = m.make_symbolic_value()
        xexponent = m.make_symbolic_value()
        ybase = m.make_symbolic_value()
        yexponent = m.make_symbolic_value()
        contract.foo(xbase, xexponent, ybase, yexponent)

        found = 0
        for st in m.all_states:
            if not m.fix_unsound_symbolication(st):
                m.kill_state(st)
                continue
            found += len(st.platform.logs)

        self.assertEqual(found, 1)  # log is reachable

        # x==y && x == 10
        # x==y && x != 10
        # x!=y
        self.assertEqual(m.count_all_states(), 3)

    def test_example8(self):
        source_code = """
        contract IsThisVulnerable {
            event Log(string);
            function foo(uint xbase, uint xexponent, uint ybase, uint yexponent) payable public{
                if (xbase ** xexponent == ybase ** yexponent){
                    if (xbase == 10 && xexponent == 10) {
                        emit Log("Found a bug"); //Reachable 
                    }
                }
            }
        }
        """

        m = self.ManticoreEVM()
        owner = m.create_account(balance=10000000, name="owner")
        attacker = m.create_account(balance=10000000, name="attacker")
        contract = m.solidity_create_contract(source_code, owner=owner, name="contract")

        xbase = m.make_symbolic_value()
        xexponent = m.make_symbolic_value()
        ybase = m.make_symbolic_value()
        yexponent = m.make_symbolic_value()
        contract.foo(xbase, xexponent, ybase, yexponent)
 
        found = 0
        for st in m.all_states:
            if not m.fix_unsound_symbolication(st):
                m.kill_state(st)
                continue
            found += len(st.platform.logs)

        self.assertEqual(found, 1)  # log is reachable

        # x==y && x == 10
        # x==y && x != 10
        # x!=y
        self.assertEqual(m.count_all_states(), 3)


    def test_essence2(self):
        source_code = """
        contract I_Choose_Not_To_Run {
            event Log(string);
            function foo(uint base, uint exponent) public {

            if( (45**5)**5 == (base ** exponent) **exponent )

                {
                    emit Log("bug");
                }
            }
        }
        """

        m = self.ManticoreEVM()
        owner = m.create_account(balance=10000000, name="owner")
        attacker = m.create_account(balance=10000000, name="attacker")
        contract = m.solidity_create_contract(source_code, owner=owner, name="contract")

        xbase = m.make_symbolic_value()
        xexponent = m.make_symbolic_value()
        contract.foo(xbase, xexponent)

        found = 0
        for st in m.all_states:
            if not m.fix_unsound_symbolication(st):
                m.kill_state(st)
                continue

            m.generate_testcase(st)
            found += len(st.platform.logs)
        self.assertEqual(found, 1)  # log is reachable
        self.assertEqual(m.count_all_states(), 2)


if __name__ == "__main__":
    unittest.main()
