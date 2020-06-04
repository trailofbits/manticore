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
            function foo(uint input) payable public{
                if (sha3(input) == 0x12341234){
                    emit Log("Found a bug");
                }
            }
        }
        """

        m = self.ManticoreEVM()
        owner = m.create_account(balance=10000000, name="owner")
        attacker = m.create_account(balance=10000000, name="attacker")
        contract = m.solidity_create_contract(source_code, owner=owner, name="contract")

        symbolic_input = m.make_symbolic_value()
        contract.foo(symbolic_input)

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
            function foo(uint x, uint y) payable public{
                if (x == uint256(sha3(y))){
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
        y = m.make_symbolic_value()
        contract.foo(x, y)

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
            function foo(uint x, uint y) payable public{
                if (sha3(x) == sha3(y)){
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
        y = m.make_symbolic_value()
        contract.foo(x, y)

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
            function foo(uint x, uint y) payable public{
                if (sha3(x) == sha3(y)){
                    if (x != 10) {
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
        y = m.make_symbolic_value()
        contract.foo(x, y)

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
            function foo(uint x, uint y) payable public{
                if (sha3(x) == sha3(y)){
                    if (x != 10 && y != 10) {
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
        y = m.make_symbolic_value()
        contract.foo(x, y)

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
            function foo(uint x, uint y) payable public{
                if (x == uint256(sha3(y))){
                    if(y == 10){
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
        y = m.make_symbolic_value()
        contract.foo(x, y)

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
            function foo(uint x, uint y) payable public{
                if (sha3(x) == sha3(y)){
                    if (x == 10) {
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
        y = m.make_symbolic_value()
        contract.foo(x, y)

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
            function foo(uint x, uint y) payable public{
                if (sha3(x) == sha3(y)){
                    if (x == 10) {
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
        y = m.make_symbolic_value()
        contract.foo(x, y)

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

    def test_essence1(self):
        source_code = """
        contract I_Choose_Not_To_Run {
            event Log(string);
            function foo(bytes x) public {
                // x1 keccak
                if (keccak256("tob") == keccak256(abi.encodePacked(x))){
                    emit Log("bug");
                }
            }
        }
        """

        m = self.ManticoreEVM()
        owner = m.create_account(balance=10000000, name="owner")
        attacker = m.create_account(balance=10000000, name="attacker")
        contract = m.solidity_create_contract(source_code, owner=owner, name="contract")

        x = m.make_symbolic_buffer(3)
        contract.foo(x)

        found = 0
        for st in m.all_states:
            if not m.fix_unsound_symbolication(st):
                m.kill_state(st)
                continue
            m.generate_testcase(st)
            found += len(st.platform.logs)
        self.assertEqual(found, 1)  # log is reachable
        self.assertEqual(m.count_all_states(), 2)

    def test_essence2(self):
        source_code = """
        contract I_Choose_Not_To_Run {
            event Log(string);
            function foo(bytes x) public {
                //# x10 keccak
//if(keccak256(keccak256(keccak256(keccak256(keccak256(keccak256(keccak256(keccak256(keccak256(keccak256("tob"))))))))))==keccak256(keccak256(keccak256(keccak256(keccak256(keccak256(keccak256(keccak256(keccak256(keccak256(abi.encodePacked(x))))))))))))
if(keccak256(keccak256(keccak256(keccak256(keccak256(keccak256(keccak256(keccak256(keccak256(keccak256("tob")))))))))) ==  keccak256(keccak256(keccak256(keccak256(keccak256(keccak256(keccak256(keccak256(keccak256(keccak256(abi.encodePacked(x)) ))))))))))

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

        x = m.make_symbolic_buffer(3)
        contract.foo(x)
        found = 0
        for st in m.all_states:
            if not m.fix_unsound_symbolication(st):
                m.kill_state(st)
                continue

            m.generate_testcase(st)
            found += len(st.platform.logs)
        self.assertEqual(found, 1)  # log is reachable
        self.assertEqual(m.count_all_states(), 2)

    def test_essence3(self):
        source_code = """contract Sha3_Multiple_tx{
            event Log(string);
            bytes32 val;
            function foo(uint x) public {
                if (x == 12345){
                    val = keccak256(keccak256(uint(6789)));
                }
                else{
                    if (keccak256(val) == keccak256(keccak256(keccak256(x)))){
                        emit Log("bug");
                    }
                }
            }
        }

        """

        m = self.ManticoreEVM()
        m.register_plugin(KeepOnlyIfStorageChanges())
        owner = m.create_account(balance=10000000, name="owner")
        attacker = m.create_account(balance=10000000, name="attacker")
        contract = m.solidity_create_contract(source_code, owner=owner, name="contract")

        x1 = m.make_symbolic_value()
        contract.foo(x1)
        x2 = m.make_symbolic_value()
        contract.foo(x2)

        for st in m.all_states:
            if not m.fix_unsound_symbolication(st):
                m.kill_state(st)
                continue

        self.assertEqual(m.count_all_states(), 4)

        found = 0
        for st in m.all_states:
            m.generate_testcase(st)
            found += len(st.platform.logs)
        self.assertEqual(found, 1)  # log is reachable


class EthSha3TestConcrete(unittest.TestCase):
    def setUp(self):
        evm_consts = config.get_group("evm")
        evm_consts.sha3 = evm_consts.sha3.concretize

        self.mevm = ManticoreEVM()
        self.worksp = self.mevm.workspace

    def tearDown(self):
        self.mevm = None
        shutil.rmtree(self.worksp)

    def ManticoreEVM(self):
        return self.mevm

    def test_example_concrete_1(self):
        source_code = """
        contract IsThisVulnerable {
            event Log(string);
            function foo(uint x, uint y) payable public{
                if (sha3(x) == sha3(y)){
                    if (x != 10 && y != 10) {
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
        y = m.make_symbolic_value()
        contract.foo(x, y)

        found = 0
        for st in m.all_states:
            if not m.fix_unsound_symbolication(st):
                m.kill_state(st)
                continue
            found += len(st.platform.logs)

        self.assertEqual(found, 1)  # log is reachable (depends on concretization)
        self.assertEqual(m.count_all_states(), 1)  # Only 1 state concretized


class EthSha3TestFake(EthSha3TestSymbolicate):
    def setUp(self):
        evm_consts = config.get_group("evm")
        self.saved_sha3 = evm_consts.sha3
        evm_consts.sha3 = evm_consts.sha3.fake

        self.mevm = ManticoreEVM()
        self.worksp = self.mevm.workspace

    def tearDown(self):
        evm_consts = config.get_group("evm")
        evm_consts.sha3 = self.saved_sha3

    def test_example1(self):
        pass

    def test_essence3(self):
        source_code = """contract Sha3_Multiple_tx{
            event Log(string);
            bytes32 val;
            function foo(uint x) public {
                if (x == 12345){
                    val = keccak256(keccak256(uint(6789)));
                }
                else{
                    if (keccak256(val) == keccak256(keccak256(keccak256(x)))){
                        emit Log("bug");
                    }
                }
            }
        }

        """

        m = self.ManticoreEVM()
        m.register_plugin(KeepOnlyIfStorageChanges())
        owner = m.create_account(balance=10000000, name="owner")
        attacker = m.create_account(balance=10000000, name="attacker")
        contract = m.solidity_create_contract(source_code, owner=owner, name="contract")

        x1 = m.make_symbolic_value()
        contract.foo(x1)
        x2 = m.make_symbolic_value()
        contract.foo(x2)

        for st in m.all_states:
            if not m.fix_unsound_symbolication(st):
                m.kill_state(st)
                continue

        self.assertTrue(m.count_all_states() >= 4)  # Some fake results may appear

        found = 0
        for st in m.all_states:
            m.generate_testcase(st)
            found += len(st.platform.logs)
        self.assertTrue(found >= 1)  # log is reachable


if __name__ == "__main__":
    unittest.main()
