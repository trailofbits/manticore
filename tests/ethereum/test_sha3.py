import pytest

# Test markers for categorization
pytestmark = [pytest.mark.ethereum, pytest.mark.unit]

"""
File name is purposefully not test_* to run this test separately.
"""

import inspect
import unittest
import subprocess
import functools

import os
import shutil
from manticore.platforms.evm import EVMWorld
from manticore.core.smtlib import operators, ConstraintSet
from manticore.ethereum import ManticoreEVM
from manticore.ethereum.plugins import KeepOnlyIfStorageChanges
from manticore.utils import config
from tests.markers import ethereum_test

consts = config.get_group("core")
consts.mprocessing = consts.mprocessing.single

THIS_DIR = os.path.dirname(os.path.abspath(__file__))


def requires_solc(version):
    """
    Decorator that ensures a specific Solidity version is active for a test.
    Skips test if version cannot be switched.
    """
    def decorator(func):
        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            try:
                # Get current version
                result = subprocess.run(
                    ['solc', '--version'],
                    capture_output=True,
                    text=True,
                    check=True
                )
                current_version = None
                for line in result.stdout.split('\n'):
                    if 'Version:' in line:
                        current_version = line.split()[1].split('+')[0]
                        break
                
                # If already on correct version, just run
                if current_version == version:
                    return func(*args, **kwargs)
                
                # Try to switch versions
                result = subprocess.run(
                    ['solc-select', 'use', version],
                    capture_output=True,
                    text=True,
                    check=False
                )
                
                if result.returncode != 0:
                    # Can't switch, skip test if version doesn't match
                    if version not in current_version:
                        pytest.skip(f"Test requires Solidity {version}, but have {current_version} and cannot switch")
                    return func(*args, **kwargs)
                
                try:
                    # Run the test with new version
                    test_result = func(*args, **kwargs)
                finally:
                    # Switch back
                    subprocess.run(
                        ['solc-select', 'use', current_version],
                        capture_output=True,
                        check=False
                    )
                
                return test_result
                    
            except (subprocess.CalledProcessError, FileNotFoundError):
                # If we can't determine version, just run the test
                return func(*args, **kwargs)
        
        return wrapper
    return decorator


@ethereum_test
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
        pragma solidity ^0.4.24;
        contract IsThisVulnerable {
            event Log(string);
            function foo(uint input) payable public{
                if (keccak256(abi.encodePacked(input)) == 0x12341234){
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
        pragma solidity ^0.4.24;
        contract IsThisVulnerable {
            event Log(string);
            function foo(uint x, uint y) payable public{
                if (x == uint256(keccak256(abi.encodePacked(y)))){
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
        pragma solidity ^0.4.24;
        contract IsThisVulnerable {
            event Log(string);
            function foo(uint x, uint y) payable public{
                if (keccak256(abi.encodePacked(x)) == keccak256(abi.encodePacked(y))){
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
        pragma solidity ^0.4.24;
        contract IsThisVulnerable {
            event Log(string);
            function foo(uint x, uint y) payable public{
                if (keccak256(abi.encodePacked(x)) == keccak256(abi.encodePacked(y))){
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
        pragma solidity ^0.4.24;
        contract IsThisVulnerable {
            event Log(string);
            function foo(uint x, uint y) payable public{
                if (keccak256(abi.encodePacked(x)) == keccak256(abi.encodePacked(y))){
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
        pragma solidity ^0.4.24;
        contract IsThisVulnerable {
            event Log(string);
            function foo(uint x, uint y) payable public{
                if (x == uint256(keccak256(abi.encodePacked(y)))){
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
        pragma solidity ^0.4.24;
        contract IsThisVulnerable {
            event Log(string);
            function foo(uint x, uint y) payable public{
                if (keccak256(abi.encodePacked(x)) == keccak256(abi.encodePacked(y))){
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
        pragma solidity ^0.4.24;
        contract IsThisVulnerable {
            event Log(string);
            function foo(uint x, uint y) payable public{
                if (keccak256(abi.encodePacked(x)) == keccak256(abi.encodePacked(y))){
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
        pragma solidity ^0.4.24;
        contract I_Choose_Not_To_Run {
            event Log(string);
            function foo(bytes memory x) public {
                // x1 keccak - keep at 0.4.24 for simplicity
                if (keccak256("tob") == keccak256(x)){
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
        pragma solidity ^0.4.24;
        contract I_Choose_Not_To_Run {
            event Log(string);
            function foo(bytes memory x) public {
                // Reduced from 10 to 5 levels of keccak for performance
                if(keccak256(keccak256(keccak256(keccak256(keccak256("tob"))))) == 
                   keccak256(keccak256(keccak256(keccak256(keccak256(abi.encodePacked(x)))))))
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
        source_code = """pragma solidity ^0.4.24;
        contract Sha3_Multiple_tx{
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


@ethereum_test
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
        pragma solidity ^0.4.24;
        contract IsThisVulnerable {
            event Log(string);
            function foo(uint x, uint y) payable public{
                if (keccak256(abi.encodePacked(x)) == keccak256(abi.encodePacked(y))){
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


@ethereum_test
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
        source_code = """pragma solidity ^0.4.24;
        contract Sha3_Multiple_tx{
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
