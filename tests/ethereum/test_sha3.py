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
    Modifies the test instance to use specific solc version via compile_args.
    """

    def decorator(func):
        @functools.wraps(func)
        def wrapper(self, *args, **kwargs):
            import os

            try:
                import solcx
            except ImportError:
                # If solcx not available, just run the test
                return func(self, *args, **kwargs)

            try:
                # Install version if needed
                if version not in [str(v) for v in solcx.get_installed_solc_versions()]:
                    print(f"Installing Solidity {version}...")
                    solcx.install_solc(version)

                # Get path to specific solc version
                solc_path = solcx.get_solcx_install_folder() / f"solc-v{version}"
                if solc_path.exists():
                    # Store the solc path in the test instance for use in solidity_create_contract
                    self._test_solc_path = str(solc_path)
                    print(f"Using Solidity {version} at {solc_path}")
                else:
                    print(f"Warning: Solidity {version} binary not found at {solc_path}")
                    self._test_solc_path = None

                # Run the test
                return func(self, *args, **kwargs)

            finally:
                # Clean up
                if hasattr(self, "_test_solc_path"):
                    delattr(self, "_test_solc_path")

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

    @requires_solc("0.5.0")
    def test_essence1(self):
        source_code = """
        pragma solidity ^0.5.0;
        contract I_Choose_Not_To_Run {
            event Log(string);
            function foo(bytes memory x) public {
                // x1 keccak - using 0.5.0 syntax for version diversity
                if (keccak256(bytes("tob")) == keccak256(x)){
                    emit Log("bug");
                }
            }
        }
        """

        m = self.ManticoreEVM()
        owner = m.create_account(balance=10000000, name="owner")
        attacker = m.create_account(balance=10000000, name="attacker")
        compile_args = (
            {"solc": self._test_solc_path}
            if hasattr(self, "_test_solc_path") and self._test_solc_path
            else None
        )
        contract = m.solidity_create_contract(
            source_code, owner=owner, name="contract", compile_args=compile_args
        )

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

    @requires_solc("0.4.24")
    def test_essence2(self):
        source_code = """
        pragma solidity ^0.4.24;
        contract I_Choose_Not_To_Run {
            event Log(string);
            function foo(bytes memory x) public {
                // Testing with 6 levels of nested keccak256 - good balance of complexity and performance
                if(keccak256(keccak256(keccak256(keccak256(keccak256(keccak256("tob")))))) == 
                   keccak256(keccak256(keccak256(keccak256(keccak256(keccak256(abi.encodePacked(x))))))))
                {
                    emit Log("bug");
                }
            }
        }
        """

        m = self.ManticoreEVM()
        owner = m.create_account(balance=10000000, name="owner")
        attacker = m.create_account(balance=10000000, name="attacker")
        compile_args = (
            {"solc": self._test_solc_path}
            if hasattr(self, "_test_solc_path") and self._test_solc_path
            else None
        )
        contract = m.solidity_create_contract(
            source_code, owner=owner, name="contract", compile_args=compile_args
        )

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

    @requires_solc("0.4.24")
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
        compile_args = (
            {"solc": self._test_solc_path}
            if hasattr(self, "_test_solc_path") and self._test_solc_path
            else None
        )
        contract = m.solidity_create_contract(
            source_code, owner=owner, name="contract", compile_args=compile_args
        )

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

    @requires_solc("0.4.24")
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
        compile_args = (
            {"solc": self._test_solc_path}
            if hasattr(self, "_test_solc_path") and self._test_solc_path
            else None
        )
        contract = m.solidity_create_contract(
            source_code, owner=owner, name="contract", compile_args=compile_args
        )

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
