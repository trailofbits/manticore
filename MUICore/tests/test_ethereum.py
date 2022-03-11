import unittest
import unittest.mock

from muicore import mui_server
from muicore.MUICore_pb2 import *

from inspect import currentframe, getframeinfo
from pathlib import Path
from uuid import UUID, uuid4
from shutil import rmtree, which
import glob
import time
import os


class MUICoreEVMTest(unittest.TestCase):
    def setUp(self):
        self.dirname = str(Path(getframeinfo(currentframe()).filename).resolve().parent)
        self.contract_path = str(self.dirname / Path("contracts") / Path("adder.sol"))
        self.servicer = mui_server.MUIServicer()
        self.solc_path = str(self.dirname / Path("solc"))

    def tearDown(self):
        for m, mthread in self.servicer.manticore_instances.values():
            m.kill()
            stime = time.time()
            while m.is_running():
                if (time.time() - stime) > 10:
                    time.sleep(1)

    @classmethod
    def tearDownClass(cls):
        for f in glob.glob("mcore_*"):
            if Path(f).is_dir():
                rmtree(f, ignore_errors=True)

    def test_start_with_no_or_invalid_contract_path(self):
        with self.assertRaises(FileNotFoundError) as e:
            self.servicer.StartEVM(EVMArguments(solc_bin=self.solc_path), None)

        expected_exception = "Contract path not specified!"

        self.assertEqual(str(e.exception), expected_exception)

        invalid_contract_path = str(
            self.dirname / Path("contracts") / Path("invalid_contract")
        )
        with self.assertRaises(FileNotFoundError) as e:
            self.servicer.StartEVM(
                EVMArguments(
                    contract_path=invalid_contract_path, solc_bin=self.solc_path
                ),
                None,
            )

        expected_exception = f"Contract path invalid: '{invalid_contract_path}'"

        self.assertEqual(str(e.exception), expected_exception)

    def test_start_with_no_solc_specified_or_in_path(self):
        path_to_use = os.environ["PATH"]
        solc_on_path = which("solc")

        if solc_on_path:
            solc_dir = str(Path(solc_on_path).parent)
            cur_paths = os.environ["PATH"].split(os.pathsep)

            path_to_use = str(os.pathsep).join(
                [dir for dir in cur_paths if dir != solc_dir]
            )

        with self.assertRaises(Exception) as e:
            with unittest.mock.patch.dict(os.environ, {"PATH": path_to_use}):
                mcore_instance = self.servicer.StartEVM(
                    EVMArguments(contract_path=self.contract_path),
                    None,
                )

        self.assertEqual(
            str(e.exception),
            "solc binary neither specified in EVMArguments nor found in PATH!",
        )

    def test_start(self):
        mcore_instance = self.servicer.StartEVM(
            EVMArguments(contract_path=self.contract_path, solc_bin=self.solc_path),
            None,
        )

        try:
            UUID(mcore_instance.uuid)
        except ValueError:
            self.fail(
                "Start() returned ManticoreInstance with missing or malformed UUID"
            )

        self.assertTrue(mcore_instance.uuid in self.servicer.manticore_instances)

        mcore = self.servicer.manticore_instances[mcore_instance.uuid][0]
        self.assertTrue(Path(mcore.workspace).is_dir())

    def test_terminate_running_manticore(self):
        mcore_instance = self.servicer.StartEVM(
            EVMArguments(contract_path=self.contract_path, solc_bin=self.solc_path),
            None,
        )
        m, mthread = self.servicer.manticore_instances[mcore_instance.uuid]

        stime = time.time()
        while not m.is_running():
            if (time.time() - stime) > 5:
                self.fail(
                    f"Manticore instance {mcore_instance.uuid} failed to start running before timeout"
                )
            time.sleep(1)

        t_status = self.servicer.Terminate(mcore_instance, None)
        self.assertTrue(t_status.success)
        self.assertTrue(m.is_killed())

        stime = time.time()
        while m.is_running():
            if (time.time() - stime) > 10:
                self.fail(
                    f"Manticore instance {mcore_instance.uuid} failed to stop running before timeout"
                )
                time.sleep(1)

    def test_terminate_killed_manticore(self):
        mcore_instance = self.servicer.StartEVM(
            EVMArguments(contract_path=self.contract_path, solc_bin=self.solc_path),
            None,
        )
        m, mthread = self.servicer.manticore_instances[mcore_instance.uuid]
        m.kill()
        stime = time.time()
        while m.is_running():
            if (time.time() - stime) > 10:
                self.fail(
                    f"Manticore instance {mcore_instance.uuid} failed to stop running before timeout"
                )
                time.sleep(1)

        t_status = self.servicer.Terminate(mcore_instance, None)

        self.assertTrue(t_status.success)

    def test_terminate_invalid_manticore(self):
        t_status = self.servicer.Terminate(ManticoreInstance(uuid=uuid4().hex), None)
        self.assertFalse(t_status.success)

    def test_get_message_list_running_manticore(self):
        mcore_instance = self.servicer.StartEVM(
            EVMArguments(contract_path=self.contract_path, solc_bin=self.solc_path),
            None,
        )
        m, mthread = self.servicer.manticore_instances[mcore_instance.uuid]

        stime = time.time()
        while m._log_queue.empty() and time.time() - stime < 5:
            time.sleep(1)
            if not m._log_queue.empty():
                deque_messages = list(m._log_queue)
                messages = self.servicer.GetMessageList(mcore_instance, None).messages
                for i in range(len(messages)):
                    self.assertEqual(messages[i].content, deque_messages[i])
                break

    def test_get_message_list_stopped_manticore(self):
        mcore_instance = self.servicer.StartEVM(
            EVMArguments(contract_path=self.contract_path, solc_bin=self.solc_path),
            None,
        )
        m, mthread = self.servicer.manticore_instances[mcore_instance.uuid]

        m.kill()
        stime = time.time()
        while m.is_running():
            if (time.time() - stime) > 10:
                self.fail(
                    f"Manticore instance {mcore_instance.uuid} failed to stop running before timeout"
                )
                time.sleep(1)

        stime = time.time()
        while m._log_queue.empty() and time.time() - stime < 5:
            time.sleep(1)
            if not m._log_queue.empty():
                deque_messages = list(m._log_queue)
                messages = self.servicer.GetMessageList(mcore_instance, None).messages
                for i in range(len(messages)):
                    self.assertEqual(messages[i].content, deque_messages[i])
                break

    def test_get_message_list_invalid_manticore(self):
        message_list = self.servicer.GetMessageList(
            ManticoreInstance(uuid=uuid4().hex), None
        )
        self.assertEqual(len(message_list.messages), 1)
        self.assertEqual(
            message_list.messages[0].content, "Manticore instance not found!"
        )

    def test_get_state_list_running_manticore(self):
        mcore_instance = self.servicer.StartEVM(
            EVMArguments(contract_path=self.contract_path, solc_bin=self.solc_path),
            None,
        )
        m, mthread = self.servicer.manticore_instances[mcore_instance.uuid]

        for i in range(5):
            time.sleep(1)
            state_list = self.servicer.GetStateList(mcore_instance, None)
            all_states = list(
                map(
                    lambda x: x.state_id,
                    list(state_list.active_states)
                    + list(state_list.waiting_states)
                    + list(state_list.forked_states)
                    + list(state_list.errored_states)
                    + list(state_list.complete_states),
                )
            )
            state_ids = m.introspect().keys()

            for sid in state_ids:
                self.assertIn(sid, all_states)

    def test_get_state_list_stopped_manticore(self):
        mcore_instance = self.servicer.StartEVM(
            EVMArguments(contract_path=self.contract_path, solc_bin=self.solc_path),
            None,
        )
        m, mthread = self.servicer.manticore_instances[mcore_instance.uuid]

        m.kill()
        stime = time.time()
        while m.is_running():
            if (time.time() - stime) > 10:
                self.fail(
                    f"Manticore instance {mcore_instance.uuid} failed to stop running before timeout"
                )
                time.sleep(1)

        stime = time.time()
        for i in range(5):
            time.sleep(1)
            state_list = self.servicer.GetStateList(mcore_instance, None)
            all_states = list(
                map(
                    lambda x: x.state_id,
                    list(state_list.active_states)
                    + list(state_list.waiting_states)
                    + list(state_list.forked_states)
                    + list(state_list.errored_states)
                    + list(state_list.complete_states),
                )
            )
            state_ids = m.introspect().keys()

            for sid in state_ids:
                self.assertIn(sid, all_states)

    def test_get_state_list_invalid_manticore(self):
        state_list = self.servicer.GetStateList(
            ManticoreInstance(uuid=uuid4().hex), None
        )

        self.assertFalse(state_list.active_states)
        self.assertFalse(state_list.waiting_states)
        self.assertFalse(state_list.forked_states)
        self.assertFalse(state_list.errored_states)
        self.assertFalse(state_list.complete_states)

    def test_check_manticore_running(self):
        mcore_instance = self.servicer.StartEVM(
            EVMArguments(contract_path=self.contract_path, solc_bin=self.solc_path),
            None,
        )
        m, mthread = self.servicer.manticore_instances[mcore_instance.uuid]

        stime = time.time()
        while not m.is_running():
            if (time.time() - stime) > 10:
                self.fail(
                    f"Manticore instance {mcore_instance.uuid} failed to start running before timeout"
                )
                time.sleep(1)

        self.assertTrue(
            self.servicer.CheckManticoreRunning(mcore_instance, None).is_running
        )

        m.kill()

        stime = time.time()
        while m.is_running():
            if (time.time() - stime) > 10:
                self.fail(
                    f"Manticore instance {mcore_instance.uuid} failed to stop running before timeout"
                )
                time.sleep(1)

        self.assertFalse(
            self.servicer.CheckManticoreRunning(mcore_instance, None).is_running
        )

    def test_check_manticore_running_invalid_manticore(self):
        self.assertFalse(
            self.servicer.CheckManticoreRunning(
                ManticoreInstance(uuid=uuid4().hex), None
            ).is_running
        )
