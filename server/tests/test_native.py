import glob
import time
import unittest
from inspect import currentframe, getframeinfo
from pathlib import Path
from shutil import rmtree
from uuid import UUID, uuid4

from muicore import mui_server
from muicore.MUICore_pb2 import *


class MUICoreNativeTest(unittest.TestCase):
    def setUp(self):
        self.dirname = str(Path(getframeinfo(currentframe()).filename).resolve().parent)
        self.binary_path = str(
            self.dirname / Path("binaries") / Path("arguments_linux_amd64")
        )
        self.servicer = mui_server.MUIServicer()

    def tearDown(self):
        for mwrapper in self.servicer.manticore_instances.values():
            mwrapper.manticore_object.kill()
            stime = time.time()
            while mwrapper.manticore_object.is_running():
                time.sleep(1)
                if (time.time() - stime) > 10:
                    break

    @classmethod
    def tearDownClass(cls):
        for f in glob.glob("mcore_*"):
            if Path(f).is_dir():
                rmtree(f, ignore_errors=True)

    def test_start_with_no_or_invalid_binary_path(self):
        with self.assertRaises(FileNotFoundError) as e:
            self.servicer.StartNative(NativeArguments(), None)

        expected_exception = "[Errno 2] No such file or directory: ''"

        self.assertEqual(str(e.exception), expected_exception)

        invalid_binary_path = str(
            self.dirname / Path("binaries") / Path("invalid_binary")
        )
        with self.assertRaises(FileNotFoundError) as e:
            self.servicer.StartNative(
                NativeArguments(program_path=invalid_binary_path), None
            )

        expected_exception = (
            f"[Errno 2] No such file or directory: '{invalid_binary_path}'"
        )

        self.assertEqual(str(e.exception), expected_exception)

    def test_start(self):
        mcore_instance = self.servicer.StartNative(
            NativeArguments(program_path=self.binary_path), None
        )

        try:
            UUID(mcore_instance.uuid)
        except ValueError:
            self.fail(
                "Start() returned ManticoreInstance with missing or malformed UUID"
            )

        self.assertTrue(mcore_instance.uuid in self.servicer.manticore_instances)

        mcore = self.servicer.manticore_instances[mcore_instance.uuid].manticore_object
        self.assertTrue(Path(mcore.workspace).is_dir())

    def test_terminate_running_manticore(self):
        mcore_instance = self.servicer.StartNative(
            NativeArguments(program_path=self.binary_path), None
        )
        mwrapper = self.servicer.manticore_instances[mcore_instance.uuid]

        stime = time.time()
        while not mwrapper.manticore_object.is_running():
            if (time.time() - stime) > 5:
                self.fail(
                    f"Manticore instance {mcore_instance.uuid} failed to start running before timeout"
                )
            time.sleep(1)

        t_status = self.servicer.Terminate(mcore_instance, None)
        self.assertTrue(t_status.success)
        self.assertTrue(mwrapper.manticore_object.is_killed())

        stime = time.time()
        while mwrapper.manticore_object.is_running():
            if (time.time() - stime) > 10:
                self.fail(
                    f"Manticore instance {mcore_instance.uuid} failed to stop running before timeout"
                )
            time.sleep(1)

    def test_terminate_killed_manticore(self):
        mcore_instance = self.servicer.StartNative(
            NativeArguments(program_path=self.binary_path), None
        )
        mwrapper = self.servicer.manticore_instances[mcore_instance.uuid]
        mwrapper.manticore_object.kill()
        stime = time.time()
        while mwrapper.manticore_object.is_running():
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
        mcore_instance = self.servicer.StartNative(
            NativeArguments(program_path=self.binary_path), None
        )
        mwrapper = self.servicer.manticore_instances[mcore_instance.uuid]

        stime = time.time()
        while mwrapper.manticore_object._log_queue.empty() and time.time() - stime < 5:
            time.sleep(1)
            if not mwrapper.manticore_object._log_queue.empty():
                deque_messages = list(mwrapper.manticore_object._log_queue)
                messages = self.servicer.GetMessageList(mcore_instance, None).messages
                for i in range(len(messages)):
                    self.assertEqual(messages[i].content, deque_messages[i])
                break

    def test_get_message_list_stopped_manticore(self):
        mcore_instance = self.servicer.StartNative(
            NativeArguments(program_path=self.binary_path), None
        )
        mwrapper = self.servicer.manticore_instances[mcore_instance.uuid]

        mwrapper.manticore_object.kill()
        stime = time.time()
        while mwrapper.manticore_object.is_running():
            if (time.time() - stime) > 10:
                self.fail(
                    f"Manticore instance {mcore_instance.uuid} failed to stop running before timeout"
                )
            time.sleep(1)

        stime = time.time()
        while mwrapper.manticore_object._log_queue.empty() and time.time() - stime < 5:
            time.sleep(1)
            if not mwrapper.manticore_object._log_queue.empty():
                deque_messages = list(mwrapper.manticore_object._log_queue)
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
        mcore_instance = self.servicer.StartNative(
            NativeArguments(program_path=self.binary_path), None
        )
        mwrapper = self.servicer.manticore_instances[mcore_instance.uuid]

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
            state_ids = mwrapper.manticore_object.introspect().keys()

            for sid in state_ids:
                self.assertIn(sid, all_states)

    def test_get_state_list_stopped_manticore(self):
        mcore_instance = self.servicer.StartNative(
            NativeArguments(program_path=self.binary_path), None
        )
        mwrapper = self.servicer.manticore_instances[mcore_instance.uuid]

        mwrapper.manticore_object.kill()
        stime = time.time()
        while mwrapper.manticore_object.is_running():
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
            state_ids = mwrapper.manticore_object.introspect().keys()

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
        mcore_instance = self.servicer.StartNative(
            NativeArguments(program_path=self.binary_path), None
        )
        mwrapper = self.servicer.manticore_instances[mcore_instance.uuid]

        stime = time.time()
        while not mwrapper.manticore_object.is_running():
            if (time.time() - stime) > 10:
                self.fail(
                    f"Manticore instance {mcore_instance.uuid} failed to start running before timeout"
                )
            time.sleep(1)

        self.assertTrue(
            self.servicer.CheckManticoreRunning(mcore_instance, None).is_running
        )

        mwrapper.manticore_object.kill()

        stime = time.time()
        while mwrapper.manticore_object.is_running():
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
