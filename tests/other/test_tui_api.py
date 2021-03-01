import unittest
import threading
import socket
import select
import subprocess
import logging
import time
import sys

from google.protobuf.message import DecodeError
from manticore.core.state_pb2 import StateList, State, MessageList
from pathlib import Path


PYTHON_BIN: str = sys.executable

HOST = "localhost"
PORT = 4123

ms_file = str(
    Path(__file__).parent.parent.parent.joinpath("examples", "linux", "binaries", "multiple-styles")
)

finished = False
logs = []
state_captures = []


def fetch_update():
    logger = logging.getLogger("FetchThread")
    while not finished:
        try:
            # Attempts to (re)connect to manticore server
            log_sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            logger.debug("Connecting to %s:%s", HOST, PORT)
            log_sock.connect((HOST, PORT))
            logger.info("Connected to %s:%s", HOST, PORT)

            read_sockets, write_sockets, error_sockets = select.select([log_sock], [], [], 60)

            serialized = b""
            if read_sockets:
                serialized = read_sockets[0].recv(10000)
                logger.info("Pulled {} bytes".format(len(serialized)))

                try:
                    m = MessageList()
                    m.ParseFromString(serialized)
                    logs.extend(m.messages)
                    logger.info("Deserialized LogMessage")

                except DecodeError:
                    logger.info("Unable to deserialize message, malformed response")

            read_sockets[0].shutdown(socket.SHUT_RDWR)

            log_sock.close()
        except socket.error:
            logger.warning("Log Socket disconnected")
            log_sock.close()

        try:
            # Attempts to (re)connect to manticore server
            state_sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            logger.debug("Connecting to %s:%s", HOST, PORT + 1)
            state_sock.connect((HOST, PORT + 1))
            logger.info("Connected to %s:%s", HOST, PORT + 1)

            read_sockets, write_sockets, error_sockets = select.select([state_sock], [], [], 60)

            serialized = b""
            if read_sockets:
                serialized = read_sockets[0].recv(10000)
                logger.info("Pulled {} bytes".format(len(serialized)))

                try:
                    m = StateList()
                    m.ParseFromString(serialized)

                    logger.info("Got %d states", len(m.states))

                    state_captures.append(m.states)

                except DecodeError:
                    logger.info("Unable to deserialize message, malformed response")

            state_sock.shutdown(socket.SHUT_RDWR)

            state_sock.close()
        except socket.error:
            logger.warning("State Socket disconnected")
            state_sock.close()

        time.sleep(0.5)


class TestTui(unittest.TestCase):
    def test_simple_state_updates(self):
        global finished

        fetch_thread = threading.Thread(target=fetch_update)
        fetch_thread.start()

        cmd = [
            PYTHON_BIN,
            "-m",
            "manticore",
            "-v",
            "--no-color",
            "--core.procs",
            str(10),
            "--core.seed",
            str(100),
            "--core.PORT",
            str(PORT),
            ms_file,
        ]

        self.assertEqual(subprocess.check_call(cmd), 0, "Manticore had a non-zero exit code")

        finished = True

        # Check that logs look right
        self.assertTrue(any("you got it!" in i.content for i in logs))
        self.assertTrue(any("Program finished with exit status: 0" in i.content for i in logs))
        self.assertEqual(
            sum(1 if "Program finished with exit status: 1" in i.content else 0 for i in logs), 17
        )

        # Check that state lists seem correct
        self.assertLessEqual(
            max(len(list(filter(lambda x: x.type == State.BUSY, i))) for i in state_captures), 10
        )  # At most ten running states

        self.assertEqual(
            min(len(list(filter(lambda x: x.type == State.BUSY, i))) for i in state_captures), 0
        )  # No running states at the end

        self.assertEqual(max(len(i) for i in state_captures), 18)  # Should have 18 states in total


if __name__ == "__main__":
    unittest.main()
