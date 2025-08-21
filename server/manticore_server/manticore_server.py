import argparse
import dataclasses
import logging
import shutil
import time
import uuid
from collections import defaultdict
from concurrent import futures
from pathlib import Path
from threading import Event, Thread
from typing import Any, Callable, Dict, Optional, Set

import grpc
from grpc._server import _Context
from manticore.core.plugin import (
    InstructionCounter,
    RecordSymbolicBranches,
    StateDescriptor,
    Tracer,
    Visited,
)
from manticore.core.state import StateBase, TerminateState
from manticore.core.worker import WorkerProcess, WorkerThread
from manticore.ethereum import ManticoreEVM
from manticore.native import Manticore
from manticore.utils.enums import StateLists, StateStatus
from manticore.utils.helpers import deque
from manticore.utils.log import CallbackStream, ManticoreContextFilter

from .evm_utils import setup_detectors_flags
from .introspect_plugin import ManticoreServerIntrospectionPlugin
from .ManticoreServer_pb2 import *
from .ManticoreServer_pb2_grpc import (
    ManticoreServerServicer,
    add_ManticoreServerServicer_to_server,
)
from .native_plugin import UnicornEmulatePlugin
from .native_utils import parse_native_arguments

logger = logging.getLogger(__name__)


class ManticoreWrapper:
    def __init__(
        self, mcore_object: Manticore, thread_target: Callable, *thread_args: Any
    ):
        self.uuid: str = uuid.uuid4().hex
        self.manticore_object: Manticore = mcore_object
        # mimics Manticore repository, reasoning for the queue size difference is provided in Manticore:
        # https://github.com/trailofbits/manticore/blob/5a258f499098394c0af25e2e3f00b1b603c2334d/manticore/core/manticore.py#L133-L135
        self.log_queue = (
            mcore_object._manager.Queue(15000)
            if mcore_object._worker_type == WorkerProcess
            else deque(maxlen=5000)
        )

        # contains the state ids of all states paused by the user through the ControlState rpc
        self.paused_states: Set[int] = set()

        # saves a copy of all state descriptors after analysis is complete or terminated
        # but before the finalize() operation which destroys all states
        self.final_states: Optional[Dict[int, StateDescriptor]] = None

        self.state_callbacks: Dict[int, Set[Callable]] = defaultdict(set)

        self.thread: Thread = Thread(
            target=thread_target,
            args=(self,) + thread_args,
            daemon=True,
            name=self.uuid,
        )

    def start(self) -> None:
        self.thread.start()

    def append_log(self, msg: str) -> None:
        q = self.log_queue
        try:
            q.append(msg)
        except AttributeError:
            # mimics Manticore repository, reasoning for using append and catching an AttributeError is provided in Manticore:
            # https://github.com/trailofbits/manticore/blob/5a258f499098394c0af25e2e3f00b1b603c2334d/manticore/core/worker.py#L297-L303
            if q.full():
                q.get()
            q.put(msg)


class ManticoreServicer(ManticoreServerServicer):
    """Provides functionality for the methods set out in the protobuf spec"""

    def __init__(self, stop_event: Event):
        """Initializes the dict that keeps track of all created manticore instances, as well as avoid/find address set"""

        self.manticore_instances: Dict[str, ManticoreWrapper] = {}
        self.stop_event: Event = stop_event

        manticore_logger = logging.getLogger("manticore")
        manticore_logger.parent = None
        manticore_logger.setLevel(logging.WARNING)

        custom_log_handler = logging.StreamHandler(CallbackStream(self.log_callback))
        custom_log_handler.setFormatter(
            logging.Formatter(
                "%(threadName)s %(asctime)s: [%(process)d] %(name)s:%(levelname)s %(message)s"
            )
        )
        custom_log_handler.addFilter(ManticoreContextFilter())

        manticore_logger.addHandler(custom_log_handler)

    def log_callback(self, msg: str):
        logger.debug(msg)
        thread_name, msg_content = msg.split(" ", 1)

        if thread_name in self.manticore_instances:
            # This will always be True if multiprocessing or single is used, since all WorkerProcess/WorkerSingle
            # instances will share the same Thread name as the ManticoreWrapper's mthread which is added on Start
            self.manticore_instances[thread_name].append_log(msg_content)
        else:
            for mwrapper in filter(
                lambda x: x.manticore_object._worker_type == WorkerThread,
                list(self.manticore_instances.values())[::-1],
            ):  # Thread name/idents can be reused, so start search from most recently-started instance
                for worker in mwrapper.manticore_object._workers + list(
                    mwrapper.manticore_object._daemon_threads.values()
                ):
                    if type(worker._t) is Thread and worker._t.name == thread_name:
                        worker._t.name = mwrapper.uuid
                        mwrapper.append_log(msg_content)
                        return

    def StartNative(
        self, native_arguments: NativeArguments, context: _Context
    ) -> ManticoreInstance:
        """Starts a singular Manticore instance to analyze a native binary"""
        try:
            parsed = parse_native_arguments(native_arguments.additional_mcore_args)
        except Exception as e:
            logger.debug(e)
            context.set_code(grpc.StatusCode.INVALID_ARGUMENT)
            context.set_details("Additional arguments could not be parsed!")
            return ManticoreInstance()
        try:
            m = Manticore.linux(
                native_arguments.program_path,
                argv=None
                if not native_arguments.binary_args
                else list(native_arguments.binary_args),
                envp=None
                if not native_arguments.envp
                else {
                    key: val
                    for key, val in [e.split("=") for e in native_arguments.envp]
                },
                symbolic_files=None
                if not native_arguments.symbolic_files
                else list(native_arguments.symbolic_files),
                concrete_start=""
                if not native_arguments.concrete_start
                else native_arguments.concrete_start,
                stdin_size=265
                if not native_arguments.stdin_size
                else int(native_arguments.stdin_size),
                workspace_url=parsed.workspace,
                introspection_plugin_type=ManticoreServerIntrospectionPlugin,
            )
        except Exception as e:
            logger.warning(e)
            context.set_code(grpc.StatusCode.INVALID_ARGUMENT)
            context.set_details("Basic arguments are invalid!")
            return ManticoreInstance()

        try:
            m.register_plugin(InstructionCounter())
            m.register_plugin(Visited(parsed.coverage))
            m.register_plugin(Tracer())
            m.register_plugin(RecordSymbolicBranches())

            if native_arguments.emulate_until:
                m.register_plugin(UnicornEmulatePlugin(native_arguments.emulate_until))

            if parsed.names is not None:
                m.apply_model_hooks(parsed.names)

            if parsed.assertions:
                m.load_assertions(parsed.assertions)

            def find_f(state: StateBase):
                bufs = state.solve_one_n_batched(state.input_symbols)
                for symbol, buf in zip(state.input_symbols, bufs):
                    logger.info(f"{symbol.name}: {buf!r}\n")
                with m.locked_context() as context:
                    m.kill()
                state.abandon()

            def avoid_f(state: StateBase):
                state.abandon()

            for hook in native_arguments.hooks:
                if hook.type == Hook.HookType.FIND:
                    m.add_hook(hook.address, find_f)
                elif hook.type == Hook.HookType.AVOID:
                    m.add_hook(hook.address, avoid_f)
                elif hook.type == Hook.HookType.CUSTOM:
                    exec(hook.func_text, {"addr": hook.address, "m": m})
                elif hook.type == Hook.HookType.GLOBAL:
                    exec(hook.func_text, {"m": m})

        except Exception as e:
            logger.warning(e)
            context.set_code(grpc.StatusCode.INVALID_ARGUMENT)
            context.set_details("Hooks set are invalid!")
            return ManticoreInstance()

        try:

            def manticore_native_runner(mcore_wrapper: ManticoreWrapper):
                mcore_wrapper.manticore_object.run()
                mcore_wrapper.final_states = {
                    k: dataclasses.replace(v)
                    for k, v in mcore_wrapper.manticore_object.introspect().items()
                }
                mcore_wrapper.manticore_object.finalize()

            manticore_wrapper = ManticoreWrapper(m, manticore_native_runner)
            self.manticore_instances[manticore_wrapper.uuid] = manticore_wrapper

            def state_callback_hook(state: StateBase):
                callbacks = manticore_wrapper.state_callbacks[state.id]
                for callback in callbacks:
                    callback(state)

            m.hook(None)(state_callback_hook)

            manticore_wrapper.start()

        except Exception as e:
            logger.warning(e)
            context.set_code(grpc.StatusCode.INTERNAL)
            context.set_details(
                "Manticore failed to start or crashed during execution!"
            )
            return ManticoreInstance()

        return ManticoreInstance(uuid=manticore_wrapper.uuid)

    def StartEVM(
        self, evm_arguments: EVMArguments, context: _Context
    ) -> ManticoreInstance:
        """Starts a singular Manticore instance to analyze a solidity contract"""
        if evm_arguments.contract_path == "":
            context.set_code(grpc.StatusCode.INVALID_ARGUMENT)
            context.set_details("Contract path not specified!")
            return ManticoreInstance()
        if not Path(evm_arguments.contract_path).is_file():
            context.set_code(grpc.StatusCode.INVALID_ARGUMENT)
            context.set_details(
                f"Contract path invalid: '{evm_arguments.contract_path}'"
            )
            return ManticoreInstance()

        if evm_arguments.solc_bin:
            solc_bin_path = evm_arguments.solc_bin
        elif shutil.which("solc"):
            solc_bin_path = str(shutil.which("solc"))
        else:
            context.set_code(grpc.StatusCode.INVALID_ARGUMENT)
            context.set_details(
                "solc binary neither specified in EVMArguments nor found in PATH!"
            )
            return ManticoreInstance()

        try:
            m = ManticoreEVM()

            args = setup_detectors_flags(
                list(evm_arguments.detectors_to_exclude),
                evm_arguments.additional_flags,
                m,
            )

            def manticore_evm_runner(
                mcore_wrapper: ManticoreWrapper, args: argparse.Namespace
            ):
                mcore_wrapper.manticore_object.multi_tx_analysis(
                    evm_arguments.contract_path,
                    contract_name=evm_arguments.contract_name,
                    tx_limit=-1
                    if not evm_arguments.tx_limit
                    else evm_arguments.tx_limit,
                    tx_use_coverage=True
                    if args.txnocoverage == None
                    else args.txnocoverage,
                    tx_send_ether=True if args.txnoether == None else args.txnoether,
                    tx_account="attacker"
                    if not evm_arguments.tx_account
                    else evm_arguments.tx_account,
                    tx_preconstrain=False
                    if args.txpreconstrain == None
                    else args.txpreconstrain,
                    compile_args={"solc_solcs_bin": solc_bin_path},
                )

                mcore_wrapper.final_states = {
                    k: dataclasses.replace(v)
                    for k, v in mcore_wrapper.manticore_object.introspect().items()
                }

                if not args.no_testcases:
                    mcore_wrapper.manticore_object.finalize(
                        only_alive_states=args.only_alive_testcases
                    )
                else:
                    mcore_wrapper.manticore_object.kill()

            manticore_wrapper = ManticoreWrapper(m, manticore_evm_runner, args)
            self.manticore_instances[manticore_wrapper.uuid] = manticore_wrapper
            manticore_wrapper.start()

        except Exception as e:
            logger.warning(e)
            context.set_code(grpc.StatusCode.INTERNAL)
            context.set_details(
                "Manticore failed to start or crashed during execution!"
            )
            return ManticoreInstance()

        return ManticoreInstance(uuid=manticore_wrapper.uuid)

    def Terminate(
        self, mcore_instance: ManticoreInstance, context: _Context
    ) -> TerminateResponse:
        """Terminates the specified Manticore instance."""
        if mcore_instance.uuid not in self.manticore_instances:
            context.set_code(grpc.StatusCode.FAILED_PRECONDITION)
            context.set_details("Specified Manticore instance not found!")
            return TerminateResponse()

        m_wrapper = self.manticore_instances[mcore_instance.uuid]

        if not (
            m_wrapper.manticore_object.is_running() and m_wrapper.thread.is_alive()
        ):
            return TerminateResponse()
        m_wrapper.manticore_object.kill()
        return TerminateResponse()

    def GetStateList(
        self, mcore_instance: ManticoreInstance, context: _Context
    ) -> ManticoreStateList:
        """Returns full list of states for given ManticoreInstance."""
        active_states = []
        waiting_states = []
        paused_states = []
        forked_states = []
        errored_states = []
        complete_states = []

        if mcore_instance.uuid not in self.manticore_instances:
            context.set_code(grpc.StatusCode.FAILED_PRECONDITION)
            context.set_details("Specified Manticore instance not found!")
            return ManticoreStateList()

        mcore_wrapper = self.manticore_instances[mcore_instance.uuid]
        states = (
            mcore_wrapper.final_states
            if mcore_wrapper.final_states is not None
            else mcore_wrapper.manticore_object.introspect()
        )

        for state_id, state_desc in states.items():
            # Build ManticoreState with explicit arguments
            pc = None
            if isinstance(state_desc.pc, int):
                pc = state_desc.pc
            elif isinstance(state_desc.last_pc, int):
                pc = state_desc.last_pc

            parent_id = None
            if isinstance(state_desc.parent, int):
                parent_id = state_desc.parent

            children_ids = list(state_desc.children)

            # Create ManticoreState with explicit keyword arguments
            if pc is not None:
                s = ManticoreState(
                    state_id=state_id,
                    pc=pc,
                    parent_id=parent_id,
                    children_ids=children_ids
                )
            else:
                # If pc is None, only pass required arguments
                s = ManticoreState(
                    state_id=state_id,
                    parent_id=parent_id,
                    children_ids=children_ids
                )

            if state_desc.status == StateStatus.running:
                active_states.append(s)
            elif state_desc.status in (
                StateStatus.waiting_for_solver,
                StateStatus.waiting_for_worker,
            ):
                waiting_states.append(s)
            elif state_desc.status == StateStatus.destroyed:
                forked_states.append(s)
            elif state_desc.status == StateStatus.stopped:
                if state_id in mcore_wrapper.paused_states:
                    paused_states.append(s)
                elif state_desc.state_list == StateLists.killed:
                    errored_states.append(s)
                else:
                    complete_states.append(s)
            else:
                raise ValueError(f"Unknown status {state_desc.status}")

        return ManticoreStateList(
            active_states=active_states,
            waiting_states=waiting_states,
            paused_states=paused_states,
            forked_states=forked_states,
            errored_states=errored_states,
            complete_states=complete_states,
        )

    def GetMessageList(
        self, mcore_instance: ManticoreInstance, context: _Context
    ) -> ManticoreMessageList:
        """Returns any new log messages for given ManticoreInstance since the previous call.
        Currently, implementation is based on TUI."""
        if mcore_instance.uuid not in self.manticore_instances:
            context.set_code(grpc.StatusCode.FAILED_PRECONDITION)
            context.set_details("Specified Manticore instance not found!")
            return ManticoreMessageList()

        q = self.manticore_instances[mcore_instance.uuid].log_queue
        i = 0
        messages = []
        while not q.empty():
            msg = ManticoreLogMessage(content=q.get())
            messages.append(msg)
            i += 1
        return ManticoreMessageList(messages=messages)

    def CheckManticoreRunning(
        self, mcore_instance: ManticoreInstance, context: _Context
    ) -> ManticoreRunningStatus:
        if mcore_instance.uuid not in self.manticore_instances:
            context.set_code(grpc.StatusCode.FAILED_PRECONDITION)
            context.set_details("Specified Manticore instance not found!")
            return ManticoreRunningStatus()

        m_wrapper = self.manticore_instances[mcore_instance.uuid]

        return ManticoreRunningStatus(is_running=(m_wrapper.thread.is_alive()))

    def StopServer(
        self, request: StopServerRequest, context: _Context
    ) -> StopServerResponse:
        to_warn = False
        for mwrapper in self.manticore_instances.values():
            mwrapper.manticore_object.kill()
            stime = time.time()
            while mwrapper.thread.is_alive():
                time.sleep(1)
                if (time.time() - stime) > 10:
                    to_warn = True
                    break

        if to_warn:
            warning_message = "WARNING: Not all Manticore processes were shut down successfully before timeout. There may be extra processes running even after the server has stopped."
            context.set_code(grpc.StatusCode.INTERNAL)
            context.set_details(warning_message)
            logger.warning(warning_message)

        self.stop_event.set()
        return StopServerResponse()

    def ControlState(
        self, request: ControlStateRequest, context: _Context
    ) -> ControlStateResponse:
        if request.manticore_instance.uuid not in self.manticore_instances:
            context.set_code(grpc.StatusCode.FAILED_PRECONDITION)
            context.set_details("Specified Manticore instance not found!")
            return ControlStateResponse()

        mcore_wrapper = self.manticore_instances[request.manticore_instance.uuid]
        mcore_object = mcore_wrapper.manticore_object
        states = (
            mcore_wrapper.final_states
            if mcore_wrapper.final_states is not None
            else mcore_object.introspect()
        )

        if request.state_id not in states:
            context.set_code(grpc.StatusCode.FAILED_PRECONDITION)
            context.set_details("Specified state not found!")
            return ControlStateResponse()

        # Pause / Resume / Kill should have no effect if Manticore is no longer running,
        # but we do not raise an error to account for latency between CheckStatus() calls
        if not mcore_object.is_running():
            return ControlStateResponse()

        # helper callbacks for state control
        def state_pause_hook(state: StateBase) -> None:
            mcore_wrapper.state_callbacks[state.id].discard(state_pause_hook)
            raise TerminateState("Pausing state")

        def state_kill_hook(state: StateBase) -> None:
            mcore_wrapper.state_callbacks[state.id].discard(state_kill_hook)
            state.abandon()

        try:
            if request.action == ControlStateRequest.StateAction.PAUSE:
                if len(mcore_wrapper.paused_states) == 0:
                    with mcore_object._lock:
                        mcore_object._busy_states.append(-1)
                        mcore_object._lock.notify_all()
                mcore_wrapper.state_callbacks[request.state_id].add(state_pause_hook)
                mcore_wrapper.paused_states.add(request.state_id)

            elif request.action == ControlStateRequest.StateAction.RESUME:
                mcore_wrapper.paused_states.discard(request.state_id)
                with mcore_object._lock:
                    mcore_object._revive_state(request.state_id)
                    if len(mcore_wrapper.paused_states) == 0:
                        mcore_object._busy_states.remove(-1)
                    mcore_object._lock.notify_all()

            elif request.action == ControlStateRequest.StateAction.KILL:
                if request.state_id in mcore_wrapper.paused_states:
                    mcore_wrapper.paused_states.remove(request.state_id)
                    if len(mcore_wrapper.paused_states) == 0:
                        with mcore_object._lock:
                            mcore_object._busy_states.remove(-1)
                            mcore_object._lock.notify_all()
                else:
                    mcore_wrapper.state_callbacks[request.state_id].add(state_kill_hook)
        except:
            context.set_code(grpc.StatusCode.INTERNAL)
            context.set_details(
                f"Failed apply action {request.action} to state {request.state_id}"
            )

        return ControlStateResponse()


def main():
    logger.setLevel(logging.DEBUG)
    port = "[::]:50010"
    logger.info(f"server starting at '{port}' ...")
    stop_event = Event()
    server = grpc.server(futures.ThreadPoolExecutor(max_workers=10))
    add_ManticoreServerServicer_to_server(ManticoreServicer(stop_event), server)
    server.add_insecure_port(port)
    server.start()
    logger.info("server started.")
    stop_event.wait()
    server.stop(None)
    logger.info("shutdown gracefully!")
