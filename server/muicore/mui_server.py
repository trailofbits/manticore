from concurrent import futures
from threading import Thread
import argparse
from pathlib import Path

import grpc
from grpc._server import _Context
from .MUICore_pb2 import *
from .MUICore_pb2_grpc import ManticoreUIServicer, add_ManticoreUIServicer_to_server
from .introspect_plugin import MUIIntrospectionPlugin

from manticore.core.state import StateBase
from manticore.native import Manticore
from manticore.ethereum import ManticoreEVM
from manticore.core.plugin import (
    InstructionCounter,
    Visited,
    Tracer,
    RecordSymbolicBranches,
)

from manticore.utils.enums import StateStatus, StateLists

import uuid
import shutil
from inspect import currentframe, getframeinfo

from .native_utils import parse_native_arguments
from .evm_utils import setup_detectors_flags


class MUIServicer(ManticoreUIServicer):
    """Provides functionality for the methods set out in the protobuf spec"""

    def __init__(self):
        """Initializes the dict that keeps track of all created manticore instances, as well as avoid/find address set"""

        self.manticore_instances = {}
        self.avoid = set()
        self.find = set()

    def StartNative(
        self, native_arguments: NativeArguments, context: _Context
    ) -> ManticoreInstance:
        """Starts a singular Manticore instance to analyze a native binary"""
        id = uuid.uuid4().hex
        try:

            parsed = parse_native_arguments(native_arguments.additional_mcore_args)
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
                introspection_plugin_type=MUIIntrospectionPlugin,
            )

            m.register_plugin(InstructionCounter())
            m.register_plugin(Visited(parsed.coverage))
            m.register_plugin(Tracer())
            m.register_plugin(RecordSymbolicBranches())

            if parsed.names is not None:
                m.apply_model_hooks(parsed.names)

            if parsed.assertions:
                m.load_assertions(parsed.assertions)

            def avoid_f(state: StateBase):
                state.abandon()

            for addr in self.avoid:
                m.add_hook(addr, avoid_f)

            def find_f(state: StateBase):
                bufs = state.solve_one_n_batched(state.input_symbols)
                for symbol, buf in zip(state.input_symbols, bufs):
                    print(f"{symbol.name}: {buf!r}\n")
                with m.locked_context() as context:
                    m.kill()
                state.abandon()

            for addr in self.find:
                m.add_hook(addr, find_f)

            def manticore_native_runner(mcore: Manticore):
                mcore.run()
                mcore.finalize()

            mthread = Thread(target=manticore_native_runner, args=(m,), daemon=True)
            mthread.start()
            self.manticore_instances[id] = (m, mthread)

        except Exception as e:
            print(e)
            raise e
            return ManticoreInstance()

        return ManticoreInstance(uuid=id)

    def StartEVM(
        self, evm_arguments: EVMArguments, context: _Context
    ) -> ManticoreInstance:
        """Starts a singular Manticore instance to analyze a solidity contract"""

        if evm_arguments.contract_path == "":
            raise FileNotFoundError("Contract path not specified!")
        if not Path(evm_arguments.contract_path).is_file():
            raise FileNotFoundError(
                f"Contract path invalid: '{evm_arguments.contract_path}'"
            )

        if evm_arguments.solc_bin:
            solc_bin_path = evm_arguments.solc_bin
        elif shutil.which("solc"):
            solc_bin_path = shutil.which("solc")
        else:
            raise Exception(
                "solc binary neither specified in EVMArguments nor found in PATH!"
            )

        id = uuid.uuid4().hex
        try:
            m = ManticoreEVM()

            args = setup_detectors_flags(
                evm_arguments.detectors_to_exclude, evm_arguments.additional_flags, m
            )

            def manticore_evm_runner(m: ManticoreEVM, args: argparse.Namespace):

                m.multi_tx_analysis(
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

                if not args.no_testcases:
                    m.finalize(only_alive_states=args.only_alive_testcases)
                else:
                    m.kill()

            mthread = Thread(target=manticore_evm_runner, args=(m, args), daemon=True)
            mthread.start()
            self.manticore_instances[id] = (m, mthread)

        except Exception as e:
            print(e)
            raise e
            return ManticoreInstance()

        return ManticoreInstance(uuid=id)

    def Terminate(
        self, mcore_instance: ManticoreInstance, context: _Context
    ) -> TerminateResponse:
        """Terminates the specified Manticore instance."""
        if mcore_instance.uuid not in self.manticore_instances:
            return TerminateResponse(success=False)

        m, mthread = self.manticore_instances[mcore_instance.uuid]

        if not (m.is_running() and mthread.is_alive()):
            return TerminateResponse(success=True)
        m.kill()
        return TerminateResponse(success=True)

    def TargetAddressNative(
        self, address_request: AddressRequest, context: _Context
    ) -> TargetResponse:
        """Sets addresses in the binary to find/avoid, or clears address status.
        Values set will be used for subsequent Start calls.
        Currently, implementation is based on MUI's Binary Ninja plugin."""

        if address_request.type == AddressRequest.TargetType.FIND:
            self.find.add(address_request.address)
        elif address_request.type == AddressRequest.TargetType.AVOID:
            self.avoid.add(address_request.address)
        elif address_request.type == AddressRequest.TargetType.CLEAR:
            self.avoid.remove(address_request.address)
            self.find.remove(address_request.address)
        return TargetResponse(success=True)

    def GetStateList(
        self, mcore_instance: ManticoreInstance, context: _Context
    ) -> MUIStateList:
        """Returns full list of states for given ManticoreInstance.
        Currently, implementation is based on MUI's Binary Ninja plugin."""
        active_states = []
        waiting_states = []
        forked_states = []
        errored_states = []
        complete_states = []
        if mcore_instance.uuid not in self.manticore_instances:
            return MUIStateList()

        m = self.manticore_instances[mcore_instance.uuid][0]
        states = m.introspect()

        for state_id, state_desc in states.items():
            s = MUIState(state_id=state_id)
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
                if state_desc.state_list == StateLists.killed:
                    errored_states.append(s)
                else:
                    complete_states.append(s)
            else:
                raise ValueError(f"Unknown status {state_desc.status}")

        return MUIStateList(
            active_states=active_states,
            waiting_states=waiting_states,
            forked_states=forked_states,
            errored_states=errored_states,
            complete_states=complete_states,
        )

    def GetMessageList(
        self, mcore_instance: ManticoreInstance, context: _Context
    ) -> MUIMessageList:
        """Returns any new log messages for given ManticoreInstance since the previous call.
        Currently, implementation is based on TUI."""
        if mcore_instance.uuid not in self.manticore_instances:
            return MUIMessageList(
                messages=[MUILogMessage(content="Manticore instance not found!")]
            )
        m = self.manticore_instances[mcore_instance.uuid][0]
        q = m._log_queue
        i = 0
        messages = []
        while i < 50 and not q.empty():
            msg = MUILogMessage(content=q.get())
            messages.append(msg)
            i += 1
        return MUIMessageList(messages=messages)

    def CheckManticoreRunning(
        self, mcore_instance: ManticoreInstance, context: _Context
    ) -> ManticoreRunningStatus:

        if mcore_instance.uuid not in self.manticore_instances:
            return ManticoreRunningStatus(is_running=False)

        m, mthread = self.manticore_instances[mcore_instance.uuid]

        return ManticoreRunningStatus(
            is_running=(m.is_running() and mthread.is_alive())
        )


def main():
    server = grpc.server(futures.ThreadPoolExecutor(max_workers=10))
    add_ManticoreUIServicer_to_server(MUIServicer(), server)
    server.add_insecure_port("[::]:50010")
    server.start()
    server.wait_for_termination()


if __name__ == "__main__":
    main()
