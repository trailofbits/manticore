import copy
import logging
from collections import namedtuple
from typing import Any, Callable, Dict, NamedTuple, Optional, Set, Tuple, Union

from .cpu.disasm import Instruction
from .memory import ConcretizeMemory, MemoryException
from .. import issymbolic
from ..core.state import StateBase, Concretize, TerminateState
from ..core.smtlib import Expression
from ..platforms import linux_syscalls


HookCallback = Callable[[StateBase], None]
logger = logging.getLogger(__name__)


class CheckpointData(NamedTuple):
    pc: Any
    last_pc: Any


class State(StateBase):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._hooks: Dict[Optional[int], Set[HookCallback]] = {}
        self._after_hooks: Dict[Optional[int], Set[HookCallback]] = {}
        self._sys_hooks: Dict[Optional[int], Set[HookCallback]] = {}
        self._sys_after_hooks: Dict[Optional[int], Set[HookCallback]] = {}

    def __getstate__(self) -> Dict[str, Any]:
        state = super().__getstate__()
        state["hooks"] = self._hooks
        state["after_hooks"] = self._after_hooks
        state["sys_hooks"] = self._sys_hooks
        state["sys_after_hooks"] = self._sys_after_hooks
        return state

    def __setstate__(self, state: Dict[str, Any]) -> None:
        super().__setstate__(state)
        self._hooks = state["hooks"]
        self._after_hooks = state["after_hooks"]
        self._sys_hooks = state["sys_hooks"]
        self._sys_after_hooks = state["sys_after_hooks"]
        self._resub_hooks()

    def __enter__(self) -> "State":
        new_state = super().__enter__()
        new_state._hooks = copy.copy(self._hooks)
        new_state._after_hooks = copy.copy(self._after_hooks)
        new_state._sys_hooks = copy.copy(self._sys_hooks)
        new_state._sys_after_hooks = copy.copy(self._sys_after_hooks)

        # Update constraint pointers in platform objects
        from ..platforms.linux import SLinux

        if isinstance(new_state.platform, SLinux):
            from ..platforms.linux import SymbolicSocket

            # Add constraints to symbolic sockets
            for fd_entry in new_state.platform.fd_table.entries():
                symb_socket_entry = fd_entry.fdlike
                if isinstance(symb_socket_entry, SymbolicSocket):
                    symb_socket_entry._constraints = new_state.constraints

        return new_state

    def _get_hook_context(
        self, after: bool = True, syscall: bool = False
    ) -> Tuple[Dict[Optional[int], Set[HookCallback]], str, Any]:
        """
        Internal helper function to get hook context information.

        :param after: Whether we want info pertaining to hooks after instruction executes or before
        :param syscall: Catch a syscall invocation instead of instruction?
        :return: Information for hooks after or before:
            - set of hooks for specified after or before
            - string of callback event
            - State function that handles the callback
        """
        if not syscall:
            return (
                (self._hooks, "will_execute_instruction", self._state_hook_callback)
                if not after
                else (self._after_hooks, "did_execute_instruction", self._state_after_hook_callback)
            )
        else:
            return (
                (self._sys_hooks, "will_invoke_syscall", self._state_sys_hook_callback)
                if not after
                else (
                    self._sys_after_hooks,
                    "did_invoke_syscall",
                    self._state_sys_after_hook_callback,
                )
            )

    def remove_hook(
        self,
        pc_or_sys: Optional[Union[int, str]],
        callback: HookCallback,
        after: bool = False,
        syscall: bool = False,
    ) -> bool:
        """
        Remove a callback with the specified properties
        :param pc_or_sys: Address of instruction, syscall number, or syscall name to remove hook from
        :type pc_or_sys: int or None if `syscall` = False. int, str, or None if `syscall` = True
        :param callback: The callback function that was at the address (or syscall)
        :param after: Whether it was after instruction executed or not
        :param syscall: Catch a syscall invocation instead of instruction?
        :return: Whether it was removed
        """

        if isinstance(pc_or_sys, str):
            table = getattr(linux_syscalls, self._platform.current.machine)
            for index, name in table.items():
                if name == pc_or_sys:
                    pc_or_sys = index
                    break
            if isinstance(pc_or_sys, str):
                logger.warning(
                    f"{pc_or_sys} is not a valid syscall name in architecture {self._platform.current.machine}. "
                    "Please refer to manticore/platforms/linux_syscalls.py to find the correct name."
                )
                return False

        hooks, when, _ = self._get_hook_context(after, syscall)
        cbs = hooks.get(pc_or_sys, set())
        if callback in cbs:
            cbs.remove(callback)
        else:
            return False

        if not len(hooks.get(pc_or_sys, set())):
            del hooks[pc_or_sys]

        return True

    def add_hook(
        self,
        pc_or_sys: Optional[Union[int, str]],
        callback: HookCallback,
        after: bool = False,
        syscall: bool = False,
    ) -> None:
        """
        Add a callback to be invoked on executing a program counter (or syscall). Pass `None`
        for `pc_or_sys` to invoke callback on every instruction (or syscall invocation).
        `callback` should be a callable that takes one :class:`~manticore.native.state.State` argument.

        :param pc_or_sys: Address of instruction to hook, syscall number, or syscall name
        :type pc_or_sys: int or None if `syscall` = False. int, str, or None if `syscall` = True
        :param callback: Hook function
        :param after: Hook after PC (or after syscall) executes?
        :param syscall: Catch a syscall invocation instead of instruction?
        """

        if isinstance(pc_or_sys, str):
            table = getattr(linux_syscalls, self._platform.current.machine)
            for index, name in table.items():
                if name == pc_or_sys:
                    pc_or_sys = index
                    break
            if isinstance(pc_or_sys, str):
                logger.warning(
                    f"{pc_or_sys} is not a valid syscall name in architecture {self._platform.current.machine}. "
                    "Please refer to manticore/platforms/linux_syscalls.py to find the correct name."
                )
                return

        hooks, when, hook_callback = self._get_hook_context(after, syscall)
        hooks.setdefault(pc_or_sys, set()).add(callback)
        if hooks:
            self.subscribe(when, hook_callback)

    def _resub_hooks(self) -> None:
        """
        Internal helper function to resubscribe hook callback events when the
        state is active again.
        """
        # TODO: check if the lists actually have hooks
        _, when, hook_callback = self._get_hook_context(False, False)
        self.subscribe(when, hook_callback)

        _, when, hook_callback = self._get_hook_context(True, False)
        self.subscribe(when, hook_callback)

        _, when, hook_callback = self._get_hook_context(False, True)
        self.subscribe(when, hook_callback)

        _, when, hook_callback = self._get_hook_context(True, True)
        self.subscribe(when, hook_callback)

    def _state_hook_callback(self, pc: int, _instruction: Instruction) -> None:
        """
        Invoke all registered State hooks before the instruction executes.

        :param pc: Address where the hook should run
        :param _instruction: Instruction at this PC
        """
        # Prevent crash if removing hook(s) during a callback
        tmp_hooks = copy.deepcopy(self._hooks)

        # Invoke all pc-specific hooks
        for cb in tmp_hooks.get(pc, []):
            cb(self)

        # Invoke all pc-agnostic hooks
        for cb in tmp_hooks.get(None, []):
            cb(self)

    def _state_after_hook_callback(self, last_pc: int, _pc: int, _instruction: Instruction):
        """
        Invoke all registered State hooks after the instruction executes.

        :param last_pc: Address where the hook should run after instruction execution
        :param _pc: Next address to execute
        :param _instruction: Instruction at this last_pc
        """
        # Prevent crash if removing hook(s) during a callback
        tmp_hooks = copy.deepcopy(self._after_hooks)
        # Invoke all pc-specific hooks
        for cb in tmp_hooks.get(last_pc, []):
            cb(self)

        # Invoke all pc-agnostic hooks
        for cb in tmp_hooks.get(None, []):
            cb(self)

    def _state_sys_hook_callback(self, syscall_num: int) -> None:
        """
        Invoke all registered State hooks before the syscall executes.

        :param syscall_num: index of the syscall about to be executed
        """
        # Prevent crash if removing hook(s) during a callback
        tmp_hooks = copy.deepcopy(self._sys_hooks)

        # Invoke all syscall-specific hooks
        for cb in tmp_hooks.get(syscall_num, []):
            cb(self)

        # Invoke all syscall-agnostic hooks
        for cb in tmp_hooks.get(None, []):
            cb(self)

    def _state_sys_after_hook_callback(self, syscall_num: int):
        """
        Invoke all registered State hooks after the syscall executes.

        :param syscall_num: index of the syscall that was just executed
        """
        # Prevent crash if removing hook(s) during a callback
        tmp_hooks = copy.deepcopy(self._sys_after_hooks)

        # Invoke all syscall-specific hooks
        for cb in tmp_hooks.get(syscall_num, []):
            cb(self)

        # Invoke all syscall-agnostic hooks
        for cb in tmp_hooks.get(None, []):
            cb(self)

    @property
    def cpu(self):
        """
        Current cpu state
        """
        return self._platform.current

    @property
    def mem(self):
        """
        Current virtual memory mappings
        """
        return self._platform.current.memory

    def _rollback(self, checkpoint_data: CheckpointData) -> None:
        """
        Rollback state to previous values in checkpoint_data
        """
        # Keep in this form to make sure we don't miss restoring any newly added
        # data. Make sure the order is correct
        self.cpu.PC, self.cpu._last_pc = checkpoint_data

    def execute(self):
        """
        Perform a single step on the current state
        """
        super().execute()
        from .cpu.abstractcpu import (
            ConcretizeRegister,
        )  # must be here, otherwise we get circular imports

        checkpoint_data = CheckpointData(pc=self.cpu.PC, last_pc=self.cpu._last_pc)
        try:
            result = self._platform.execute()

        # Instead of State importing SymbolicRegisterException and SymbolicMemoryException
        # from cpu/memory shouldn't we import Concretize from linux, cpu, memory ??
        # We are forcing State to have abstractcpu
        except ConcretizeRegister as exc:
            # Need to define local variable to use in closure
            e = exc
            expression = self.cpu.read_register(e.reg_name)

            def setstate(state: State, value):
                state.cpu.write_register(e.reg_name, value)

            self._rollback(checkpoint_data)
            raise Concretize(str(e), expression=expression, setstate=setstate, policy=e.policy)
        except ConcretizeMemory as exc:
            # Need to define local variable to use in closure
            e = exc
            expression = self.cpu.read_int(e.address, e.size)

            def setstate(state: State, value):
                state.cpu.write_int(e.address, value, e.size)

            self._rollback(checkpoint_data)
            raise Concretize(str(e), expression=expression, setstate=setstate, policy=e.policy)
        except Concretize as e:
            self._rollback(checkpoint_data)
            raise e
        except MemoryException as e:
            raise TerminateState(str(e), testcase=True)

        # Remove when code gets stable?
        assert self.platform.constraints is self.constraints

        return result

    def invoke_model(self, model):
        """
        Invokes a `model`. Modelling can be used to override a function in the target program with a custom
        implementation.

        For more information on modelling see docs/models.rst

        A `model` is a callable whose first argument is a `manticore.native.State` instance.
        If the following arguments correspond to the arguments of the C function
        being modeled. If the `model` models a variadic function, the following argument
        is a generator object, which can be used to access function arguments dynamically.
        The `model` callable should simply return the value that should be returned by the
        native function being modeled.f

        :param model: callable, model to invoke
        """
        self._platform.invoke_model(model, prefix_args=(self,))

    def _update_state_descriptor(self, descriptor, *args, **kwargs):
        """
        Called on execution_intermittent to update the descriptor for this state.
        This one should apply any native-specific information to the descriptor. Right now, that's just the PC

        :param descriptor: StateDescriptor for this state
        """
        super()._update_state_descriptor(descriptor, *args, **kwargs)
        descriptor.pc = self.cpu.PC
