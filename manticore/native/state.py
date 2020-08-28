import copy
from collections import namedtuple
from typing import Any, Callable, Dict, NamedTuple, Optional, Set, Tuple, Union

from .cpu.disasm import Instruction
from .memory import ConcretizeMemory, MemoryException
from .. import issymbolic
from ..core.state import StateBase, Concretize, TerminateState
from ..core.smtlib import Expression


HookCallback = Callable[[StateBase], None]


class CheckpointData(NamedTuple):
    pc: Any
    last_pc: Any


class State(StateBase):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._hooks: Dict[Optional[int], Set[HookCallback]] = {}
        self._after_hooks: Dict[Optional[int], Set[HookCallback]] = {}

    def __getstate__(self) -> Dict[str, Any]:
        state = super().__getstate__()
        state["hooks"] = self._hooks
        state["after_hooks"] = self._after_hooks
        return state

    def __setstate__(self, state: Dict[str, Any]) -> None:
        super().__setstate__(state)
        self._hooks = state["hooks"]
        self._after_hooks = state["after_hooks"]
        self._resub_hooks()

    def __enter__(self) -> "State":
        new_state = super().__enter__()
        new_state._hooks = copy.copy(self._hooks)
        new_state._after_hooks = copy.copy(self._after_hooks)

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
        self, after: bool = True
    ) -> Tuple[Dict[Optional[int], Set[HookCallback]], str, Any]:
        """
        Internal helper function to get hook context information.

        :param after: Whether we want info pertaining to hooks after instruction executes or before
        :return: Information for hooks after or before:
            - set of hooks for specified after or before
            - string of callback event
            - State function that handles the callback
        """
        return (
            (self._hooks, "will_execute_instruction", self._state_hook_callback)
            if not after
            else (self._after_hooks, "did_execute_instruction", self._state_after_hook_callback)
        )

    def remove_hook(self, pc: Optional[int], callback: HookCallback, after: bool = False) -> bool:
        """
        Remove a callback with the specified properties
        :param pc: Address of instruction to remove from
        :param callback: The callback function that was at the address
        :param after: Whether it was after instruction executed or not
        :return: Whether it was removed
        """
        hooks, when, _ = self._get_hook_context(after)
        cbs = hooks.get(pc, set())
        if callback in cbs:
            cbs.remove(callback)
        else:
            return False

        if len(hooks.get(pc, set())) == 0:
            del hooks[pc]

        return True

    def add_hook(self, pc: Optional[int], callback: HookCallback, after: bool = False) -> None:
        """
        Add a callback to be invoked on executing a program counter. Pass `None`
        for pc to invoke callback on every instruction. `callback` should be a callable
        that takes one :class:`~manticore.native.state.State` argument.

        :param pc: Address of instruction to hook
        :param callback: Hook function
        :param after: Hook after PC executes?
        :param state: Add hook to this state
        """
        hooks, when, hook_callback = self._get_hook_context(after)
        hooks.setdefault(pc, set()).add(callback)
        if hooks:
            self.subscribe(when, hook_callback)

    def _resub_hooks(self) -> None:
        """
        Internal helper function to resubscribe hook callback events when the
        state is active again.
        """
        # TODO: check if the lists actually have hooks
        _, when, hook_callback = self._get_hook_context(False)
        self.subscribe(when, hook_callback)

        _, when, hook_callback = self._get_hook_context(True)
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
