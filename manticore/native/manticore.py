import logging
import types

import elftools
import os
import shlex
import time
import sys
from elftools.elf.elffile import ELFFile
from elftools.elf.sections import SymbolTableSection

from .state import State
from ..core.manticore import ManticoreBase
from ..core.smtlib import ConstraintSet
from ..core.smtlib.solver import SelectedSolver, issymbolic
from ..exceptions import ManticoreError
from ..utils import log, config

logger = logging.getLogger(__name__)

consts = config.get_group("native")
consts.add("stdin_size", default=256, description="Maximum symbolic stdin size")


class Manticore(ManticoreBase):
    def generate_testcase(self, state, message="test"):
        testcase = super().generate_testcase(state, message)
        self._output.save_testcase(state, testcase, message)

    def __init__(self, path_or_state, argv=None, workspace_url=None, policy="random", **kwargs):
        """
        :param path_or_state: Path to binary or a state (object) to begin from.
        :param argv: arguments passed to the binary.
        """
        if isinstance(path_or_state, str):
            if not os.path.isfile(path_or_state):
                raise OSError(f"{path_or_state} is not an existing regular file")
            initial_state = _make_initial_state(path_or_state, argv=argv, **kwargs)
        else:
            initial_state = path_or_state

        super().__init__(initial_state, workspace_url=workspace_url, policy=policy, **kwargs)

        # Move the following into a linux plugin
        self._assertions = {}
        self.trace = None
        # sugar for 'will_execute_instruction"
        self._hooks = {}
        self._after_hooks = {}
        self._init_hooks = set()

        # self.subscribe('will_generate_testcase', self._generate_testcase_callback)

    ############################################################################
    # Model hooks + callback
    ############################################################################

    def apply_model_hooks(self, path):
        # TODO(yan): Simplify the partial function application

        # Imported straight from __main__.py; this will be re-written once the new
        # event code is in place.
        import importlib
        from manticore import platforms

        with open(path, "r") as fnames:
            for line in fnames.readlines():
                address, cc_name, name = line.strip().split(" ")
                fmodel = platforms
                name_parts = name.split(".")
                importlib.import_module(f".platforms.{name_parts[0]}", "manticore")
                for n in name_parts:
                    fmodel = getattr(fmodel, n)
                assert fmodel != platforms

                def cb_function(state):
                    state.platform.invoke_model(fmodel, prefix_args=(state.platform,))

                self._model_hooks.setdefault(int(address, 0), set()).add(cb_function)
                self._executor.subscribe("will_execute_instruction", self._model_hook_callback)

    def _model_hook_callback(self, state, instruction):
        pc = state.cpu.PC
        if pc not in self._model_hooks:
            return

        for cb in self._model_hooks[pc]:
            cb(state)

    def _generate_testcase_callback(self, state, testcase, message):
        self._output.save_testcase(state, testcase, message)

    @classmethod
    def linux(
        cls,
        path,
        argv=None,
        envp=None,
        entry_symbol=None,
        symbolic_files=None,
        concrete_start="",
        pure_symbolic=False,
        stdin_size=None,
        **kwargs,
    ):
        """
        Constructor for Linux binary analysis.

        :param str path: Path to binary to analyze
        :param argv: Arguments to provide to the binary
        :type argv: list[str]
        :param envp: Environment to provide to the binary
        :type envp: dict[str, str]
        :param entry_symbol: Entry symbol to resolve to start execution
        :type envp: str
        :param symbolic_files: Filenames to mark as having symbolic input
        :type symbolic_files: list[str]
        :param str concrete_start: Concrete stdin to use before symbolic input
        :param int stdin_size: symbolic stdin size to use
        :param kwargs: Forwarded to the Manticore constructor
        :return: Manticore instance, initialized with a Linux State
        :rtype: Manticore
        """
        if stdin_size is None:
            stdin_size = consts.stdin_size

        try:
            return cls(
                _make_linux(
                    path,
                    argv,
                    envp,
                    entry_symbol,
                    symbolic_files,
                    concrete_start,
                    pure_symbolic,
                    stdin_size,
                ),
                **kwargs,
            )
        except elftools.common.exceptions.ELFError:
            raise ManticoreError(f"Invalid binary: {path}")

    @classmethod
    def decree(cls, path, concrete_start="", **kwargs):
        """
        Constructor for Decree binary analysis.

        :param str path: Path to binary to analyze
        :param str concrete_start: Concrete stdin to use before symbolic input
        :param kwargs: Forwarded to the Manticore constructor
        :return: Manticore instance, initialized with a Decree State
        :rtype: Manticore
        """
        try:
            return cls(_make_decree(path, concrete_start), **kwargs)
        except KeyError:  # FIXME(mark) magic parsing for DECREE should raise better error
            raise ManticoreError(f"Invalid binary: {path}")

    @property
    def binary_path(self):
        """
        Assumes that all states refers to a single common program. Might not be
        true in case program calls execve().
        """
        for st in self.all_states:
            return st.platform.program

    ############################################################################
    # Assertion hooks + callback
    ############################################################################

    def load_assertions(self, path):
        with open(path, "r") as f:
            for line in f.readlines():
                pc = int(line.split(" ")[0], 16)
                if pc in self._assertions:
                    logger.debug("Repeated PC in assertions file %s", path)
                self._assertions[pc] = " ".join(line.split(" ")[1:])
                self.subscribe("will_execute_instruction", self._assertions_callback)

    def _assertions_callback(self, state, pc, instruction):
        if pc not in self._assertions:
            return

        from ..core.parser.parser import parse

        program = self._assertions[pc]

        # This will interpret the buffer specification written in INTEL ASM.
        # (It may dereference pointers)
        assertion = parse(program, state.cpu.read_int, state.cpu.read_register)
        if not SelectedSolver.instance().can_be_true(state.constraints, assertion):
            logger.info(str(state.cpu))
            logger.info(
                "Assertion %x -> {%s} does not hold. Aborting state.", state.cpu.pc, program
            )
            raise TerminateState()

        # Everything is good add it.
        state.constraints.add(assertion)

    ###############################
    # Hook Callback Methods
    ###############################

    def init(self, f):
        """
        A decorator used to register a hook function to run before analysis begins. Hook
        function takes one :class:`~manticore.core.state.State` argument.
        """
        self._init_hooks.add(f)
        if self._init_hooks:
            self.subscribe("will_run", self._init_callback)
        return f

    def hook(self, pc, after=False):
        """
        A decorator used to register a hook function for a given instruction address.
        Equivalent to calling :func:`~add_hook`.

        :param pc: Address of instruction to hook
        :type pc: int or None
        """

        def decorator(f):
            self.add_hook(pc, f, after)
            return f

        return decorator

    def add_hook(self, pc, callback, after=False):
        """
        Add a callback to be invoked on executing a program counter. Pass `None`
        for pc to invoke callback on every instruction. `callback` should be a callable
        that takes one :class:`~manticore.core.state.State` argument.

        :param pc: Address of instruction to hook
        :type pc: int or None
        :param callable callback: Hook function
        """
        if not (isinstance(pc, int) or pc is None):
            raise TypeError(f"pc must be either an int or None, not {pc.__class__.__name__}")
        else:
            hooks, when, hook_callback = (
                (self._hooks, "will_execute_instruction", self._hook_callback)
                if not after
                else (self._after_hooks, "did_execute_instruction", self._after_hook_callback)
            )
            hooks.setdefault(pc, set()).add(callback)
            if hooks:
                self.subscribe(when, hook_callback)

    def _hook_callback(self, state, pc, instruction):
        "Invoke all registered generic hooks"

        # Ignore symbolic pc.
        # TODO(yan): Should we ask the solver if any of the hooks are possible,
        # and execute those that are?

        if issymbolic(pc):
            return

        # Invoke all pc-specific hooks
        for cb in self._hooks.get(pc, []):
            cb(state)

        # Invoke all pc-agnostic hooks
        for cb in self._hooks.get(None, []):
            cb(state)

    def _after_hook_callback(self, state, last_pc, pc, instruction):
        "Invoke all registered generic hooks"

        # Invoke all pc-specific hooks
        for cb in self._after_hooks.get(last_pc, []):
            cb(state)

        # Invoke all pc-agnostic hooks
        for cb in self._after_hooks.get(None, []):
            cb(state)

    def _init_callback(self, ready_states):
        for cb in self._init_hooks:
            # We _should_ only ever have one starting state. Right now we're putting
            # this in a loop for futureproofing.
            for state in ready_states:
                cb(state)

    ###############################
    # Symbol Resolution
    ###############################

    def resolve(self, symbol):
        """
        A helper method used to resolve a symbol name into a memory address when
        injecting hooks for analysis.

        :param symbol: function name to be resolved
        :type symbol: string

        :param line: if more functions present, optional line number can be included
        :type line: int or None
        """

        with open(self.binary_path, "rb") as f:

            elffile = ELFFile(f)

            # iterate over sections and identify symbol table section
            for section in elffile.iter_sections():
                if not isinstance(section, SymbolTableSection):
                    continue

                # get list of symbols by name
                symbols = section.get_symbol_by_name(symbol)
                if not symbols:
                    continue

                # return first indexed memory address for the symbol,
                return symbols[0].entry["st_value"]

            raise ValueError(f"The {self.binary_path} ELFfile does not contain symbol {symbol}")

    def run(self, timeout=None):
        with self.locked_context() as context:
            context["time_started"] = time.time()
        with self.kill_timeout(timeout):
            super().run()

    def finalize(self):
        super().finalize()
        self.save_run_data()

    def save_run_data(self):
        super().save_run_data()

        time_ended = time.time()

        with self.locked_context() as context:
            time_elapsed = time_ended - context["time_started"]

            logger.info("Total time: %s", time_elapsed)

            context["time_ended"] = time_ended
            context["time_elapsed"] = time_elapsed


def _make_initial_state(binary_path, **kwargs):
    with open(binary_path, "rb") as f:
        magic = f.read(4)
    if magic == b"\x7fELF":
        # Linux
        state = _make_linux(binary_path, **kwargs)
    elif magic == b"\x7fCGC":
        # Decree
        state = _make_decree(binary_path, **kwargs)
    else:
        raise NotImplementedError(f"Binary {binary_path} not supported.")
    return state


def _make_decree(program, concrete_start="", **kwargs):
    from ..platforms import decree

    constraints = ConstraintSet()
    platform = decree.SDecree(constraints, program)
    initial_state = State(constraints, platform)
    logger.info("Loading program %s", program)

    if concrete_start != "":
        logger.info(f"Starting with concrete input: {concrete_start}")
    platform.input.transmit(concrete_start)
    platform.input.transmit(initial_state.symbolicate_buffer("+" * 14, label="RECEIVE"))
    return initial_state


def _make_linux(
    program,
    argv=None,
    env=None,
    entry_symbol=None,
    symbolic_files=None,
    concrete_start="",
    pure_symbolic=False,
    stdin_size=None,
) -> State:
    from ..platforms import linux

    env = {} if env is None else env
    argv = [] if argv is None else argv
    env = [f"{k}={v}" for k, v in env.items()]

    if stdin_size is None:
        stdin_size = consts.stdin_size

    logger.info("Loading program %s", program)

    constraints = ConstraintSet()
    platform = linux.SLinux(
        program, argv=argv, envp=env, symbolic_files=symbolic_files, pure_symbolic=pure_symbolic
    )
    if entry_symbol is not None:
        entry_pc = platform._find_symbol(entry_symbol)
        if entry_pc is None:
            logger.error("No symbol for '%s' in %s", entry_symbol, program)
            raise ManticoreError("Symbol not found")
        else:
            logger.info("Found symbol '%s' (%x)", entry_symbol, entry_pc)
            # TODO: use argv as arguments for function
            platform.set_entry(entry_pc)

    initial_state = State(constraints, platform)

    if concrete_start != "":
        logger.info("Starting with concrete input: %s", concrete_start)

    if pure_symbolic:
        logger.warning("[EXPERIMENTAL] Using purely symbolic memory.")

    for i, arg in enumerate(argv):
        argv[i] = initial_state.symbolicate_buffer(arg, label=f"ARGV{i + 1}")

    for i, evar in enumerate(env):
        env[i] = initial_state.symbolicate_buffer(evar, label=f"ENV{i + 1}")

    # If any of the arguments or environment refer to symbolic values, re-
    # initialize the stack
    if any(issymbolic(x) for val in argv + env for x in val):
        platform.setup_stack([program] + argv, env)

    platform.input.write(concrete_start)

    # set stdin input...
    platform.input.write(initial_state.symbolicate_buffer("+" * stdin_size, label="STDIN"))
    return initial_state
