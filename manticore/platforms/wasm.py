from .platform import Platform
from ..wasm.structure import (
    ModuleInstance,
    Store,
    FuncAddr,
    HostFunc,
    Stack,
    ProtoFuncInst,
    MemInst,
    MemAddr,
    GlobalInst,
    GlobalAddr,
    TableInst,
    TableAddr,
    ExternVal,
    Module,
)
from ..wasm.types import Trap, TypeIdx, TableType, MemoryType, GlobalType, MissingExportException
from ..core.state import TerminateState
from ..core.smtlib import ConstraintSet
from functools import partial
import typing
import logging
import os

logger = logging.getLogger(__name__)
# logger.setLevel(logging.DEBUG)


def stub(arity, _state, *args):
    """Default function used for hostfunc calls when a proper import wasn't provided"""
    logger.info("Called stub function with args: %s", args)
    return [0 for _ in range(arity)]  # TODO: Return symbolic values


class WASMWorld(Platform):
    """Manages global environment for a WASM state. Analagous to EVMWorld."""

    def __init__(self, filename, name="self", **kwargs):
        """
        :param filename: The WASM module to execute
        :param kwargs: Accepts "constraints" to pass in an initial ConstraintSet
        """
        super().__init__(filename, **kwargs)
        #: Initial set of constraints
        self.constraints = kwargs.get("constraints", ConstraintSet())
        #: Prevents users from calling run without instantiating the module
        self.instantiated = []
        #: Backing store for functions, memories, tables, and globals
        self.store = Store()

        self.modules = []
        self.module_names = {}
        self.manual_exports = {}
        self.default_module = name
        self.register_module(name, filename)

        #: Stores numeric values, branch labels, and execution frames
        self.stack = Stack()

        #: Stores concretized information used to advise execution of the next instruction.
        self.advice = None

        self.forward_events_from(self.stack)
        self.forward_events_from(self.instance)
        self.forward_events_from(self.instance.executor)

    def __getstate__(self):
        state = super().__getstate__()
        state["modules"] = self.modules
        state["store"] = self.store
        state["stack"] = self.stack
        state["advice"] = self.advice
        state["constraints"] = self.constraints
        state["instantiated"] = self.instantiated
        state["module_names"] = self.module_names
        state["default_module"] = self.default_module
        state["manual_exports"] = self.manual_exports
        return state

    def __setstate__(self, state):
        self.modules = state["modules"]
        self.store = state["store"]
        self.stack = state["stack"]
        self.advice = state["advice"]
        self.constraints = state["constraints"]
        self.instantiated = state["instantiated"]
        self.module_names = state["module_names"]
        self.default_module = state["default_module"]
        self.manual_exports = state["manual_exports"]
        self.forward_events_from(self.stack)
        self.forward_events_from(self.instance)
        self.forward_events_from(self.instance.executor)
        for mem in self.store.mems:
            self.forward_events_from(mem)
        super().__setstate__(state)

    @property
    def instance(self) -> ModuleInstance:
        """
        :return: the ModuleInstance for the first module registered
        """
        return self.modules[self.module_names[self.default_module]][1]

    @property
    def module(self) -> Module:
        """
        :return: The first module registered
        """
        return self.modules[self.module_names[self.default_module]][0]

    def register_module(self, name, filename_or_alias):
        """
        Provide an explicit path to a WASM module so the importer will know where to find it

        :param name: Module name to register the module under
        :param filename_or_alias: Name of the .wasm file that module lives in
        :return:
        """
        if filename_or_alias in self.module_names:
            self.module_names[name] = self.module_names[filename_or_alias]
        if name not in self.module_names:
            self.modules.append((Module.load(filename_or_alias), ModuleInstance(self.constraints)))
            self.module_names[name] = len(self.modules) - 1
            self.instantiated.append(False)

    def set_env(
        self,
        exports: typing.Dict[
            str, typing.Union[ProtoFuncInst, TableInst, MemInst, GlobalInst, typing.Callable]
        ],
        mod_name="env",
    ):
        """
        Manually insert exports into the global environment

        :param exports: Dict mapping names to functions/tables/globals/memories
        :param mod_name: The name of the module these exports should fall under
        """
        self.manual_exports.setdefault(mod_name, {}).update(exports)

    def import_module(self, module_name, exec_start, stub_missing):
        """
        Collect all of the imports for the given module and instantiate it

        :param module_name: module to import
        :param exec_start: whether to run the start functions automatically
        :param stub_missing: whether to replace missing imports with stubs
        :return: None
        """
        search_paths = {"."}
        # If the module isn't registered, look for it on the filesystem
        if module_name not in self.module_names:
            logger.debug("Module %s was not provided, attempting to load from disk", module_name)
            for pth in search_paths:
                possible_path = os.path.join(pth, module_name + ".wasm")
                if os.path.isfile(possible_path):
                    self.register_module(module_name, possible_path)
                    break
            else:
                raise RuntimeError("Missing imported module: " + module_name)

        if self.instantiated[self.module_names[module_name]]:
            return

        # Get the module and the instance from the world
        module, instance = self.modules[self.module_names[module_name]]

        imports = self.get_module_imports(module, exec_start, stub_missing)

        instance.instantiate(self.store, module, imports, exec_start)
        self.instantiated[self.module_names[module_name]] = True
        logger.info("Imported %s", module_name)

    def _get_export_addr(
        self, export_name, mod_name=None
    ) -> typing.Optional[typing.Union[FuncAddr, TableAddr, MemAddr, GlobalAddr]]:
        """
        Gets the address in the store of a given export

        :param export_name: Name of the export to look for
        :param mod_name: Name of the module the export lives in
        :return: The address of the export
        """
        try:
            if mod_name in self.module_names:  # TODO - handle mod_name.export_name
                return self.modules[self.module_names[mod_name]][1].get_export_address(export_name)
        except MissingExportException as exc:
            logger.error("Couldn't find export %s.%s", mod_name, exc.name)
        return None

    def get_export(
        self, export_name, mod_name=None
    ) -> typing.Optional[
        typing.Union[ProtoFuncInst, TableInst, MemInst, GlobalInst, typing.Callable]
    ]:
        """
        Gets the export _instance_ for a given export & module name
        (basically just dereferences _get_export_addr into the store)

        :param export_name: Name of the export to look for
        :param mod_name: Name of the module the export lives in
        :return: The export itself
        """
        mod_name = self.default_module if not mod_name else mod_name
        if mod_name in self.manual_exports:
            if export_name in self.manual_exports[mod_name]:
                return self.manual_exports[mod_name][export_name]
        addr = self._get_export_addr(export_name, mod_name)
        if addr is not None:
            if isinstance(addr, FuncAddr):
                return self.store.funcs[addr]
            if isinstance(addr, TableAddr):
                return self.store.funcs[addr]
            if isinstance(addr, MemAddr):
                return self.store.mems[addr]
            if isinstance(addr, GlobalAddr):
                return self.store.globals[addr]

        return None

    def get_module_imports(self, module, exec_start, stub_missing) -> typing.List[ExternVal]:
        """
        Builds the list of imports that should be passed to the given module upon instantiation

        :param module: The module to find the imports for
        :param exec_start: Whether to execute the start function of the module
        :param stub_missing: Whether to replace missing imports with stubs (TODO: symbolicate)
        :return: List of addresses for the imports within the store
        """
        imports: typing.List[ExternVal] = []
        for i in module.imports:
            logger.info("Importing %s:%s", i.module, i.name)
            if i.module not in self.module_names:  # If the module isn't registered
                if i.module not in self.manual_exports:  # or manually provided
                    # Attempt to load it from the filesystem
                    self.import_module(
                        i.module, exec_start, stub_missing
                    )  # TODO - prevent circular imports
            # If it's registered, but hasn't been imported yet, import it
            elif not self.instantiated[self.module_names[i.module]]:
                self.import_module(i.module, exec_start, stub_missing)
            imported_version = self._get_export_addr(i.name, i.module)
            if imported_version is None:
                # check for manually provided version
                # Possibly overwriting imported_version from an address to an instance here
                imported_version = self.get_export(i.name, i.module)  # type: ignore
                if imported_version is None and not stub_missing:
                    raise RuntimeError(f"Could not find import {i.module}:{i.name}")

            if isinstance(imported_version, (FuncAddr, TableAddr, MemAddr, GlobalAddr)):
                imports.append(imported_version)  # TODO - Import type matching
            else:
                if isinstance(i.desc, TypeIdx):  # Imported function
                    func_type = module.types[i.desc]
                    if i.module == "env" and imported_version:
                        if callable(imported_version):
                            logger.info(
                                "Auto-converting callable %s into HostFunc of appropriate type",
                                i.name,
                            )
                            imported_version = HostFunc(func_type, imported_version)
                    self.store.funcs.append(
                        imported_version
                        if imported_version
                        else HostFunc(
                            # mypy doesn't like that we're using a partial function instead of a proper function
                            func_type,
                            partial(stub, len(func_type.result_types)),  # type: ignore
                        )
                    )
                    addr = FuncAddr(len(self.store.funcs) - 1)
                    imports.append(addr)
                    self.instance.function_names[addr] = f"{i.module}.{i.name}"

                elif isinstance(i.desc, TableType):
                    self.store.tables.append(
                        imported_version
                        if imported_version
                        else TableInst([None] * i.desc.limits.min, i.desc.limits.max)
                    )
                    imports.append(TableAddr(len(self.store.tables) - 1))
                # Create an empty memory of the correct size and provide it as an import
                elif isinstance(i.desc, MemoryType):
                    self.store.mems.append(
                        imported_version
                        if imported_version
                        else MemInst([0x0] * i.desc.min * 64 * 1024, i.desc.max)
                    )
                    imports.append(MemAddr(len(self.store.mems) - 1))
                # Create a global and set its value to 0.
                elif isinstance(i.desc, GlobalType):
                    self.store.globals.append(
                        imported_version
                        if imported_version
                        else GlobalInst(i.desc.value(0), i.desc.mut)
                    )
                    imports.append(GlobalAddr(len(self.store.globals) - 1))
                else:
                    raise RuntimeError(f"Don't know how to handle imports of type {type(i.desc)}")

        return imports

    def instantiate(
        self,
        env_import_dict: typing.Dict[
            str, typing.Union[ProtoFuncInst, TableInst, MemInst, GlobalInst, typing.Callable]
        ],
        supplemental_env: typing.Dict[
            str,
            typing.Dict[
                str, typing.Union[ProtoFuncInst, TableInst, MemInst, GlobalInst, typing.Callable]
            ],
        ] = {},
        exec_start=False,
        stub_missing=True,
    ):
        """
        Prepares the underlying ModuleInstance for execution. Calls import_module under the hood, so this is probably
        the only import-y function you ever need to call externally.

        TODO: stubbed imports should be symbolic

        :param env_import_dict: Dict mapping strings to functions. Functions should accept the current ConstraintSet as the first argument.
        :param supplemental_env: Maps strings w/ module names to environment dicts using the same format as env_import_dict
        :param exec_start: Whether or not to automatically execute the `start` function, if it is set.
        :param stub_missing: Whether or not to replace missing imports with empty stubs
        :return: None
        """
        self.set_env(env_import_dict)
        for k in supplemental_env:
            self.set_env(supplemental_env[k], k)
        self.import_module(self.default_module, exec_start, stub_missing)
        for mem in self.store.mems:
            self.forward_events_from(mem)

    def invoke(self, name="main", argv=[], module=None):
        """
        Sets up the WASMWorld to run the function specified by `name` when `ManticoreWASM.run` is called

        :param name: Name of the function to invoke
        :param argv: List of arguments to pass to the function. Should typically be I32, I64, F32, or F64
        :param module: name of a module to call the function in (if not the default module)
        :return: None
        """
        module = self.default_module if module is None else module
        instance = self.modules[self.module_names[module]][1]
        instance.invoke_by_name(name, self.stack, self.store, list(argv))

    def exec_for_test(self, funcname, module=None):
        """
        Helper method that simulates the evaluation loop without creating workers or states, forking, or concretizing
        symbolic values.
        Only used for concrete unit testing.

        :param funcname: The name of the function to test
        :param module: The name of the module to test the function in (if not the default module)
        :return: The top n items from the stack where n is the expected number of return values from the function
        """
        module = self.default_module if module is None else module
        instance = self.modules[self.module_names[module]][1]

        # Grab the appropriate number of return values for the function being invoked
        rets = 0
        for export in instance.exports:
            if export.name == funcname and isinstance(export.value, FuncAddr):
                rets = len(self.store.funcs[export.value].type.result_types)

        # Call exec_instruction until it returns false or throws an error
        try:
            while self._exec_instruction(instance):
                pass
            # Return the top `rets` values from the stack
            return [self.stack.pop() for _i in range(rets)]
        except (Trap, NotImplementedError) as e:  # Reset the internals if we have any problems
            instance.reset_internal()
            self.stack = Stack()
            raise e

    def execute(self, current_state):
        """
        Tells the underlying ModuleInstance to execute a single WASM instruction. Raises TerminateState if there are
        no more instructions to execute, or if the instruction raises a Trap.
        """
        if not self.instantiated:
            raise RuntimeError("Trying to execute before instantiation!")
        try:
            if not self._exec_instruction(self.instance, current_state):
                raise TerminateState(f"Execution returned {self.stack.peek()}")
        except Trap as e:
            raise TerminateState(f"Execution raised Trap: {str(e)}")

    def _exec_instruction(self, instance, current_state=None):
        """
        Executes a single instruction on the instance and clears the advice.
        """
        try:
            return instance.exec_instruction(self.store, self.stack, self.advice, current_state)
        finally:
            self.advice = None
