from typing import Any, Dict, Mapping, Optional, Sequence, Iterable, Tuple
import pyevmasm as EVMAsm

from .abi import ABI
from ..utils.deprecated import deprecated


class SolidityMetadata:
    @staticmethod
    def function_signature_for_name_and_inputs(
        name: str, inputs: Sequence[Mapping[str, Any]]
    ) -> str:
        """Returns the function signature for the specified name and Solidity JSON metadata inputs array.

        The ABI specification defines the function signature as the function name followed by the parenthesised list of
        parameter types separated by single commas and no spaces.
        See https://solidity.readthedocs.io/en/latest/abi-spec.html#function-selector
        """
        return name + SolidityMetadata.tuple_signature_for_components(inputs)

    @staticmethod
    def tuple_signature_for_components(components: Sequence[Mapping[str, Any]]) -> str:
        """Equivalent to ``function_signature_for_name_and_inputs('', components)``."""
        ts = []
        for c in components:
            t: str = c["type"]
            if t.startswith("tuple"):
                assert len(t) == 5 or t[5] == "["
                t = SolidityMetadata.tuple_signature_for_components(c["components"]) + t[5:]
            ts.append(t)
        return f'({",".join(ts)})'

    def __init__(
        self,
        name,
        source_code,
        init_bytecode,
        runtime_bytecode,
        srcmap,
        srcmap_runtime,
        hashes,
        abi,
        warnings,
    ):
        """ Contract metadata for Solidity-based contracts """
        self.name = name
        if isinstance(source_code, bytes):
            source_code = source_code.decode()
        self.source_code = source_code
        self._init_bytecode = init_bytecode
        self._runtime_bytecode = runtime_bytecode

        self._function_signatures_by_selector = {
            bytes.fromhex("{:08x}".format(sel)): sig for sig, sel in hashes.items()
        }

        fallback_selector = b"\0\0\0\0"
        while fallback_selector in self._function_signatures_by_selector:
            fallback_selector = (int.from_bytes(fallback_selector, "big") + 1).to_bytes(4, "big")
        self._fallback_function_selector = fallback_selector

        self._constructor_abi_item = None
        self._fallback_function_abi_item = None
        function_items = {}
        event_items = {}
        for item in abi:
            type = item["type"]
            if type == "function":
                signature = self.function_signature_for_name_and_inputs(
                    item["name"], item["inputs"]
                )
                function_items[signature] = item
            elif type == "event":
                signature = self.function_signature_for_name_and_inputs(
                    item["name"], item["inputs"]
                )
                event_items[signature] = item
            elif type == "constructor":
                assert not self._constructor_abi_item, "A constructor cannot be overloaded"
                self._constructor_abi_item = item
            elif type == "fallback":
                assert (
                    not self._fallback_function_abi_item
                ), "There can only be one fallback function"
                self._fallback_function_abi_item = item
        self._function_abi_items_by_signature = function_items
        self._event_abi_items_by_signature = event_items

        self.warnings = warnings
        self.srcmap_runtime = self.__build_source_map(self.runtime_bytecode, srcmap_runtime)
        self.srcmap = self.__build_source_map(self.init_bytecode, srcmap)

    def get_constructor_arguments(self) -> str:
        """Returns the tuple type signature for the arguments of the contract constructor."""
        item = self._constructor_abi_item
        return "()" if item is None else self.tuple_signature_for_components(item["inputs"])

    @staticmethod
    def _without_metadata(bytecode):
        end = None
        if (
            bytecode[-43:-34] == b"\xa1\x65\x62\x7a\x7a\x72\x30\x58\x20"
            and bytecode[-2:] == b"\x00\x29"
        ):
            end = -9 - 32 - 2  # Size of metadata at the end of most contracts
        return bytecode[:end]

    def __build_source_map(self, bytecode, srcmap):
        # https://solidity.readthedocs.io/en/develop/miscellaneous.html#source-mappings
        new_srcmap = {}
        bytecode = self._without_metadata(bytecode)
        if self.source_code and bytecode and srcmap:
            asm_offset = 0
            asm_pos = 0
            md = dict(enumerate(srcmap[asm_pos].split(":")))
            byte_offset = int(
                md.get(0, 0)
            )  # is the byte-offset to the start of the range in the source file
            source_len = int(md.get(1, 0))  # is the length of the source range in bytes
            file_index = int(md.get(2, 0))  # is the source index over sourceList
            jump_type = md.get(
                3, None
            )  # this can be either i, o or - signifying whether a jump instruction goes into a function, returns from a function or is a regular jump as part of e.g. a loop

            pos_to_offset = {}
            for i in EVMAsm.disassemble_all(bytecode):
                pos_to_offset[asm_pos] = asm_offset
                asm_pos += 1
                asm_offset += i.size

            for asm_pos, md in enumerate(srcmap):
                if len(md):
                    d = {p: k for p, k in enumerate(md.split(":")) if k}

                    byte_offset = int(d.get(0, byte_offset))
                    source_len = int(d.get(1, source_len))
                    file_index = int(d.get(2, file_index))
                    jump_type = d.get(3, jump_type)

                new_srcmap[pos_to_offset[asm_pos]] = (
                    byte_offset,
                    source_len,
                    file_index,
                    jump_type,
                )

        return new_srcmap

    @property
    def runtime_bytecode(self):
        # Removes metadata from the tail of bytecode
        return self._without_metadata(self._runtime_bytecode)

    @property
    def init_bytecode(self):
        # Removes metadata from the tail of bytecode
        return self._without_metadata(self._init_bytecode)

    def get_source_for(self, asm_offset, runtime=True):
        """ Solidity source code snippet related to `asm_pos` evm bytecode offset.
            If runtime is False, initialization bytecode source map is used
        """
        srcmap = self.get_srcmap(runtime)

        try:
            beg, size, _, _ = srcmap[asm_offset]
        except KeyError:
            # asm_offset pointing outside the known bytecode
            return ""

        output = ""
        nl = self.source_code[:beg].count("\n") + 1
        snippet = self.source_code[beg : beg + size]
        for l in snippet.split("\n"):
            output += "    %s  %s\n" % (nl, l)
            nl += 1
        return output

    def get_srcmap(self, runtime=True):
        return self.srcmap_runtime if runtime else self.srcmap

    @property
    def signatures(self) -> Dict[bytes, str]:
        """Returns a new dict mapping contract function selectors to the function signatures.

        The dict does not include an item for the default or non-default fallback function.
        """
        return dict(self._function_signatures_by_selector)

    @property
    def has_non_default_constructor(self) -> bool:
        """Indicates whether the contract has an explicitly defined constructor."""
        return self._fallback_function_abi_item is not None

    @property
    def constructor_abi(self) -> Dict[str, Any]:
        """Returns a copy of the Solidity JSON ABI item for the contract constructor.

        The content of the returned dict is described at https://solidity.readthedocs.io/en/latest/abi-spec.html#json_
        """
        item = self._constructor_abi_item
        if item:
            return dict(item)
        return {
            "inputs": [],
            "payable": False,
            "stateMutability": "nonpayable",
            "type": "constructor",
        }

    def get_abi(self, hsh: bytes) -> Dict[str, Any]:
        """Returns a copy of the Solidity JSON ABI item for the function associated with the selector ``hsh``.

        If no normal contract function has the specified selector, a dict describing the default or non-default
        fallback function is returned.

        The content of the returned dict is described at https://solidity.readthedocs.io/en/latest/abi-spec.html#json_
        """
        if not isinstance(hsh, (bytes, bytearray)):
            raise TypeError("The selector argument must be a concrete byte array")
        sig = self._function_signatures_by_selector.get(hsh)
        if sig is not None:
            return dict(self._function_abi_items_by_signature[sig])
        item = self._fallback_function_abi_item
        if item is not None:
            return dict(item)
        # An item describing the default fallback function.
        return {"payable": False, "stateMutability": "nonpayable", "type": "fallback"}

    def get_func_argument_types(self, hsh: bytes):
        """Returns the tuple type signature for the arguments of the function associated with the selector ``hsh``.

        If no normal contract function has the specified selector,
        the empty tuple type signature ``'()'`` is returned.
        """
        if not isinstance(hsh, (bytes, bytearray)):
            raise TypeError("The selector argument must be a concrete byte array")
        sig = self._function_signatures_by_selector.get(hsh)
        return "()" if sig is None else sig[sig.find("(") :]

    def get_func_return_types(self, hsh: bytes) -> str:
        """Returns the tuple type signature for the output values of the function
        associated with the selector ``hsh``.

        If no normal contract function has the specified selector,
        the empty tuple type signature ``'()'`` is returned.
        """
        if not isinstance(hsh, (bytes, bytearray)):
            raise TypeError("The selector argument must be a concrete byte array")
        abi = self.get_abi(hsh)
        outputs = abi.get("outputs")
        return "()" if outputs is None else SolidityMetadata.tuple_signature_for_components(outputs)

    def get_func_name(self, hsh: bytes) -> str:
        """Returns the name of the normal function with the selector ``hsh``,
        or ``'{fallback}'`` if no such function exists.
        """
        if not isinstance(hsh, (bytes, bytearray)):
            raise TypeError("The selector argument must be a concrete byte array")
        sig = self._function_signatures_by_selector.get(hsh)
        return "{fallback}" if sig is None else sig[: sig.find("(")]

    def get_func_signature(self, hsh: bytes) -> Optional[str]:
        """Returns the signature of the normal function with the selector ``hsh``,
        or ``None`` if no such function exists.

        This function returns ``None`` for any selector that will be dispatched to a fallback function.
        """
        if not isinstance(hsh, (bytes, bytearray)):
            raise TypeError("The selector argument must be a concrete byte array")
        return self._function_signatures_by_selector.get(hsh)

    @deprecated("Use `abi.ABI.function_selector` instead.")
    def get_hash(self, method_name_and_signature) -> bytes:
        return ABI.function_selector(method_name_and_signature)

    @property
    def function_signatures(self) -> Iterable[str]:
        """The signatures of all normal contract functions."""
        return self._function_signatures_by_selector.values()

    @property  # type: ignore
    @deprecated(
        "Use `.function_signatures` instead, which does not return the `'{fallback}()'` pseudo-signature"
    )
    def functions(self) -> Tuple[str, ...]:
        """The signatures of all normal contract functions, plus the ``'{fallback}()'`` pseudo-signature."""
        return (*self._function_signatures_by_selector.values(), "{fallback}()")

    @property
    def has_non_default_fallback_function(self) -> bool:
        """Indicates whether the contract has an explicitly defined fallback function."""
        return self._fallback_function_abi_item is not None

    @property
    def fallback_function_selector(self) -> bytes:
        """A function selector not associated with any of the non-fallback contract functions.

        This selector is almost always ``b'\0\0\0\0'``.
        """
        return self._fallback_function_selector

    @property
    def function_selectors(self) -> Iterable[bytes]:
        """The selectors of all normal contract functions,
        plus ``self.fallback_function_selector`` if the contract has a non-default fallback function.
        """
        selectors = self._function_signatures_by_selector.keys()
        if self._fallback_function_abi_item is None:
            return tuple(selectors)
        return (*selectors, self.fallback_function_selector)

    @property  # type: ignore
    @deprecated(
        "Use `.function_selectors` instead, which only returns a fallback"
        " function selector if the contract has a non-default fallback function."
    )
    def hashes(self) -> Tuple[bytes, ...]:
        """The selectors of all normal contract functions, plus ``self.fallback_function_selector``."""
        selectors = self._function_signatures_by_selector.keys()
        return (*selectors, self.fallback_function_selector)

    def parse_tx(self, calldata, returndata=None):
        if returndata is None:
            returndata = bytes()
        if not isinstance(calldata, (bytes, bytearray)):
            raise TypeError("calldata must be a concrete byte array")
        if not isinstance(returndata, (bytes, bytearray)):
            raise TypeError("returndata must be a concrete byte array")
        calldata = bytes(calldata)
        returndata = bytes(returndata)
        function_id = calldata[:4]
        signature = self.get_func_signature(function_id)
        function_name = self.get_func_name(function_id)
        if signature:
            _, arguments = ABI.deserialize(signature, calldata)
        else:
            arguments = (calldata,)

        arguments_str = ", ".join(map(str, arguments))
        return_value = None
        if returndata:
            ret_types = self.get_func_return_types(function_id)
            return_value = ABI.deserialize(ret_types, returndata)  # function return
            return f"{function_name}({arguments_str}) -> {return_value}"
        else:
            return f"{function_name}({arguments_str})"
