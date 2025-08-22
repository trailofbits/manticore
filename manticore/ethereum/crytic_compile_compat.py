"""
Compatibility wrapper for crytic-compile 0.3.x to work with Manticore's expected 0.2.x API

This module addresses several critical compatibility issues between crytic-compile versions:
- Issue #2619: CompilationUnit object has no attribute contracts_names
- Issue #1611: Invalid solc compilation
- Issue #2497: Failed to build contract with openzeppelin imports
- Issue #2523: Deployment Error with Hardhat Project

The wrapper handles API changes in crytic-compile 0.3.x where:
1. The main CryticCompile object contains compilation_units (not source_units directly)
2. Each CompilationUnit has source_units containing the contract data
3. SourceUnit methods changed from private attributes (_contracts_name) to public methods
4. filename_to_contracts is now a defaultdict with set values instead of list values
"""


class CompilationUnitWrapper:
    """Wraps a crytic-compile 0.3.x CompilationUnit to provide 0.2.x-like API"""

    def __init__(self, compilation_unit):
        # Handle both CryticCompile object (0.3.x) and CompilationUnit object (0.2.x)
        if hasattr(compilation_unit, "compilation_units"):
            # 0.3.x: compilation_unit is a CryticCompile object
            self._crytic_compile = compilation_unit
            if compilation_unit.compilation_units:
                self._cu = list(compilation_unit.compilation_units.values())[0]
            else:
                self._cu = None
        else:
            # 0.2.x: compilation_unit is already a CompilationUnit
            self._crytic_compile = None
            self._cu = compilation_unit

        self._source_unit = None

        # Get the first (and usually only) source unit
        if self._cu and hasattr(self._cu, "source_units") and self._cu.source_units:
            self._source_unit = list(self._cu.source_units.values())[0]

    @property
    def contracts_names(self):
        """Get all contract names"""
        # Try 0.3.x SourceUnit API first
        if self._source_unit:
            if hasattr(self._source_unit, "contracts_names"):
                return self._source_unit.contracts_names
            elif hasattr(self._source_unit, "_contracts_name"):
                return self._source_unit._contracts_name

        # Fallback to getting from filename_to_contracts
        if self._cu and hasattr(self._cu, "filename_to_contracts"):
            contracts = set()
            for fname_contracts in self._cu.filename_to_contracts.values():
                contracts.update(fname_contracts)
            return list(contracts)

        return []

    @property
    def contracts_names_without_libraries(self):
        """Get contract names excluding libraries"""
        # Try 0.3.x SourceUnit API first
        if self._source_unit:
            if hasattr(self._source_unit, "contracts_names_without_libraries"):
                return self._source_unit.contracts_names_without_libraries
            elif hasattr(self._source_unit, "_contracts_name_without_libraries"):
                if self._source_unit._contracts_name_without_libraries:
                    return self._source_unit._contracts_name_without_libraries

        # Fallback to all contracts (assuming no libraries for now)
        return self.contracts_names

    def libraries_names(self, contract_name):
        """Get library dependencies for a contract"""
        # Try 0.3.x SourceUnit API first
        if self._source_unit:
            if hasattr(self._source_unit, "libraries_names"):
                return self._source_unit.libraries_names(contract_name)
            elif hasattr(self._source_unit, "_libraries"):
                libs = self._source_unit._libraries.get(contract_name, [])
                return libs
        return []

    def bytecode_init(self, contract_name, libraries=None):
        """Get initialization bytecode"""
        bytecode = ""

        # Try 0.3.x SourceUnit API first
        if self._source_unit:
            if hasattr(self._source_unit, "bytecode_init"):
                bytecode = self._source_unit.bytecode_init(contract_name, libraries or {})
            elif hasattr(self._source_unit, "_init_bytecodes"):
                bytecode = self._source_unit._init_bytecodes.get(contract_name, "")

        # Handle library linking if needed
        if libraries and bytecode:
            for lib_name, lib_addr in libraries.items():
                # Simple placeholder replacement - may need more sophisticated linking
                bytecode = bytecode.replace(f"__{lib_name}__", lib_addr)

        return bytecode

    def bytecode_runtime(self, contract_name, libraries=None):
        """Get runtime bytecode"""
        bytecode = ""

        # Try 0.3.x SourceUnit API first
        if self._source_unit:
            if hasattr(self._source_unit, "bytecode_runtime"):
                bytecode = self._source_unit.bytecode_runtime(contract_name, libraries or {})
            elif hasattr(self._source_unit, "_runtime_bytecodes"):
                bytecode = self._source_unit._runtime_bytecodes.get(contract_name, "")

        # Handle library linking if needed
        if libraries and bytecode:
            for lib_name, lib_addr in libraries.items():
                bytecode = bytecode.replace(f"__{lib_name}__", lib_addr)

        return bytecode

    def srcmap_init(self, contract_name):
        """Get initialization source map"""
        if self._source_unit:
            if hasattr(self._source_unit, "srcmap_init"):
                return self._source_unit.srcmap_init(contract_name)
            elif hasattr(self._source_unit, "_srcmaps"):
                return self._source_unit._srcmaps.get(contract_name, "")
        return ""

    def srcmap_runtime(self, contract_name):
        """Get runtime source map"""
        if self._source_unit:
            if hasattr(self._source_unit, "srcmap_runtime"):
                return self._source_unit.srcmap_runtime(contract_name)
            elif hasattr(self._source_unit, "_srcmaps_runtime"):
                return self._source_unit._srcmaps_runtime.get(contract_name, "")
        return ""

    def hashes(self, contract_name):
        """Get function hashes"""
        if self._source_unit:
            if hasattr(self._source_unit, "hashes"):
                return self._source_unit.hashes(contract_name)
            elif hasattr(self._source_unit, "_hashes"):
                # Compute hashes if they haven't been computed yet
                if (
                    hasattr(self._source_unit, "_compute_hashes")
                    and contract_name not in self._source_unit._hashes
                ):
                    self._source_unit._compute_hashes(contract_name)
                return self._source_unit._hashes.get(contract_name, {})
        return {}

    def abi(self, contract_name):
        """Get contract ABI"""
        if self._source_unit:
            if hasattr(self._source_unit, "abi"):
                return self._source_unit.abi(contract_name)
            elif hasattr(self._source_unit, "_abis"):
                return self._source_unit._abis.get(contract_name, [])
        return []

    @property
    def filename_to_contracts(self):
        """Get filename to contracts mapping"""
        if self._cu and hasattr(self._cu, "filename_to_contracts"):
            # Convert defaultdict to regular dict and convert set values to lists for compatibility
            result = {}
            for filename, contracts in self._cu.filename_to_contracts.items():
                if isinstance(contracts, set):
                    result[filename] = list(contracts)
                else:
                    result[filename] = contracts
            return result
        return {}


def wrap_compilation_unit(compilation_unit):
    """
    Wraps a crytic-compile 0.3.x CompilationUnit to provide 0.2.x-compatible API
    """
    return CompilationUnitWrapper(compilation_unit)
