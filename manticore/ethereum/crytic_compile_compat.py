"""
Compatibility wrapper for crytic-compile 0.3.x to work with Manticore's expected 0.2.x API
"""


class CompilationUnitWrapper:
    """Wraps a crytic-compile 0.3.x CompilationUnit to provide 0.2.x-like API"""
    
    def __init__(self, compilation_unit):
        self._cu = compilation_unit
        self._source_unit = None
        
        # Get the first (and usually only) source unit
        if self._cu.source_units:
            self._source_unit = list(self._cu.source_units.values())[0]
    
    @property
    def contracts_names(self):
        """Get all contract names"""
        if self._source_unit and self._source_unit._contracts_name:
            return self._source_unit._contracts_name
        # Fallback to getting from filename_to_contracts
        contracts = set()
        for fname_contracts in self._cu.filename_to_contracts.values():
            contracts.update(fname_contracts)
        return list(contracts)
    
    @property 
    def contracts_names_without_libraries(self):
        """Get contract names excluding libraries"""
        # In 0.3.x, _contracts_name_without_libraries might not be set
        # We'll use all contracts for now as we can't easily distinguish
        if self._source_unit and hasattr(self._source_unit, '_contracts_name_without_libraries'):
            if self._source_unit._contracts_name_without_libraries:
                return self._source_unit._contracts_name_without_libraries
        # Fallback to all contracts
        return self.contracts_names
    
    def libraries_names(self, contract_name):
        """Get library dependencies for a contract"""
        if self._source_unit and hasattr(self._source_unit, '_libraries'):
            libs = self._source_unit._libraries.get(contract_name, [])
            return libs
        return []
    
    def bytecode_init(self, contract_name, libraries=None):
        """Get initialization bytecode"""
        if self._source_unit and self._source_unit._init_bytecodes:
            bytecode = self._source_unit._init_bytecodes.get(contract_name, '')
            # Handle library linking if needed
            if libraries and bytecode:
                for lib_name, lib_addr in libraries.items():
                    # Simple placeholder replacement - may need more sophisticated linking
                    bytecode = bytecode.replace(f'__{lib_name}__', lib_addr)
            return bytecode
        return ''
    
    def bytecode_runtime(self, contract_name, libraries=None):
        """Get runtime bytecode"""
        if self._source_unit and self._source_unit._runtime_bytecodes:
            bytecode = self._source_unit._runtime_bytecodes.get(contract_name, '')
            # Handle library linking if needed
            if libraries and bytecode:
                for lib_name, lib_addr in libraries.items():
                    bytecode = bytecode.replace(f'__{lib_name}__', lib_addr)
            return bytecode
        return ''
    
    def srcmap_init(self, contract_name):
        """Get initialization source map"""
        if self._source_unit and hasattr(self._source_unit, '_srcmaps'):
            return self._source_unit._srcmaps.get(contract_name, '')
        return ''
    
    def srcmap_runtime(self, contract_name):
        """Get runtime source map"""
        if self._source_unit and hasattr(self._source_unit, '_srcmaps_runtime'):
            return self._source_unit._srcmaps_runtime.get(contract_name, '')
        return ''
    
    def hashes(self, contract_name):
        """Get function hashes"""
        if self._source_unit and hasattr(self._source_unit, '_hashes'):
            return self._source_unit._hashes.get(contract_name, {})
        return {}
    
    def abi(self, contract_name):
        """Get contract ABI"""
        if self._source_unit and self._source_unit._abis:
            return self._source_unit._abis.get(contract_name, [])
        return []
    
    @property
    def filename_to_contracts(self):
        """Get filename to contracts mapping"""
        return self._cu.filename_to_contracts


def wrap_compilation_unit(compilation_unit):
    """
    Wraps a crytic-compile 0.3.x CompilationUnit to provide 0.2.x-compatible API
    """
    return CompilationUnitWrapper(compilation_unit)