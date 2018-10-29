import pyevmasm as EVMAsm

from .abi import ABI
from ..exceptions import EthereumError


class SolidityMetadata(object):
    def __init__(self, name, source_code, init_bytecode, runtime_bytecode, srcmap, srcmap_runtime, hashes, abi, warnings):
        """ Contract metadata for Solidity-based contracts """
        self.name = name
        if isinstance(source_code, bytes):
            source_code = source_code.decode()
        self.source_code = source_code
        self._init_bytecode = init_bytecode
        self._runtime_bytecode = runtime_bytecode
        self._functions = hashes.keys()
        self.abi = {item.get('name', '{fallback}'): item for item in abi}
        self.warnings = warnings
        self.srcmap_runtime = self.__build_source_map(self.runtime_bytecode, srcmap_runtime)
        self.srcmap = self.__build_source_map(self.init_bytecode, srcmap)

    def get_constructor_arguments(self):
        for fun in self.abi.values():
            if fun['type'] == 'constructor':
                constructor_inputs = fun['inputs']
                break
        else:
            constructor_inputs = ()

        def process(spec):
            if spec['type'].startswith('tuple'):
                types = []
                for component in spec['components']:
                    types.append(process(component))
                return '({}){:s}'.format(','.join(types), spec['type'][5:])
            else:
                return spec['type']
        inputs = {'components': constructor_inputs, 'type': 'tuple'}
        return process(inputs)

    def add_function(self, method_name_and_signature):
        if not isinstance(method_name_and_signature, str):
            raise ValueError("method_name_and_signature needs to be a string")
        #TODO: use re, and check it's sane
        name = method_name_and_signature.split('(')[0]
        if name in self.abi:
            raise EthereumError("Function already defined")
        hsh = ABI.function_selector(method_name_and_signature)
        self._functions.add(method_name_and_signature)

        input_types = method_name_and_signature.split('(')[1].split(')')[0].split(',')
        output_types = method_name_and_signature.split(')')[1].split(',')
        self.abi[name] = {'inputs': [{'type': ty} for ty in input_types],
                          'name': name,
                          'outputs': [{'type': ty} for ty in output_types]}

    @staticmethod
    def _without_metadata(bytecode):
        end = None
        if bytecode[-43: -34] == b'\xa1\x65\x62\x7a\x7a\x72\x30\x58\x20' \
                and bytecode[-2:] == b'\x00\x29':
            end = -9 - 32 - 2  # Size of metadata at the end of most contracts
        return bytecode[:end]

    def __build_source_map(self, bytecode, srcmap):
        # https://solidity.readthedocs.io/en/develop/miscellaneous.html#source-mappings
        new_srcmap = {}
        bytecode = self._without_metadata(bytecode)

        asm_offset = 0
        asm_pos = 0
        md = dict(enumerate(srcmap[asm_pos].split(':')))
        byte_offset = int(md.get(0, 0))  # is the byte-offset to the start of the range in the source file
        source_len = int(md.get(1, 0))  # is the length of the source range in bytes
        file_index = int(md.get(2, 0))  # is the source index over sourceList
        jump_type = md.get(3, None)  # this can be either i, o or - signifying whether a jump instruction goes into a function, returns from a function or is a regular jump as part of e.g. a loop

        pos_to_offset = {}
        for i in EVMAsm.disassemble_all(bytecode):
            pos_to_offset[asm_pos] = asm_offset
            asm_pos += 1
            asm_offset += i.size

        for asm_pos, md in enumerate(srcmap):
            if len(md):
                d = {p: k for p, k in enumerate(md.split(':')) if k}

                byte_offset = int(d.get(0, byte_offset))
                source_len = int(d.get(1, source_len))
                file_index = int(d.get(2, file_index))
                jump_type = d.get(3, jump_type)

            new_srcmap[pos_to_offset[asm_pos]] = (byte_offset, source_len, file_index, jump_type)

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
            #asm_offset pointing outside the known bytecode
            return ''

        output = ''
        nl = self.source_code[:beg].count('\n')
        snippet = self.source_code[beg:beg + size]
        for l in snippet.split('\n'):
            output += '    %s  %s\n' % (nl, l)
            nl += 1
        return output

    def get_srcmap(self, runtime=True):
        return self.srcmap_runtime if runtime else self.srcmap

    @property
    def signatures(self):
        return dict(((self.get_hash(f), f) for f in self._functions))

    def get_abi(self, hsh):
        func_name = self.get_func_name(hsh)
        default_fallback_abi = {'stateMutability': 'nonpayable', 'payable': False, 'type': 'fallback'}
        return self.abi.get(func_name, default_fallback_abi)

    def get_func_argument_types(self, hsh):
        abi = self.get_abi(hsh)
        return '(' + ','.join(x['type'] for x in abi.get('inputs', [])) + ')'

    def get_func_return_types(self, hsh):
        abi = self.get_abi(hsh)
        return '(' + ','.join(x['type'] for x in abi.get('outputs', [])) + ')'

    def get_func_name(self, hsh):
        signature = self.signatures.get(hsh, '{fallback}()')
        return signature.split('(')[0]

    def get_func_signature(self, hsh):
        return self.signatures.get(hsh)

    def get_hash(self, method_name_and_signature):
        #helper
        return ABI.function_selector(method_name_and_signature)

    @property
    def functions(self):
        return tuple(self._functions) + ('{fallback}()',)

    @property
    def hashes(self):
        # \x00\x00\x00\x00 corresponds to {fallback}()
        return tuple(map(self.get_hash, self._functions)) + (b'\x00\x00\x00\x00',)

    def parse_tx(self, calldata, returndata=None):
        if returndata is None:
            returndata = bytes()
        if not isinstance(calldata, (bytes, bytearray)):
            raise ValueError("calldata must be a concrete array")
        if not isinstance(returndata, (bytes, bytearray)):
            raise ValueError("returndata must be a concrete array")
        calldata = bytes(calldata)
        returndata = bytes(returndata)
        function_id = calldata[:4]
        signature = self.get_func_signature(function_id)
        function_name = self.get_func_name(function_id)
        if signature:
            _, arguments = ABI.deserialize(signature, calldata)
        else:
            arguments = (calldata,)

        arguments_str = ', '.join(map(str, arguments))
        return_value = None
        if returndata:
            ret_types = self.get_func_return_types(function_id)
            return_value = ABI.deserialize(ret_types, returndata)  # function return
            return f'{function_name}({arguments_str}) -> {return_value}'
        else:
            return f'{function_name}({arguments_str})'
