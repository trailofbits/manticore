import typing
import logging
import uuid

import re
import sha3

from . import abitypes
from ..core.smtlib import (
    Array,
    Operators,
    BitVec,
    ArrayVariable,
    ArrayProxy,
    to_constant,
    issymbolic,
)
from ..exceptions import EthereumError

logger = logging.getLogger(__name__)


class ABI:
    """
        This class contains methods to handle the ABI.
        The Application Binary Interface is the standard way to interact with
        contracts in the Ethereum ecosystem, both from outside the blockchain
        and for contract-to-contract interaction.

    """

    @staticmethod
    def _type_size(ty):
        """ Calculate `static` type size """
        if ty[0] in ("int", "uint", "bytesM", "function"):
            return 32
        elif ty[0] in ("tuple"):
            result = 0
            for ty_i in ty[1]:
                result += ABI._type_size(ty_i)
            return result
        elif ty[0] in ("array"):
            rep = ty[1]
            result = 32  # offset link
            return result
        elif ty[0] in ("bytes", "string"):
            result = 32  # offset link
            return result
        raise ValueError

    @staticmethod
    def _check_and_warn_num_args(type_spec, *args):
        num_args = len(args)

        no_declared_args = "()" in type_spec
        if no_declared_args:
            num_sig_args = 0
        else:
            num_sig_args = len(type_spec.split(","))

        if num_args != num_sig_args:
            logger.warning(
                f"Number of provided arguments ({num_args}) does not match number of arguments in signature: {type_spec}"
            )

    @staticmethod
    def function_call(type_spec, *args):
        """
        Build transaction data from function signature and arguments
        """
        m = re.match(r"(?P<name>[a-zA-Z_][a-zA-Z_0-9]*)(?P<type>\(.*\))", type_spec)
        if not m:
            raise EthereumError("Function signature expected")

        ABI._check_and_warn_num_args(type_spec, *args)

        result = ABI.function_selector(type_spec)  # Funcid
        result += ABI.serialize(m.group("type"), *args)
        return result

    @staticmethod
    def serialize(ty, *values, **kwargs):
        """
        Serialize value using type specification in ty.
        ABI.serialize('int256', 1000)
        ABI.serialize('(int, int256)', 1000, 2000)
        """
        try:
            parsed_ty = abitypes.parse(ty)
        except Exception as e:
            # Catch and rebrand parsing errors
            raise EthereumError(str(e))

        if parsed_ty[0] != "tuple":
            if len(values) > 1:
                raise ValueError("too many values passed for non-tuple")
            values = values[0]
            if isinstance(values, str):
                values = values.encode()
        else:
            # implement type forgiveness for bytesM/string types
            # allow python strs also to be used for Solidity bytesM/string types
            values = tuple(val.encode() if isinstance(val, str) else val for val in values)

        result, dyn_result = ABI._serialize(parsed_ty, values)
        return result + dyn_result

    @staticmethod
    def _serialize(ty, value, dyn_offset=None):
        if dyn_offset is None:
            dyn_offset = ABI._type_size(ty)

        result = bytearray()
        dyn_result = bytearray()

        if ty[0] == "int":
            result += ABI._serialize_int(value, size=ty[1] // 8, padding=32 - ty[1] // 8)
        elif ty[0] == "uint":
            result += ABI._serialize_uint(value, size=ty[1] // 8, padding=32 - ty[1] // 8)
        elif ty[0] == "bytesM":
            nbytes = ty[1]
            if len(value) > nbytes:
                raise EthereumError(
                    "bytesM: value length exceeds size of bytes{} type".format(nbytes)
                )
            result += ABI._serialize_bytes(value)
        elif ty[0] in ("bytes", "string"):
            result += ABI._serialize_uint(dyn_offset)
            dyn_result += ABI._serialize_uint(len(value))
            dyn_result += ABI._serialize_bytes(value)
        elif ty[0] == "function":
            result = ABI._serialize_uint(value[0], 20)
            result += value[1] + bytearray("\0" * 8)
            assert len(result) == 32
        elif ty[0] == "tuple":
            sub_result, sub_dyn_result = ABI._serialize_tuple(ty[1], value, dyn_offset)
            result += sub_result
            dyn_result += sub_dyn_result
        elif ty[0] == "array":
            rep = ty[1]
            base_type = ty[2]
            sub_result, sub_dyn_result = ABI._serialize_array(rep, base_type, value, dyn_offset)
            result += sub_result
            dyn_result += sub_dyn_result

        assert len(result) == ABI._type_size(ty)
        return result, dyn_result

    @staticmethod
    def _serialize_bytes(value):
        """
        Serializes the value and pads to multiple of 32 bytes

        :param value:
        :type value: str or bytearray or Array
        """
        return value + bytearray(b"\x00" * (32 - len(value)))

    @staticmethod
    def _serialize_tuple(types, value, dyn_offset=None):
        result = bytearray()
        dyn_result = bytearray()
        if len(types) != len(value):
            raise ValueError(
                f"The number of values to serialize is {'less' if len(value) < len(types) else 'greater'} than the number of types"
            )
        for ty_i, value_i in zip(types, value):
            result_i, dyn_result_i = ABI._serialize(ty_i, value_i, dyn_offset + len(dyn_result))
            result += result_i
            dyn_result += dyn_result_i
        return result, dyn_result

    @staticmethod
    def _serialize_array(rep, base_type, value, dyn_offset=None):
        result = ABI._serialize_uint(dyn_offset)
        dyn_result = bytearray()

        sub_result = bytearray()
        sub_dyn_result = bytearray()

        if rep is not None and len(value) != rep:
            raise ValueError("More reps than values")
        sub_result += ABI._serialize_uint(len(value))

        for value_i in value:
            result_i, dyn_result_i = ABI._serialize(
                base_type, value_i, dyn_offset + len(dyn_result)
            )
            sub_result += result_i
            sub_dyn_result += dyn_result_i

        dyn_result += sub_result
        dyn_result += sub_dyn_result
        return result, dyn_result

    @staticmethod
    def function_selector(method_name_and_signature):
        """
        Makes a function hash id from a method signature
        """
        s = sha3.keccak_256()
        s.update(method_name_and_signature.encode())
        return bytes(s.digest()[:4])

    @staticmethod
    def deserialize(type_spec, data):
        try:
            if isinstance(data, str):
                data = bytearray(data.encode())
            elif isinstance(data, bytes):
                data = bytearray(data)
            assert isinstance(data, (bytearray, Array))

            m = re.match(r"(?P<name>[a-zA-Z_0-9]+)(?P<type>\(.*\))", type_spec)
            if m and m.group("name"):
                # Type has function name. Let's take the function id from the data
                # This does not check that the encoded func_id is valid
                # func_id = ABI.function_selector(type_spec)
                result = (data[:4],)
                ty = m.group("type")
                result += (ABI._deserialize(abitypes.parse(ty), data[4:]),)
            else:
                # No function name, just types
                ty = type_spec
                result = ABI._deserialize(abitypes.parse(ty), data)
            return result
        except Exception as e:
            raise EthereumError("Error {} deserializing type {:s}".format(str(e), type_spec))

    @staticmethod
    def _deserialize(ty, buf: typing.Union[bytearray, bytes, Array], offset=0):
        assert isinstance(buf, (bytearray, bytes, Array))
        result = None
        if ty[0] == "int":
            result = ABI._deserialize_int(buf[offset : offset + 32], nbytes=ty[1] // 8)
        elif ty[0] == "uint":
            result = ABI._deserialize_uint(buf[offset : offset + 32], nbytes=ty[1] // 8)
        elif ty[0] == "bytesM":
            result = buf[offset : offset + ty[1]]
        elif ty[0] == "function":
            address = Operators.ZEXTEND(ABI._readBE(buf[offset : offset + 20], 20), 256)
            func_id = buf[offset + 20 : offset + 24]
            result = (address, func_id)
        elif ty[0] in ("bytes", "string"):
            dyn_offset = ABI._deserialize_int(buf[offset : offset + 32])
            dyn_offset = to_constant(dyn_offset)
            size = ABI._deserialize_int(buf[dyn_offset : dyn_offset + 32])
            result = buf[dyn_offset + 32 : dyn_offset + 32 + size]
        elif ty[0] in ("tuple"):
            result = ()
            for ty_i in ty[1]:
                result += (ABI._deserialize(ty_i, buf, offset),)
                offset += ABI._type_size(ty_i)
        elif ty[0] in ("array"):
            result = []
            dyn_offset = ABI._deserialize_int(buf[offset : offset + 32])
            dyn_offset = to_constant(dyn_offset)
            rep = ty[1]
            ty_size = ABI._type_size(ty[2])
            if rep is None:
                rep = ABI._deserialize_int(buf[dyn_offset : dyn_offset + 32])
                dyn_offset += 32
            for _ in range(rep):
                result.append(ABI._deserialize(ty[2], buf, dyn_offset))
                dyn_offset += ty_size
        else:
            raise NotImplementedError(f"Could not deserialize type: {ty[0]}")

        return result

    @staticmethod
    def _serialize_uint(value, size=32, padding=0):
        """
        Translates a python integral or a BitVec into a 32 byte string, MSB first
        """
        if size <= 0 or size > 32:
            raise ValueError

        from .account import EVMAccount  # because of circular import

        if not isinstance(value, (int, BitVec, EVMAccount)):
            raise ValueError
        if issymbolic(value):
            # Help mypy out. Can remove this by teaching it how issymbolic works
            assert isinstance(value, BitVec)
            # FIXME This temporary array variable should be obtained from a specific constraint store
            buffer = ArrayVariable(
                index_bits=256, index_max=32, value_bits=8, name="temp{}".format(uuid.uuid1())
            )
            if value.size <= size * 8:
                value = Operators.ZEXTEND(value, size * 8)
            else:
                # automatically truncate, e.g. if they passed a BitVec(256) for an `address` argument (160 bits)
                value = Operators.EXTRACT(value, 0, size * 8)
            buffer = buffer.write_BE(padding, value, size)
        else:
            value = int(value)
            buffer = bytearray()
            for _ in range(padding):
                buffer.append(0)
            for position in reversed(range(size)):
                buffer.append(Operators.EXTRACT(value, position * 8, 8))
            buffer = bytes(buffer)
        assert len(buffer) == size + padding
        return buffer

    @staticmethod
    def _serialize_int(value: typing.Union[int, BitVec], size=32, padding=0):
        """
        Translates a signed python integral or a BitVec into a 32 byte string, MSB first
        """
        if size <= 0 or size > 32:
            raise ValueError
        if not isinstance(value, (int, BitVec)):
            raise ValueError
        if issymbolic(value):
            # Help mypy out. Can remove this by teaching it how issymbolic works
            assert isinstance(value, BitVec)
            buf = ArrayVariable(
                index_bits=256, index_max=32, value_bits=8, name="temp{}".format(uuid.uuid1())
            )
            value = Operators.SEXTEND(value, value.size, size * 8)
            return ArrayProxy(buf.write_BE(padding, value, size))
        else:
            buf_arr = bytearray()
            for _ in range(padding):
                buf_arr.append(0)

            for position in reversed(range(size)):
                buf_arr.append(Operators.EXTRACT(value, position * 8, 8))
            return bytes(buf_arr)

    @staticmethod
    def _readBE(data, nbytes, padding=False, offset=0):
        """

        :param data:
        :param nbytes:
        :param padding: If True, treat data as padded at the beginning to multiple of 32
        :param offset:
        :return:
        """
        start = offset
        size = nbytes

        if padding:
            start += 32 - nbytes

        pos = start

        values = []
        while pos < start + size:
            if pos >= len(data):
                values.append(0)
            else:
                values.append(data[pos])
            pos += 1
        return Operators.CONCAT(nbytes * 8, *values)

    @staticmethod
    def _deserialize_uint(
        data: typing.Union[bytearray, bytes, Array], nbytes=32, padding=0, offset=0
    ):
        """
        Read a `nbytes` bytes long big endian unsigned integer from `data` starting at `offset`

        :param data: sliceable buffer; symbolic buffer of Eth ABI encoded data
        :param nbytes: number of bytes to read starting from least significant byte
        :rtype: int or Expression
        """
        assert isinstance(data, (bytearray, bytes, Array))
        value = ABI._readBE(data, nbytes, padding=True, offset=offset)
        value = Operators.ZEXTEND(value, (nbytes + padding) * 8)
        return value

    @staticmethod
    def _deserialize_int(data: typing.Union[bytearray, bytes, Array], nbytes=32, padding=0):
        """
        Read a `nbytes` bytes long big endian signed integer from `data` starting at `offset`

        :param data: sliceable buffer; symbolic buffer of Eth ABI encoded data
        :param nbytes: number of bytes to read starting from least significant byte
        :rtype: int or Expression
        """
        assert isinstance(data, (bytearray, bytes, Array))
        value = ABI._readBE(data, nbytes, padding=True)
        value = Operators.SEXTEND(value, nbytes * 8, (nbytes + padding) * 8)
        if not issymbolic(value):
            # sign bit on
            if value & (1 << (nbytes * 8 - 1)):
                value = -(((~value) + 1) & ((1 << (nbytes * 8)) - 1))
        return value
