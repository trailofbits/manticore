# -*- coding: utf-8 -*-

import collections.abc


def int_to_bytes(n):
    if n == 0:
        return b'\0'
    else:
        return n.to_bytes((n.bit_length() + 7) // 8, 'big')


def rlp_encode(item):
    r''' Recursive Length Prefix Encoding
        :param item: the object to encode, either a string, bytes, bytearray, int, long, or sequence

    https://github.com/ethereum/wiki/wiki/RLP

    >>> rlp_encode('dog')
    b'\x83dog'

    >>> rlp_encode([ 'cat', 'dog' ])
    b'\xc8\x83cat\x83dog'

    >>> rlp_encode('')
    b'\x80'

    >>> rlp_encode([])
    b'\xc0'

    >>> rlp_encode(0)
    b'\x80'

    >>> rlp_encode('\x00')
    b'\x00'

    >>> rlp_encode(15)
    b'\x0f'

    >>> rlp_encode(1024)
    b'\x82\x04\x00'

    >>> rlp_encode([ [], [[]], [ [], [[]] ] ])
    b'\xc7\xc0\xc1\xc0\xc3\xc0\xc1\xc0'

    '''
    if item is None or item == 0:
        ret = b'\x80'
    elif isinstance(item, str):
        ret = rlp_encode(item.encode('utf8'))
    elif isinstance(item, (bytearray, bytes)):
        if len(item) == 1 and item[0] < 0x80:
            # For a single byte whose value is in the [0x00, 0x7f] range, that byte is its own RLP encoding.
            ret = item
        else:
            ret = encode_length(len(item), 0x80) + item
    elif isinstance(item, collections.abc.Sequence):
        output = b''.join(map(rlp_encode, item))
        ret = encode_length(len(output), 0xC0) + output
    elif isinstance(item, int):
        ret = rlp_encode(int_to_bytes(item))
    else:
        raise Exception("Cannot encode object of type %s" % type(item).__name__)
    return ret


def encode_length(length, offset):
    if length < 56:
        # if a string is 0-55 bytes long,
        # the RLP encoding consists of a single byte with value 0x80
        # plus the length of the string followed by the string.
        return int_to_bytes(length + offset)
    elif length < 256**8:
        # if a string is more than 55 bytes long, the RLP encoding consists of
        # a single byte with value 0xb7 plus the length in bytes of the length of the string in binary form,
        # followed by the length of the string, followed by the string.
        # For example, a length-1024 string would be encoded as \xb9\x04\x00 followed by the string.
        binary = to_binary(length)
        return int_to_bytes(len(binary) + offset + 55) + binary
    else:
        raise Exception("length must be less than %d" % 256**8)


def to_binary(x):
    if x == 0:
        return b''
    else:
        return to_binary(int(x / 256)) + int_to_bytes(x % 256)


if __name__ == "__main__":
    import sys
    passed = True

    def to_list(encoded):
        ret = []
        for c in encoded:
            if c >= ord(' ') and c <= ord('~'):
                ret.append(chr(c))
            else:
                ret.append(c)
        return ret

    def to_int(exp):
        if isinstance(exp, str):
            return ord(exp)
        else:
            return exp
    LOREM_IPSUM = "Lorem ipsum dolor sit amet, consectetur adipisicing elit"
    for item, expected in (
            ('dog', [0x83, 'd', 'o', 'g']),
            (['cat', 'dog'], [0xc8, 0x83, 'c', 'a', 't', 0x83, 'd', 'o', 'g']),
            ('', [0x80]),
            ([], [0xc0]),
            (0, [0x80]),
            ('\x00', [0x00]),
            (15, [0x0f]),
            (1024, [0x82, 0x04, 0x00]),
            ([[], [[]], [[], [[]]]], [0xc7, 0xc0, 0xc1, 0xc0, 0xc3, 0xc0, 0xc1, 0xc0]),
            ('1024 Bytes Long' + '\0' * 1009, [0xb9, 0x04, 0x00] + list('1024 Bytes Long' + '\0' * 1009)),
            (LOREM_IPSUM, [0xb8, 0x38] + list(LOREM_IPSUM))
    ):
        sys.stdout.write("Testing %s" % str(item))
        expected_bytes = bytes(map(to_int, expected))
        encoding = rlp_encode(item)
        if encoding == expected_bytes:
            sys.stdout.write(' ✓\n')
        else:
            sys.stdout.write(" ✗ expected %s but got %s\n" % (expected, to_list(encoding)))
            passed = False

    if passed:
        exit(0)
    else:
        exit(1)
