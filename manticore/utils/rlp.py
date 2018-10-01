# -*- coding: utf-8 -*-

import collections.abc

def int_to_bytes(n):
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')

def rlp_encode(item):
    if item is None or item == 0:
        return b'\x80'
    elif isinstance(item, str):
        return rlp_encode(item.encode('utf8'))
    elif isinstance(item, bytearray) or isinstance(item, bytes):
        if len(item) == 1 and item[0] < 0x80:
            return item
        else:
            return encode_length(len(item), 0x80) + item
    elif isinstance(item, collections.abc.Sequence):
        output = b''.join(map(rlp_encode, item))
        return encode_length(len(output), 0xC0) + output
    elif isinstance(item, int) or isinstance(item, long):
        return rlp_encode(int_to_bytes(item))
    else:
        raise Exception("Cannot encode object of type %s" % type(item).__name__)

def encode_length(length, offset):
    if length < 56:
         return int_to_bytes(length + offset)
    elif length < 256**8:
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
            ([ "cat", "dog" ], [ 0xc8, 0x83, 'c', 'a', 't', 0x83, 'd', 'o', 'g' ]),
            ('', [ 0x80 ]),
            ([], [ 0xc0 ]),
            (0, [ 0x80 ]),
            ('\x00', [ 0x00 ]),
            (15, [ 0x0f ]),
            (1024, [ 0x82, 0x04, 0x00 ]),
            ([ [], [[]], [ [], [[]] ] ], [ 0xc7, 0xc0, 0xc1, 0xc0, 0xc3, 0xc0, 0xc1, 0xc0 ]),
            (LOREM_IPSUM, [ 0xb8, 0x38 ] + list(LOREM_IPSUM))
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
    
