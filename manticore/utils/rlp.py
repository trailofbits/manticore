# -*- coding: utf-8 -*-

import collections

def rlp_encode(item):
    if item is None:
        return 0x80
    elif isinstance(item, str) or isinstance(item, bytearray):
        if len(item) == 1 and ord(item) < 0x80:
            return item
        else:
            return encode_length(len(item), 0x80) + item
    elif isinstance(item, collections.Sequence):
        output = ''.join(map(rlp_encode, item))
        return encode_length(len(output), 0xC0) + output
    elif isinstance(item, int) or isinstance(item, long):
        if item < 0x80:
            return chr(item)
        hex_str = hex(item)[2:]
        if len(hex_str) % 2:
            hex_str = "0%s" % hex_str
        return rlp_encode(hex_str.decode('hex'))
    else:
        raise Exception("Cannot encode object of type %s" % type(item).__name__)

def encode_length(length, offset):
    if length < 56:
         return chr(length + offset)
    elif length < 256**8:
         binary = to_binary(length)
         return chr(len(binary) + offset + 55) + binary
    else:
         raise Exception("length must be less than %d" % 256**8)

def to_binary(x):
    if x == 0:
        return ''
    else: 
        return to_binary(int(x / 256)) + chr(x % 256)

if __name__ == "__main__":
    import sys
    passed = True
    def to_list(encoded):
        ret = []
        for c in encoded:
            oc = ord(c)
            if oc >= ord(' ') and oc <= ord('~'):
                ret.append(c)
            else:
                ret.append(oc)
        return ret
    def to_str(exp):
        if isinstance(exp, str):
            return exp
        else:
            return chr(exp)
    LOREM_IPSUM = "Lorem ipsum dolor sit amet, consectetur adipisicing elit"
    for item, expected in (
            ('dog', [0x83, 'd', 'o', 'g']),
            ([ "cat", "dog" ], [ 0xc8, 0x83, 'c', 'a', 't', 0x83, 'd', 'o', 'g' ]),
            ('', [ 0x80 ]),
            ([], [ 0xc0 ]),
            ('\x00', [ 0x00 ]),
            (15, [ 0x0f ]),
            (1024, [ 0x82, 0x04, 0x00 ]),
            ([ [], [[]], [ [], [[]] ] ], [ 0xc7, 0xc0, 0xc1, 0xc0, 0xc3, 0xc0, 0xc1, 0xc0 ]),
            (LOREM_IPSUM, [ 0xb8, 0x38 ] + list(LOREM_IPSUM))
    ):
        sys.stdout.write("Testing %s" % item)
        expected_str = ''.join(map(to_str, expected))
        encoding = rlp_encode(item)
        if encoding == expected_str:
            sys.stdout.write(' ✓\n')
        else:
            sys.stdout.write(" ✗ expected %s but got %s\n" % (expected, to_list(encoding)))
            passed = False
    if passed:
        exit(0)
    else:
        exit(1)
    
