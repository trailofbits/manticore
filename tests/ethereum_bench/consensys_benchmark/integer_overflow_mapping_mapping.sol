//storage key for tuples[k].a calculated as
//  keccak(bytes32(k) + bytes32(position['tuples']))+offset['a']
pragma solidity ^0.4.11;

contract Benchmark {
    mapping(uint256 => mapping (uint256 => Tuple)) maps;

    struct Tuple {
        uint256 a;
        uint256 b;
    }

    function init(uint256 k) {
        maps[k][k].b = 0x1A;
    }
}