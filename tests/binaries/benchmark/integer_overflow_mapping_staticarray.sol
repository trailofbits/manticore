//storage key for tuples[k].a calculated as
//  keccak(bytes32(k) + bytes32(position['map']))+offset['a']
pragma solidity ^0.4.11;

contract Benchmark {
    mapping(uint256 => bytes2) map;

    function init(uint256 k) public {
        map[k] = 0x1A;
    }
}
