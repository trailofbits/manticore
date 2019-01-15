//storage key for tuples[i].a calculated as
//  keccak(bytes32(i) + bytes32(position['tuples']))+offset[a]
pragma solidity ^0.4.11;

contract Benchmark {
    mapping(uint256 => uint256) tuples;

    //tuple variable offset added to keccak(bytes32(key) + bytes32(position))
    function init(uint256 key) public {
        tuples[key] = 0x1A;
        //tuples[key].b = 0x1B;
        //tuples[key].c = 0x1C;
    }
}