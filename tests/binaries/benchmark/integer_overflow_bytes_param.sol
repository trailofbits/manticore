pragma solidity ^0.4.8;

contract Benchmark {
    function get(bytes key) public pure returns (bytes32) {
        return keccak256(key);
    }
}