pragma solidity ^0.4.8;

contract Benchmark {
    mapping(string => uint256) map;

    function get(string key) public view returns (uint256) {
        return map[key];
    }
}