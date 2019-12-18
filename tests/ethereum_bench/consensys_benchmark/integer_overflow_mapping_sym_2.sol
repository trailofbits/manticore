pragma solidity ^0.4.11;

contract Benchmark {
    mapping(uint256 => uint256) map;

    function init(uint256 k, uint256 v) public {
        require(v < 10);
        map[k] = 10;
        map[k] -= v;
    }
}