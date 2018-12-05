pragma solidity ^0.4.19;

contract Benchmark {
    function run(uint256 _param) public {
        require(_param > 0);
        assert(_param > 0);
    }
}