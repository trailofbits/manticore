pragma solidity ^0.4.19;

contract Benchmark {
    uint256 private param;

    function Benchmark(uint256 _param) public {
        require(_param > 0);
        param = _param;
    }

    function run() {
        assert(param > 0);
    }

    function set(uint256 _param) {
        param = _param;
    }


}