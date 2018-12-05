//Multi-transactional, multi-function
//Arithmetic instruction reachable

pragma solidity ^0.4.19;

contract Benchmark {
    uint256 private initialized = 0;
    uint256 public count = 1;

    function init() public {
        initialized = 1;
    }

    function run(uint256 input) {
        if (initialized == 0) {
            return;
        }

        count -= input;
    }
}