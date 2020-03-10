//Multi-transactional, single function
//Arithmetic instruction reachable

pragma solidity ^0.4.19;

contract Benchmark {
    uint256 private initialized = 0;
    uint256 public count = 1;

    function run(uint256 input) public {
        if (initialized == 0) {
            initialized = 1;
            return;
        }

        count -= input;
    }
}
