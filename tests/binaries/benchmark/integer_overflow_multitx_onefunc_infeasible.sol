//Multi-transactional, single function
//Overflow infeasible because arithmetic instruction not reachable

pragma solidity ^0.4.19;

contract Benchmark {
    uint256 private initialized = 0;
    uint256 public count = 1;

    function run(uint256 input) public {
        if (initialized == 0) {
            return;
        }

        count -= input;
    }
}
