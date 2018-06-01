//Single transaction overflow
//Post-transaction effect: overflow never escapes function

pragma solidity ^0.4.19;

contract Benchmark {
    uint public count = 1;

    function run(uint256 input) public {
        uint res = count - input;
    }
}