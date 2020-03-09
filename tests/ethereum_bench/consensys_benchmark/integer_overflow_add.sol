//Single transaction overflow
//Post-transaction effect: overflow escapes to publicly-readable storage

pragma solidity ^0.4.19;

contract Benchmark {
    uint public count = 1;

    function run(uint256 input) public {
        count += input;
    }
}