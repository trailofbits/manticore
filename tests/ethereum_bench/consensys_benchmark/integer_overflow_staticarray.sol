pragma solidity ^0.4.11;
contract Benchmark {
    uint256[6] private numbers;

    function get(uint256 i) public returns(uint256) {
        require(i < 6);
        return numbers[i];
    }
}