pragma solidity ^0.4.24;

contract Overflow {
    uint private sellerBalance=10;
    
    function add(uint value) public {
        sellerBalance += value; // complicated math with possible overflow

        // possible auditor assert
        assert(sellerBalance >= value);
    }
}
