pragma solidity ^0.5.3;

contract Overflow {
    uint private sellerBalance=10;
    
    function add(uint value) public {
        sellerBalance += value; // complicated math with possible overflow

        // possible auditor assert
        assert(sellerBalance >= value);
    }
}
