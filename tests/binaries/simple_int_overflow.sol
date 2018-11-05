pragma solidity ^0.4.15;

contract Overflow {
    uint private sellerBalance=0;
    
    function add(uint value) public {
        sellerBalance += value; // complicated math with possible overflow

        // possible auditor assert
        assert(sellerBalance >= value);
    }
}
