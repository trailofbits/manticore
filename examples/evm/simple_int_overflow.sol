pragma solidity ^0.4.15;
contract Overflow {
    uint private sellerBalance=0;
    
    function add(uint value) returns (bool, uint){
        sellerBalance += value; // complicated math with possible overflow

        // possible auditor assert
        assert(sellerBalance >= value); 
    }
}
