pragma solidity ^0.4.13;

contract Test {
    uint private sellerBalance=0;
    
    function Test(uint initialBalance){
        sellerBalance += initialBalance;
    }
    
    function target(uint value) returns (bool){

        sellerBalance += value; // possible overflow
        assert(sellerBalance >= value); // auditor assert
    } 

}
