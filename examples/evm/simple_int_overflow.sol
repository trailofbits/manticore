pragma solidity ^0.4.13;

contract Test {
    mapping(address => uint) private balances;

    function Test(){
        balances[0x414141414141] = 0x1;
    }
    
    function target(address key) returns (bool){
        if (balances[key] > 0)
            return true;
        else
            return false;            
    } 

}
