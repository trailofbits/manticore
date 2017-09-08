pragma solidity ^0.4.13;

contract Test {
    mapping(address => uint) private balances;

    function Test(){
        balances[0x41424344454647484950] = 0x42424242;
    }
    
    function target(address key) returns (bool){
        if (balances[key] > 0)
            return true;
        else
            return false;            
    } 

}
