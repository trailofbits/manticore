pragma solidity ^0.4.13;

contract Test {
    event Log(string);

    function target() payable public {
        if (msg.value > 10)
            Log("Value greater than 10");
        else
            Log("Value less or equal than 10");

    } 

}
