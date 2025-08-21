pragma solidity >=0.4.24 <0.9.0;

contract Adder {
    function incremented(uint value) public pure returns (uint){
        if (value == 1)
            revert();
        return value + 1;
    }
}
