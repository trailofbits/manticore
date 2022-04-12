contract Adder {
    function incremented(uint value) public returns (uint){
        if (value == 1)
            revert();
        return value + 1;
    }
}
