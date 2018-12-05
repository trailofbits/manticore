contract C {
    uint public n=0;
    function f() public{
        n = block.number;
    }
}
