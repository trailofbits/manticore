contract Test {
    event Log(string);
    mapping(address => uint) private balances;

    function Test() {}
    function target1() public {} 
    function target2() internal {} 
    function target3() private {} 
    function() {}

}
