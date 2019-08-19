contract DetectThis {
    event Log(string);
    function foo() payable public{
        uint256 eth2;
        uint256 eth = msg.value;
        eth2 = address(msg.sender).balance;
        if(eth2 >= eth){
            emit Log("Found a bug");
        }
    }
}

