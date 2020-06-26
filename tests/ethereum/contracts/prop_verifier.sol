contract Ownership{
    address owner = msg.sender;
    function Owner() public{
        owner = msg.sender;
    }
    modifier isOwner(){
        require(owner == msg.sender);
        _;
    }
}
contract Pausable is Ownership{
    bool is_paused;
    modifier ifNotPaused(){
        require(!is_paused);
        _;
    }
    function paused() isOwner public{
        is_paused = true;
    }
    function resume() isOwner public{
        is_paused = false;
    }
}
contract Token is Pausable{
    mapping(address => uint) public balances;
    function transfer(address to, uint value) ifNotPaused public{
        balances[msg.sender] -= value;
        balances[to] += value;
    }
}

contract TestToken is Token {
    constructor() public{
        balances[msg.sender] = 10000;
    }
    // the properties
    function crytic_test_balance() view public returns(bool){
        return balances[msg.sender] <= 10000;
    }
	function crytic_test_must_revert() view public returns(bool){
		require(false);
	}
	function crytic_failing_test_must_revert() view public returns(bool){
		require(true);
	}


}
