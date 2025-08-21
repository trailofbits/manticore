contract VulnerableToken{
  mapping(address => uint) private balances;
  address public owner;

  constructor() public {
    owner = msg.sender;
    balances[owner] = 1000000;    
  }

  function fund() payable public {
    uint n = msg.value;
    balances[msg.sender] += n;
    if (n < balances[owner]){
      balances[owner] += n;
    }
  }

  function burn(uint val) public {
    require(balances[msg.sender] > 0);
    balances[msg.sender] -= val;
  }

  function takeOwnership() public {
    require(balances[owner] < balances[msg.sender]);
    owner = msg.sender;
  }
}
