/*
   Example contract - True Positive
   The argument ether leak is reachable by non-creator if you set yourself as the owner.

   This should report a finding.
*/

pragma solidity ^0.4.24;

contract DetectThis {

  address private owner;

  modifier onlyOwner() {
    require(msg.sender == owner);
    _;
  }

  function fakeconstructor() payable { // makes it possible for contract to have balance > 0
    owner = msg.sender;
  }

  function withdrawfunds(address attacker) onlyOwner {
    if (attacker != msg.sender) {
        attacker.transfer(this.balance);
    }
  }

}
