/*
   Example contract - True Negative
   The ether leak is not reachable by non-creator and there is no way to set
   yourself as the owner.

   This should NOT report a finding.
*/

pragma solidity ^0.4.24;

contract DetectThis {

  address private owner;

  modifier onlyOwner() {
    require(msg.sender == owner);
    _;
  }

  constructor () {
    owner = msg.sender;
  }

  function () payable { // makes it possible for contract to have balance > 0
  }

  function withdrawfunds() onlyOwner {
    msg.sender.transfer(this.balance);
  }

}
