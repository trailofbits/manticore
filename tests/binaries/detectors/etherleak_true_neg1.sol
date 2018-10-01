/*
   Example contract - True Negative, Potential false positive
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

  function fakeconstructor () { // writes to owner storage, but not exploitably
    owner = 2;
  }

  function () payable { // makes it possible for contract to have balance > 0
  }

  function withdrawfunds() onlyOwner {
    msg.sender.transfer(this.balance);
  }

}
