/*
   Example contract - True Negative
   The ether leak is reachable by non-creator if you set yourself as the owner, BUT the balance
   can never be > 0.

   This should NOT report a finding.
*/

pragma solidity ^0.4.24;

contract DetectThis {

  address private owner;

  modifier onlyOwner() {
    require(msg.sender == owner);
    _;
  }

  function fakeconstructor() {
    owner = msg.sender;
  }

  function withdrawfunds() onlyOwner {
    msg.sender.transfer(this.balance);
  }

}
