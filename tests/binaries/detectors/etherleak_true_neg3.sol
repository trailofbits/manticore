/*
   Example contract - True Negative, Potential false positive
   The ether leak is reachable by non-creator if you set yourself as the owner, and the
   balance can be > 0, but only 0 can ever be sent.

   This should NOT report a finding.
*/

pragma solidity ^0.4.24;

contract DetectThis {

  address private owner;

  modifier onlyOwner() {
    require(msg.sender == owner);
    _;
  }

  function fakeconstructor() payable {
    owner = msg.sender;
  }

  function withdrawfunds() onlyOwner {
    if (this.balance == 0) {
        msg.sender.transfer(this.balance);
    }
  }

}
