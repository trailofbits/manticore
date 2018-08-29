/*
   Example contract - True Positive
   The selfdestruct is reachable by non-creator if you set yourself as the owner.

   This should report a finding.
*/

pragma solidity ^0.4.24;

contract DetectThis {
  mapping (address => uint) balances;
  address owner;

  modifier onlyOwner {
    assert(msg.sender == owner);
    _;
  }

  function setOwner() public { // vulnerability here, anyone can be the owner
    owner = msg.sender;
  }

  function kill() public onlyOwner {
        selfdestruct(msg.sender);
  }
}