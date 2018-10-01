/*
   Example contract - True Negative, Potential False Positive
   The selfdestruct is not reachable by non-creator and there is no way to set
   yourself as the owner.

   This should NOT report a finding.
*/

pragma solidity ^0.4.24;

contract DetectThis {
  mapping (address => uint) balances;
  address owner;

  modifier onlyOwner {
    assert(msg.sender == owner);
    _;
  }
  function fakeSetOwner() { // writes to owner storage, but not exploitably
    owner = 2;
  }

  function kill() public onlyOwner {
        selfdestruct(msg.sender);
  }
}
