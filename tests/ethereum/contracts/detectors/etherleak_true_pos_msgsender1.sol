/*
   Example contract - True Positive, Potential false negative
   The ether leak is reachable by non-creator if you set yourself as the owner by exploiting
   the set() function.

   NOTE: this currently requires the LoopDepthLimiter plugin to find quickly. This is due to the
   assignment to map.length.

   This should report a finding.
*/

pragma solidity ^0.4.24;

contract DetectThis {

  address private owner;
  uint256[] map;

  modifier onlyOwner() {
    require(msg.sender == owner);
    _;
  }

  function set(uint256 key, uint256 value) public payable { // you can use this to overwrite owner // makes it possible for contract to have balance > 0
    // Expand dynamic array as needed
    if (map.length <= key) {
      map.length = key + 1;
    }

    map[key] = value;
  }

  function withdrawfunds() onlyOwner {
    msg.sender.transfer(this.balance);
  }

}
