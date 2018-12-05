/*
   Example contract - True Positive, Potential False Negative
   The selfdestruct is reachable by non-creator if you set yourself as the owner by exploiting
   the set() function.

   NOTE: this currently requires the LoopDepthLimiter plugin to find quickly. This is due to the
   assignment to map.length.

   This should report a finding.
*/

pragma solidity ^0.4.24;

contract DetectThis {
  address owner;
  uint256[] map;

  modifier onlyOwner {
    assert(msg.sender == owner);
    _;
  }

  function set(uint256 key, uint256 value) public { // you can use this to overwrite owner
        // Expand dynamic array as needed
        if (map.length <= key) {
            map.length = key + 1;
        }

        map[key] = value;
  }

  function kill() public onlyOwner  {
        selfdestruct(msg.sender);
  }
}

