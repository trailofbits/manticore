/*
   Example contract - True Negative, Potential false positive
   The ether leak is reachable by non-creator if you set yourself as the owner, and the
   balance can be > 0, but the destination address can only ever be one thing.

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

  function withdrawfunds(address input_address) onlyOwner {
    address approved_recipient = 0x13371337;
    if (input_address == approved_recipient) {
        input_address.transfer(this.balance);
    }
  }

}
