pragma solidity ^0.4.24;
/*
There is a dangerous use of lowlevel instruction delegatecall in the fallback function.
The address to which the delegatecall tx is sent is controlled by any user of this contract.
The storage variable `addr` is initialized to `this` and it CAN be modified.
The function selector of the delegate call is fully controlled by the user
*/

contract DetectThis {
  address addr;
  constructor(){
     addr = address(this);
  }
  function setaddr(address a){
     addr = a;
  }

  function default_call(bytes32 data) public {
        require(msg.sender == address(this));
        //do legal stuff on bytes
  }

  function f(bytes4 selector, bytes32 data) public {
      uint calldata0;
      assembly {
          calldata0 := calldataload(0)
      }
      require(selector != bytes4(calldata0 >> ((32 - 4)*8))); // Don't recurse.
      require(addr.delegatecall(selector, data));
  }
}
