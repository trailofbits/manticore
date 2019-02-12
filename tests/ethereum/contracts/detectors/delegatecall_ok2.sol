pragma solidity ^0.4.24;
/*
There is a fair use of lowlevel instruction delegatecall in the fallback function.
It is effectively a CALL to `this.default_call` with a concrete data.
The storage variable `addr` is initialized to `this` and can not be modified.
*/

contract DetectThis {
  address addr;
  constructor(){
        addr = address(this);
  }

  function default_call(bytes data) public {
        require(msg.sender == address(this));
        //do legal stuff on bytes
  }

  function () public {
        bool retval = addr.delegatecall(bytes4(keccak256("default_call(bytes)")), "Concrete values!");
        require(retval);
  }

}
