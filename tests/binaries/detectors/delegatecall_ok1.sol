pragma solidity ^0.4.24;
/*
There is a fair use of lowlevel instruction delegatecall in the fallback function.
It is effectively a CALL to `default_call` with the full calldata that was given to the fallback function
*/
contract DetectThis {

  function default_call(bytes data) public {
        require(msg.sender == address(this));
        //do legal stuff on bytes
  }

  function () public {
        bool retval = address(this).delegatecall(bytes4(keccak256("default_call(bytes)")), msg.data);
        require(retval);
  }

}
