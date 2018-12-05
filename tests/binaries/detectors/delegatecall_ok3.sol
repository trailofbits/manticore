pragma solidity ^0.4.24;
/*
There is a dangerous use of lowlevel instruction delegatecall in the fallback function.
The address to which the delegatecall tx is sent is controlled by any user of this contract.
The storage variable `addr` is initialized to `this` and it CAN be modified.
The function selector of the delegate call is fully controlled by the user
*/

contract DetectThis {
  address addr;
  constructor() public{
     addr = address(this);
  }

  function default_call(bytes data) public {
        require(msg.sender == address(this));
        //do legal stuff on bytes
  }

  function () public {
  	require(msg.data.length > 4);
        uint i;
        bytes memory new_calldata = new bytes(msg.data.length);
        bytes4 func_id = bytes4(keccak256("default_call(bytes)"));
        for (i=0; i < 4; i++) {
            new_calldata[i] = func_id[i];
        }

        for (; i < msg.data.length; i++) {
            new_calldata[i] = msg.data[i];
        }

      require(address(this).delegatecall(new_calldata));

  }
}


