pragma solidity ^0.4.24;
/*
There is a dangerous use of lowlevel instruction delegatecall in the fallback function.
The target address of the delegatecall hardcoded function selector of the delegate 
call is fully controlled by the user.
*/

contract DetectThis {
  address addr;
  constructor(){
     addr = address(this);
  }
  function setaddr(address a){
     addr = a;
  }

  function default_call(bytes data) public {
        require(msg.sender == address(this));
        //do legal stuff on bytes
  }

  function f() public {
        require(msg.data.length >=4);
        uint i;
        bytes memory new_calldata = new bytes(msg.data.length-4);

        for (i=0; i < msg.data.length-4; i++) {
            new_calldata[i] = msg.data[i+4];
        }

        require(address(0x41414141).delegatecall(new_calldata));
  }
}

