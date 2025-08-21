pragma solidity ^0.4.24;
/*
A fair use of delegatecall instruction is inserted by the solidity compiler for
implementing libraries. This is an ok use of delegatecall.
*/

library Lib {
  
  struct Data {uint val;}

  function set(Data storage self, uint new_val) public{
    self.val = new_val;      
  }
}

contract DetectThis {
    Lib.Data public myVal;

    function () public payable{
        Lib.set(myVal, msg.value);
    }
}
