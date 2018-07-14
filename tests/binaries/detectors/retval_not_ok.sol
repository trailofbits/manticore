pragma solidity ^0.4.24;

contract DetectThis {

  bool flag;

  function call() public pure{
    assert(false);
  }

  function callchecked() public {
    flag = true;
    address(this).call.value(0)(bytes4(keccak256("call()")));
    flag = false;
  }

}
