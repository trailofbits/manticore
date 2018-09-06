pragma solidity ^0.4.24;
/*
   Example contract - True Positive
   The return value of a low level call is simply ignored.
   We assume developer always want to check/bubble up exceptions.
   This should report a finding.
*/
contract DetectThis {

  function call() public pure{
    assert(false);
  }

  function callchecked() public {
    address(this).call.value(0)(bytes4(keccak256("call()")));
  }

}
