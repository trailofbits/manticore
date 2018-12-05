pragma solidity ^0.4.24;
/*
   Example contract - True Negative
   The return value of a low level call IS checked via solidity injected code.
   This should NOT report a finding.
*/
contract DetectThis {

  function call() public pure{
     assert(false);
  }

  function callchecked() public {
    this.call();
  }

}
