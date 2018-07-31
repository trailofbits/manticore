pragma solidity ^0.4.24;
/*
   Example contract - Potential False Positive
   The return value of a low level call IS checked after some manipulation.
   This should NOT report a finding.
*/

contract DetectThis{

  function call() public pure{
    assert(false);
  }

  function callchecked() public {
    bool retval;
    retval = address(this).call.value(0)(bytes4(keccak256("call()")));
    require(retval == true);
  }
}
