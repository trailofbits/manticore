pragma solidity ^0.4.24;
/*
   Example contract - Potential False Positive
   The return value of a low level call IS checked after some manipulation.
   This should NOT report a finding.
*/

contract DetectThis {

  function call() public pure{
    assert(false);
  }

  function callchecked() public {
    bool retval;
    bool retval2;
    retval = address(this).call.value(0)(bytes4(keccak256("call()")));
    retval2 = retval;
    if (retval2 == false)
        assert(false);
  }
}

