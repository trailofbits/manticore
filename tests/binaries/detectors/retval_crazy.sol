pragma solidity ^0.4.24;

contract ReturnValue {


  function call() public pure{
    assert(false);
  }

  function callchecked() public {
    bool retval;
    bool retval2;
    retval = address(this).call.value(0)(bytes4(keccak256("call()")));
    retval2 = retval;
    if (retval2 == true)
        assert(false);
  }

}

