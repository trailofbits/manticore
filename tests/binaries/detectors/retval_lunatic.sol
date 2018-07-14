pragma solidity ^0.4.24;

contract DetectThis{

  bool flag;

  function call() public pure{
    assert(false);
  }

  function callchecked() public {
    bool retval;
    flag = true;
    retval = address(this).call.value(0)(bytes4(keccak256("call()")));
    if (retval && retval)
        assert (true);
    else
        assert(false);
    flag = false;
  }

}
