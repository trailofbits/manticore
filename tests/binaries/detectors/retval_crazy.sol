pragma solidity ^0.4.24;

contract DetectThis {

  bool flag;

  function call() public pure{
    assert(false);
  }

  function callchecked() public {
    bool retval;
    bool retval2;
    //flag = true;
    retval = address(this).call.value(0)(bytes4(keccak256("call()")));
    retval2 = retval;
    if (retval2)
        assert(false);
    //flag = false;
  }

}
