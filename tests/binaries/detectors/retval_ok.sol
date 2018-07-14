pragma solidity ^0.4.24;

contract DetectThis {


  function call() public pure{    
  }

  function callchecked() public {
    this.call();
  }

}
