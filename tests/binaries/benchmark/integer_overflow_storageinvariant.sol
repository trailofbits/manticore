//No underflow because of credit/balance invariant: sum (credit.values) = balance
pragma solidity ^0.4.19;

contract Benchmark {
    mapping (address => uint) credit;
    uint balance;

    function withdrawAll() public {
        uint oCredit = credit[msg.sender];
        if (oCredit > 0) {
            credit[msg.sender] = 0;
            balance -= oCredit;
            msg.sender.transfer(oCredit);
        }
    }

    function deposit() public payable {
        credit[msg.sender] += msg.value;
        balance += msg.value;
        require(balance < 1000);
    }
}