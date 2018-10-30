pragma solidity ^0.4.19;
/*
    Example contract - True Positive

    Taken from https://consensys.github.io/smart-contract-best-practices/known_attacks/#cross-function-race-conditions

    In this case, the attacker calls transfer() when their code is executed on the external call in withdrawBalance.
    Since their balance has not yet been set to 0, they are able to transfer the tokens even though they already
    received the withdrawal. This vulnerability was also used in the DAO attack.

    This should report a finding.
*/

contract DetectThis {
    mapping (address => uint) private userBalances;

    function transfer(address to, uint amount) {
        if (userBalances[msg.sender] >= amount) {
           userBalances[to] += amount;
           userBalances[msg.sender] -= amount;
        }
    }

    function withdrawBalance() public {
        uint amountToWithdraw = userBalances[msg.sender];
        // At this point, the caller's code is executed, and can call transfer()
        require(msg.sender.call.value(amountToWithdraw)());
        userBalances[msg.sender] = 0;
    }
}