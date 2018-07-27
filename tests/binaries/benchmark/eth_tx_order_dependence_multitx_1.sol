pragma solidity ^0.4.16;

contract Benchmark {
    address public owner;
    bool public claimed;
    uint256 public reward;
    bool public freezeReward;

    function Benchmark() public {
        owner = msg.sender;
    }

    function setReward() public payable {
        require (!claimed);
        require (!freezeReward);
        require(msg.sender == owner);

        owner.transfer(reward);
        reward = msg.value;
    }

    function freezeReward() public {
        freezeReward = true;
    }

    function claimReward(uint256 submission) {
        require (freezeReward);
        require (!claimed);
        require(submission < 10);

        msg.sender.transfer(reward);
        claimed = true;
    }
}