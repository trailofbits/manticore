//Dynamic storage array with packing
//
pragma solidity ^0.4.11;

contract Benchmark {

    uint128[] private s;

    function init() public {
        s.length = 4;
        s[0] = 0xAA;
        s[1] = 0xBB;
        s[2] = 0xCC;
        s[3] = 0xDD;
    }
}
