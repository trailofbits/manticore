//Storage packing optimization stores a,b in a single 32-byte storage slot.
//solc generates MUL instruction that operates on compile-time constants to
//  extract variable a (or b) from packed storage slot.
pragma solidity ^0.4.11;
contract Benchmark {
    uint128 a;
    uint128 b;
    function C() public {
        a = 1;
        b = 2;
    }
}
