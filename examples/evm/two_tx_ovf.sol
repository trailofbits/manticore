pragma solidity ^0.4.15;

contract SymExExample {
    uint did_init = 0;

    event Log(string);

    // function id: 0x13371337
    function test_me(int input) {
        if (did_init == 0) {
            did_init = 1;
            Log("initialized");
            return;
        }

        if (input < 42) {
            // safe
            Log("safe");
            return;
        } else {
            // overflow possibly!
            int could_overflow = input + 1;
            Log("overflow");
        }

    }
}

