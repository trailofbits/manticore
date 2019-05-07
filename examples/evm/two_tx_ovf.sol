contract SymExExample {
    uint did_init = 0;

    event Log(string);

    // function id: 0x13371337
    function test_me(int input) {
        if (did_init == 0) {
            did_init = 1;
            emit Log("initialized");
            return;
        }

        if (input < 42) {
            // safe
            emit Log("safe");
            return;
        } else {
            // overflow possibly!
            int could_overflow = input + 1;
            emit Log("overflow");
        }

    }
}

