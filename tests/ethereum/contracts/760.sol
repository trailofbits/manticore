contract TEST {
    function Test_SignedInteger_AdditionOverflow(int x) public {
        int y = x + x;
        assert(y > 0);
    }
}
