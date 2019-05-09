// Smart contract based on a classic symbolic execution example from slides
// by Michael Hicks, University of Maryland.
// https://www.cs.umd.edu/~mwh/se-tutorial/symbolic-exec.pdf

contract SymExExample {


    function test_me(int a, int b, int c) public pure {
        int x = 0;
        int y = 0;
        int z = 0;

        if (a != 0) {
            x = -2;
        }

        if (b < 5) {
            if (a == 0 && c != 0) {
                y = 1;
            }
            z = 2;
        }

        // will fail when: a == 0 && b < 5 && c != 0
        assert(x + y + z != 3);
    }

}
