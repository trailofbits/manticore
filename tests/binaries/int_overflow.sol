contract IntOverflowUnderflow {
    function intoverflow_add(uint input) {
        uint local = input + 1;
    }

    function intoverflow_mul(uint input) {
        uint local = input * 2;
    }

    function intunderflow(uint input) {
        uint local = input - 1;
    }
}