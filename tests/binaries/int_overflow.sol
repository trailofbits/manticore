contract IntOverflowUnderflow {
    uint global;

    function intoverflow_add(uint input) {
        uint local = input + 1;
    }

    function intoverflow_mul(uint input) {
        uint local = input * 2;
    }

    function intunderflow(uint input) {
        uint local = input - 1;
    }

    function gintoverflow_add(uint input) {
        global = input + 1;
    }

    function gintoverflow_mul(uint input) {
        global = input * 2;
    }

    function gintunderflow(uint input) {
        global = input - 1;
    }

}
