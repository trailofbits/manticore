contract C {

    function reveal(uint x, bytes32 hash) returns (bool) {
        if (sha3(x) == hash) {
            return true;
        }

        return false;
    }
}
