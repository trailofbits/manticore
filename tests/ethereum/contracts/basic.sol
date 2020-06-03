contract Basic {
    uint256 n;

    constructor(uint256 _n) public {
        n = _n;
    }

    function submit(uint256 _x) external {
        require(_x == n, "wrong value");
        n++;
    }
}
