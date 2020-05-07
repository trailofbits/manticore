contract Sqrt {
    uint256 n;

    constructor(uint256 _n) public payable {
        require(0 < _n, "not positive");
        n = _n;
    }

    function submit(uint256 _x) external {
        require(0 < _x, "not positive");
        require(_x * _x <= n, "too big");
        require(n < (_x + 1) * (_x + 1), "too small");
        n = 0;
        msg.sender.transfer(address(this).balance);
    }
}
