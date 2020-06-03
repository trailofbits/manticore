contract Sqrt {
    uint256 n;
    mapping(address => bytes32) commits;

    constructor(uint256 _n) public payable {
        require(0 < _n, "not positive");
        n = _n;
    }

    function commit(bytes32 _value) external {
        commits[msg.sender] = _value;
    }

    function reveal(uint256 _x, uint256 _salt) external {
        require(keccak256(abi.encode(_x, _salt)) == commits[msg.sender], "not committed to");
        require(0 < _x, "not positive");
        require(_x * _x <= n, "too big");
        require(n < (_x + 1) * (_x + 1), "too small");
        n = 0;
        msg.sender.transfer(address(this).balance);
    }
}
