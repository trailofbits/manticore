contract Basic {
    uint256 x;
    uint256 y;
    constructor(uint256 _x) public {
        x = _x;
    }
    function set_y(uint256 _y) external {
        y = _y;
    }
    function guess_x(uint256 _x) external view {
        require(x == _x, "x != _x");
    }
    function guess_y(uint256 _y) external view {
        require(y == _y, "y != _y");
    }
}
