contract Predeployed {
    uint256 public x;
    uint256 public y;
    constructor(uint256 _x) public {
        x = _x;
    }
    function set_y(uint256 _y) external {
        y = _y;
    }
}
