contract Maze {
    event Log(string);
    uint constant size = 4;
    uint16[size] maze;
    uint8 x = 0;
    uint8 y = 0;
    constructor(uint16[size] memory _maze) public {
        assert(bit(0) != 0);
        maze = _maze;
        assert(!wall(x, y));
    }
    function move(uint256 _dir) external {
        require(!win(), "You already won!");
        int128 dx = 0;
        int128 dy = 0;
        if (_dir == uint8(byte('E'))) {
            dx = 1;
        } else if (_dir == uint8(byte('N'))) {
            dy = -1;
        } else if (_dir == uint8(byte('S'))) {
            dy = 1;
        } else if (_dir == uint8(byte('W'))) {
            dx = -1;
        } else {
            require(false, "Invalid direction.");
        }
        require(x != 0 || dx >= 0, "At left boundary.");
        require(y != 0 || dy >= 0, "At upper boundary.");
        require(x != size - 1 || dx <= 0, "At right boundary.");
        require(y != size - 1 || dy <= 0, "At lower boundary.");
        require(!wall(x + uint8(dx), y + uint8(dy)), "Ouch! You bumped into a wall.");
        fill(x, y);
        x += uint8(dx);
        y += uint8(dy);
        if (win()) {
            emit Log("You won!");
        }
        assert(!wall(x, y));
    }
    function wall(uint8 _x, uint8 _y) internal view returns(bool) {
        return (maze[_y] & bit(_x)) != 0;
    }
    function fill(uint8 _x, uint8 _y) internal {
        maze[_y] |= bit(_x);
    }
    function bit(uint8 _x) internal pure returns(uint16) {
        return uint16(1 << (4 * ((size - 1) - _x)));
    }
    function win() internal view returns(bool) {
        return x == size - 1 && y == size - 1;
    }
}
