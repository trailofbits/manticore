const Maze = artifacts.require("Maze");

module.exports = function (deployer) {
  deployer.deploy(Maze, [
    "0x0000",
    "0x0101",
    "0x0100",
    "0x0110",
  ]);
};
