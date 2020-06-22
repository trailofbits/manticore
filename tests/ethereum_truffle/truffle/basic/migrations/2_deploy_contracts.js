const Basic = artifacts.require("Basic");

module.exports = function (deployer) {
  deployer.deploy(Basic, "0x" + Buffer.from("constructor").toString("hex")).then(basic => {
    basic.set_y("0x" + Buffer.from("set_y").toString("hex"));
  });
};
