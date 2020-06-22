const Predeployed = artifacts.require("Predeployed");

module.exports = function (deployer) {
  deployer.deploy(Predeployed, "0x" + Buffer.from("constructor").toString("hex")).then(predeployed => {
    predeployed.set_y("0x" + Buffer.from("set_y").toString("hex"));
  });
};
