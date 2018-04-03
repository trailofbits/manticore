contract X {
  mapping(address => uint) private balance;
  function f(address z) returns (uint) { return balance[z]; }
}
contract C {
  X y;
  function C() {
    y = new X();
    uint z = y.f(0);
  }
}
