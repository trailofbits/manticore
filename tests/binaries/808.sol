library X {
  function f(uint z) returns (uint) { return 2*z; }
}
contract C {
  function C() {
    uint z = X.f(0);
  }
}
