pragma solidity ^0.4.19;
/*
    Example contract - True Positive
    There can be a race condition between storing an address with `setStoredAddress`
    and using it in `callStoredAddress`.

    An attacker seeing a `setStoredAddress` that is supposed to "change something important"
    might send a tx with more gas and execute `callStoredAddress` before one changes the state.sss

    This should report a finding.
*/

contract DetectThis {
	address public stored_address;

	function callStoredAddress() {
	    stored_address.call();
	}

	function setStoredAddress(address addr) {
	    stored_address = addr;
	}
}