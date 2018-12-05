//Single transaction overflow
//Post-transaction effect: overflow never escapes to publicly-readable storage

pragma solidity ^0.4.19;

contract Benchmark {
    uint public count;

    function run(uint256 input) public {
        bool err;
        uint256 res = 1;

        (err, res) = minus(res, input);

        require(!err);
        count = res;
    }

    //from BasicMathLib
    function minus(uint256 a, uint256 b) private pure returns (bool err,uint256 res) {
        assembly {
            res := sub(a,b)
            switch eq(and(eq(add(res,b), a), or(lt(res,a), eq(res,a))), 1)
            case 0 {
                err := 1
                res := 0
            }
        }
    }
}