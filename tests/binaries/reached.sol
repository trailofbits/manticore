pragma solidity ^0.4.0;

library Manticore{
    function system(uint funcid){
        assembly {
            jump(0x4141414141414141414141414141414141414141)
        }
    }

    function terminate_search(string message){
        system(1);
    }

    function terminate_state(string message){
        system(2);
    }

    function print(string){
        system(3);
    }

    function assume(bool){
        system(4);
    }

    function symbolic_buffer(uint size) returns (bytes o_buffer) {
        system(5);
    }

    function goal(bool condition){
        if (condition){
            terminate_search("Goal achieved!");
        }
    }

    function avoid(bool condition){
        if (condition){
            terminate_search("Forbidden spot reached. Aborting search!");
        }
    }

}

contract Reachable {
    uint storage_variable;

    function entry(uint input) {
        storage_variable = 0x585858;
        //this.write_then_throw();
        this.call.gas(10000).value(msg.value)(bytes4(sha3("function write_then_throw()")));

        Manticore.goal(storage_variable == 0x585858);
        Manticore.avoid(storage_variable != 0x585858);
        
    }

    function write_then_throw() {
        storage_variable = 120;
        throw;
    }

}
