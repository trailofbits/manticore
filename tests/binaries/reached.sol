pragma solidity ^0.4.0;

library Manticore{


    function print(string message){
        // Print message 
        assembly {
            jump(0x4141414141414141414141414141414141414141)
        }
    }


    function terminate(string message){
        /*
         Terminate global manticore search with an optional termination message
        */
        assembly {
            jump(0x4141414141414141414141414141414141414141)
        }
    }

    function assume(bool constraint){
        /*
            Add constraint to the path constraint set
        */
        assembly {
            jump(0x4141414141414141414141414141414141414141)
        }
    }

    function make_symbolic_buffer(uint size) returns (bytes o_buffer) {
        /* make a free symbolic buffer */
        assembly {
            jump(0x4141414141414141414141414141414141414141)
        }
    }


    function make_symbolic_uint() returns (uint result) {
        /* make a free symbolic int */
        assembly {
            jump(0x4141414141414141414141414141414141414141)
        }
    }

    function is_symbolic(bytes mem) returns (bool result) {
        /* make a free symbolic buffer */
        assembly {
            jump(0x4141414141414141414141414141414141414141)
        }
    }
    function is_symbolic(uint mem) returns (bool result) {
        /* make a free symbolic buffer */
        assembly {
            jump(0x4141414141414141414141414141414141414141)
        }
    }

    function set_taint(bytes mem, uint taints) returns (bytes){
        /* Taint memory */
        assembly {
            jump(0x4141414141414141414141414141414141414141)
        }
    }

    function get_taint(bytes mem, uint size) returns (uint taints){
        /* read memory tains*/
        assembly {
            jump(0x4141414141414141414141414141414141414141)
        }
    }

    function make_testcase(){
        /* make a free symbolic int */
        assembly {
            jump(0x4141414141414141414141414141414141414141)
        }
    }

    function debug_print_constraints(){
        /* Print constraints in this path to stdout */
        assembly {
            jump(0x4141414141414141414141414141414141414141)
        }
    }

    function can_be_true(bool condition) returns (bool){
        /* Return True if condition can be true */
        assembly {
            jump(0x4141414141414141414141414141414141414141)
        }
    }

    function assert(bool condition, string message){
        /* Return True if condition can be true */
        assembly {
            jump(0x4141414141414141414141414141414141414141)
        }
    }

}

contract Reachable {
    uint storage_variable;

    function entry(uint input) {
        storage_variable = 0x585858;
        Manticore.print("Initializing!");
        if (Manticore.is_symbolic(storage_variable))
            Manticore.print("No! storage_variable should not be symbolic");

        //this.write_then_throw();
        this.call.gas(10001).value(msg.value)(bytes4(sha3("function write_then_throw()")));

        if (Manticore.is_symbolic(storage_variable))
            Manticore.print("Now It could be symbolic..");

        if (Manticore.can_be_true(storage_variable == 0x585858)){
            Manticore.terminate("Goal Found!");
        }
        
    }

    function write_then_throw() {
        storage_variable = 120;
        throw;
    }

}
