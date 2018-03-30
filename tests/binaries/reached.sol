contract IntOverflowUnderflow {
    uint storage_variable;

    function entry(uint input) {
        storage_variable = 0x585858;
        write_then_throw();
        if (storage_variable != 0x585858){
            assembly {
               jump ( 0x4141414141414141414141414141414141414141 )
            }
        }
        else{ 
            assembly {
               jump ( 0x4242424242424242424242424242424242424242 )
            }
        }
           
    }

    function write_then_throw() {
        storage_variable = 120;
        assert(1==0);
    }

}
