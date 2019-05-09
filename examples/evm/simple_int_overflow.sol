contract Overflow {
    uint private sellerBalance=0;
    
    function add(uint value) returns (bool, uint){
        sellerBalance += value; // complicated math with possible overflow

        // possible auditor assert
        assert(sellerBalance >= value); 
    }
}
