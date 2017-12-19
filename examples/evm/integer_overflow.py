from manticore.seth import ManticoreEVM, IntegerOverflow
m = ManticoreEVM()
m.register_detector(IntegerOverflow())

#And now make the contract account to analyze
source_code = '''
pragma solidity ^0.4.15;
contract Overflow {
    uint private sellerBalance=0;
    
    function add(uint value) returns (uint){
        sellerBalance += value; // complicated math with possible overflow

        // possible auditor assert
        assert(sellerBalance >= value); 
        return sellerBalance;
    } 
}
'''
#Initialize user and contracts
user_account = m.create_account(balance=1000)
contract_account = m.solidity_create_contract(source_code, owner=user_account, balance=0)

#First add won't overflow uint256 representation
contract_account.add(m.make_symbolic_value())

#Potential overflow
contract_account.add(m.make_symbolic_value())

#Let seth know we are not sending more transactions so it can output 
# info about running states and global statistics
m.finalize()
print "[+] Look for results in %s"% m.workspace




