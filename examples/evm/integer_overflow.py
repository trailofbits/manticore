from manticore.seth import ManticoreEVM, IntegerOverflow
seth = ManticoreEVM()
seth.register_detector(IntegerOverflow())

#And now make the contract account to analyze
source_code = '''
pragma solidity ^0.4.15;
contract Overflow {
    uint private sellerBalance=0;
    
    function add(uint value) returns (bool){
        sellerBalance += value; // complicated math with possible overflow

        // possible auditor assert
        assert(sellerBalance >= value); 
    } 
}
'''
#Initialize user and contracts
user_account = seth.create_account(balance=1000)
contract_account = seth.solidity_create_contract(source_code, owner=user_account, balance=0)

#First add won't overflow uint256 representation
contract_account.add(seth.make_symbolic_value())

#Potential overflow
contract_account.add(seth.make_symbolic_value())

#Let seth know we are not sending more transactions so it can output 
# info about running states and global statistics
seth.finalize()
print "[+] Look for results in %s"% seth.workspace




