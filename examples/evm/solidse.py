from manticore.seth import ManticoreEVM, calculate_coverage, ABI

################ Script #######################
seth = ManticoreEVM(procs=8)

seth.verbosity(0)
#And now make the contract account to analyze
# cat  | solc --bin 
source_code = file(sys.argv[1],'rb').read()

user_account = seth.create_account(balance=1000)
print "[+] Creating a user account", user_account

contract_account = seth.solidity_create_contract(source_code, owner=user_account)
print "[+] Creating a contract account", contract_account

attacker_account = seth.create_account(balance=1000)
print "[+] Creating a attacker account", attacker_account


last_coverage = None 
new_coverage = 0
tx_count = 0
while new_coverage != last_coverage and new_coverage < 100:

    symbolic_data = seth.make_symbolic_buffer(320)
    symbolic_value = seth.make_symbolic_value() 

    seth.transaction(caller=attacker_account,
                    address=contract_account,
                    data=symbolic_data,
                    value=symbolic_value )

    tx_count += 1
    last_coverage = new_coverage
    new_coverage = seth.global_coverage(contract_account)
    
    print "[+] Coverage after %d transactions: %d%%"%(tx_count, new_coverage)
    print "[+] There are %d reverted states now"% len(seth.terminated_state_ids)
    print "[+] There are %d alive states now"% len(seth.running_state_ids)

for state in seth.all_states:
    print "="*20
    blockchain = state.platform
    for tx in blockchain.transactions: #external transactions
        print "Transaction:"
        print "\tsort %s" % tx.sort    #Last instruction or type? TBD
        print "\tcaller 0x%x" % state.solve_one(tx.caller)  #The caller as by the yellow paper
        print "\taddress 0x%x" % state.solve_one(tx.address) #The address as by the yellow paper
        print "\tvalue: %d" % state.solve_one(tx.value)   #The value as by the yellow paper
        print "\tcalldata: %r" % state.solve_one(tx.data)
        print "\tresult: %s" % tx.result  #The result if any RETURN or REVERT
        print "\treturn_data: %r" % state.solve_one(tx.return_data)  #The returned data if RETURN or REVERT

        metadata = seth.get_metadata(tx.address)
        if tx.sort == 'Call':
            if metadata is not None:
                function_id = tx.data[:4]  #hope there is enough data
                function_id = state.solve_one(function_id).encode('hex')
                signature = metadata.get_func_signature(function_id)
                print "\tparsed calldata", ABI.parse(signature, tx.data) #func_id, *function arguments
                if tx.result == 'RETURN':
                    ret_types = metadata.get_func_return_types(function_id)
                    print '\tparsed return_data', ABI.parse(ret_types, tx.return_data) #function return

        if tx.result in ('THROW', 'REVERT', 'SELFDESTRUCT'):
            if metadata is not None:
                address, offset = state.context['seth.trace'][-1]
                print metadata.get_source_for(offset)
            

    #the logs
    for log_item in blockchain.logs:
        print "log address", log_item.address
        print "memlog", log_item.memlog
        for topic in log_item.topics:
            print "topic", topic

    for address in blockchain.deleted_addresses:
        print "deleted address", address #selfdestructed address

    #accounts alive in this state
    for address in blockchain.contract_accounts: 
        code = blockchain.get_code(address)
        balance = blockchain.get_balance(address)
        trace = set(( offset for address_i, offset in state.context['seth.trace'] if address == address_i))        
        print calculate_coverage(code, trace) #coverage % for address in this state

# All accounts ever created by the script 
# (may not all be alife in all states)
# (accounts created by contract code are not in this list )
print "[+] Global coverage:"
for address in seth.contract_accounts: 
    print address, seth.global_coverage(address) #coverage % for address in this state





