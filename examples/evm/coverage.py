from manticore.ethereum import ManticoreEVM

m = ManticoreEVM()
m.verbosity(3)
# And now make the contract account to analyze
source_code = open('coverage.sol').read()

user_account = m.create_account(balance=1000)

bytecode = m.compile(source_code)
# Initialize contract
contract_account = m.create_contract(owner=user_account,
                                     balance=0,
                                     init=bytecode)

m.transaction(caller=user_account,
              address=contract_account,
              value=m.make_symbolic_value(),
              data=m.make_symbolic_buffer(164),
              )

# Up to here we get only ~30% coverage.
# We need 2 transactions to fully explore the contract
m.transaction(caller=user_account,
              address=contract_account,
              value=m.make_symbolic_value(),
              data=m.make_symbolic_buffer(164),
              )

print("[+] There are %d reverted states now" % m.count_terminated_states())
print("[+] There are %d alive states now" % m.count_running_states())
# for state_id in m.running_state_ids:
#     print(m.report(state_id))

print("[+] Global coverage: %x" % contract_account.address)
print(m.global_coverage(contract_account))
