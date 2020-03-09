from manticore.ethereum import evm, ManticoreEVM
from binascii import unhexlify, hexlify

################ Script #######################
# Bytecode only based analysis
# No solidity, no compiler, no metadata

m = ManticoreEVM()
init_bytecode = unhexlify(
    b"608060405234801561001057600080fd5b506101cc806100206000396000f30060806040527f41000000000000000000000000000000000000000000000000000000000000006000366000818110151561003557fe5b905001357f010000000000000000000000000000000000000000000000000000000000000090047f0100000000000000000000000000000000000000000000000000000000000000027effffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff19167effffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff19161415610135577fcf34ef537ac33ee1ac626ca1587a0a7e8e51561e5514f8cb36afa1c5102b3bab6040518080602001828103825260088152602001807f476f7420616e204100000000000000000000000000000000000000000000000081525060200191505060405180910390a161019e565b7fcf34ef537ac33ee1ac626ca1587a0a7e8e51561e5514f8cb36afa1c5102b3bab6040518080602001828103825260128152602001807f476f7420736f6d657468696e6720656c7365000000000000000000000000000081525060200191505060405180910390a15b0000a165627a7a72305820fd5ec850d8409e19cfe593b9ee3276cc3ac12b0e3406d965317dc9c1aeb7f2670029"
)

user_account = m.create_account(balance=1000)
print("[+] Creating a user account", user_account)

print("[+] Init bytecode:", hexlify(init_bytecode))
print("[+] EVM init assembler:")
for instr in evm.EVMAsm.disassemble_all(init_bytecode[:-44]):
    print(hex(instr.pc), instr)

contract_account = m.create_contract(owner=user_account, init=init_bytecode)
print("[+] Creating a contract account", contract_account)

print("[+] Now the symbolic values")
symbolic_data = m.make_symbolic_buffer(320)
symbolic_value = m.make_symbolic_value()
m.transaction(
    caller=user_account, address=contract_account, data=symbolic_data, value=symbolic_value
)

# Let seth know we are not sending more transactions
m.finalize()
print(f"[+] Look for results in {m.workspace}")
