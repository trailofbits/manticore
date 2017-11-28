from seth import *

seth = ManticoreEVM()
seth.verbosity(3)
user_account = seth.create_account(balance=1000)

bytecode = '`'
#Initialize contract
contract_account = seth.create_contract(owner=user_account,
                                          balance=0,
                                          init=bytecode)

def explore(state):
    pass

seth.add_hook(None, explore)
seth.transaction(  caller=user_account,
                    address=contract_account,
                    value=None,
                    data='',
                 )
