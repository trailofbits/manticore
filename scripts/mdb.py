from cmd import Cmd
import re

from manticore.ethereum import ManticoreEVM, evm, Operators, ABI
class ManticoreDebugger(Cmd):
    prompt = 'mdb> '
    def __init__(self):
        self.m = ManticoreEVM()
        self.user_account = self.m.create_account(balance=1000, name='user_account')
        self.owner_account = self.m.create_account(balance=1000, name='owner_account')
        self.current_account = self.user_account
        super().__init__()

    def do_show(self, inp):
        ''' Show current world state '''
        assert self.m.count_states() == 1
        for state in self.m.all_states:
            blockchain = state.platform
            for account_address in blockchain.accounts:
                print ("Address: %s (0x%x)" % (self.m.account_name(account_address), account_address))
                print ("Balance: ", blockchain.get_balance(account_address))
                print ("Storage: - not implemented -\n")

    def do_exit(self, inp):
        ''' Exit debugger '''
        print("Bye")
        return True 


    def do_whoami(self, inp):
        """ Print current user """
        print (self.m.account_name(self.current_account))

    def do_su(self, inp):
        """ change current user """
        if not inp:
            inp = 'owner_account'
        for state in self.m.all_states:
            blockchain = state.platform
            for account_address in blockchain.accounts:
                account_name = self.m.account_name(account_address)
                if account_address == inp or account_name == inp:
                    self.current_account = account_address
                    break

    def do_create(self, inp):
        ''' Create contract 
            create somecontract.sol ContractName2 [(args ...)]
            only int args implemented
        '''

        m = re.search(r'(\w+)(\w+)\((.*)\)', inp)
        if m:
            filename = m.group(1)
            contract_name = m.group(2)
            args = map(lambda x: int(x, 0), m.group(3).split(','))
            print ("args ignored")
        else:
            m = re.search(r'([a-zA-Z_.]+) (\w+)', inp)
            if m:
                filename = m.group(1)
                contract_name = m.group(2)
                args = []
            else:
                print ("error")
                return False

        with open(filename) as source_code:
            contract_account = self.m.solidity_create_contract(source_code, owner=self.current_account, name=contract_name)
        print (contract_account, contract_name)

    def do_call(self, inp):
        ''' make a tx 
            call pretty_name.function_name(3876, 87683)
        '''
        m = re.search(r'(\w+)\.(\w+)\((.*)\)', inp)
        if m:
            contract_name = m.group(1)
            function_name = m.group(2)
            args = map(lambda x: int(x, 0), m.group(3).split(','))
        else:
            print ("error")
            return False


        account = self.m.get_account(contract_name)
        result = getattr(account, function_name)(*args)

        for state in self.m.all_states:
            blockchain = state.platform
            print (blockchain.last_transaction.result,)
            if blockchain.last_transaction.result == 'RETURN':
                metadata = self.m.get_metadata(blockchain.last_transaction.address)
                return_data = state.solve_one(blockchain.last_transaction.return_data)
                function_id = bytes(blockchain.last_transaction.data[:4])  # hope there is enough data
                signature = metadata.get_func_signature(function_id)
                function_name = metadata.get_func_name(function_id)
                ret_types = metadata.get_func_return_types(function_id)
                return_values = ABI.deserialize(ret_types, return_data)  # function return
                print ("\t -> ", repr(return_values))

ManticoreDebugger().cmdloop()
