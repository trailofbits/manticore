from cmd import Cmd
from os import listdir
import re

from manticore.ethereum import ManticoreEVM, evm, Operators, ABI
class ManticoreDebugger(Cmd):
    intro = ''' A eth debugger '''
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
        return False

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
        state = self._get_state()
        blockchain = state.platform
        for account_address in blockchain.accounts:
            account_name = self.m.account_name(account_address)
            if account_address == inp or account_name == inp:
                self.current_account = account_address
                break
        return False


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


    def complete_create(self, text, line, begidx, endidx):
        count = len(re.findall("[a-zA-Z_.]+", line[:begidx]))
        if count == 1:
            if line[begidx:endidx]:
                return [i for i in listdir() if i.startswith(line[begidx:endidx])]
            else:
                return [i for i in listdir() if i.endswith('.sol')]
        else:
            filename = re.findall("([\w+.]+)", line)[1]
            with open(filename) as f:
                source_code = f.read()
                return re.findall("contract +(\w+)", source_code)
        return []


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
            if blockchain.last_transaction.result == 'RETURN':
                metadata = self.m.get_metadata(blockchain.last_transaction.address)
                return_data = state.solve_one(blockchain.last_transaction.return_data)
                function_id = bytes(blockchain.last_transaction.data[:4])  # hope there is enough data
                signature = metadata.get_func_signature(function_id)
                function_name = metadata.get_func_name(function_id)
                ret_types = metadata.get_func_return_types(function_id)
                return_values = ABI.deserialize(ret_types, return_data)  # function return
                print ("\t -> ", repr(return_values))
        return False

    def _get_state(self):
        for state in self.m.all_states:
            return state

    def complete_call(self, text, line, begidx, endidx):
        count = len(re.findall("[a-zA-Z_.]+", line[:begidx]))
        print ("CALL", count )
        blockchain = self._get_state().platform
        if count == 1:
            if not line[begidx:endidx]:
                accounts = []
                for account_address in blockchain.accounts:
                    if not blockchain.get_code(account_address):
                        continue

                    account_name = self.m.account_name(account_address)
                    if account_name:
                        accounts.append(account_name)
                    else:
                        accounts.append(str(account_address))
                return accounts
            else:
                accounts = []
                for account_address in blockchain.accounts:
                    if not blockchain.get_code(account_address):
                        continue
                    account_name = self.m.account_name(account_address)
                    if account_name.startswith(line[begidx:endidx]):
                        accounts.append(account_name)
                    else:
                        if str(account_address).startswith(line[begidx:endidx]):
                            accounts.append(str(account_address))
                return accounts
        elif count ==  2:
            target_account_str = re.findall("([\w+.]+)", line)[1]
            state = self._get_state()
            blockchain = state.platform
            md = None
            for account_address in blockchain.accounts:
                if target_account_str == self.m.account_name(account_address) or target_account_str == str(account_address):
                    md = self.m.get_metadata(account_address)
            if md is not None:
                result_funcs = []
                for func_name in  md.functions:
                    try:
                        func_name = func_name.split('(')[0]
                    except:
                        pass
                    if func_name.startswith(line[begidx:endidx]):
                        result_funcs.append(func_name)
                return result_funcs
        return []



ManticoreDebugger().cmdloop()
