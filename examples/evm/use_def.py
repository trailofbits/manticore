from manticore.ethereum import ManticoreEVM, Plugin
from manticore.core.smtlib import solver
from manticore.core.smtlib.visitors import arithmetic_simplifier, pretty_print, constant_folder
################ Script #######################

m = ManticoreEVM()
m.verbosity(0)
#And now make the contract account to analyze
# cat  | solc --bin 
source_code = '''
pragma solidity ^0.4;
contract C {
    uint c;
    bool enabled;
    bool i;
    function C() public {
        c =0;
        enabled = false;
        i = false;
        
    }
    function f1() public {
        c+=1;
    }
    function f2() public {
        if(c>100)
            enabled=true;
        
    }
    function f3() public{
        if (!enabled) 
            return;
        i = true;
        
    }
}
'''
print source_code
class EVMUseDef(Plugin):
    def _get_concrete_hex(self, state, array):
        r = ''
        for i in array:
            l = state.solve_n(i, 2)
            if len(l) == 1:
                r += '%02x'%l[0]
        if len(r) != 8:
            return
        return r


    def did_evm_write_storage_callback(self, state, offset, value, **kwargs):
        m = self.manticore
        world = state.platform
        tx = world.all_transactions[-1]
        md = m.get_metadata(tx.address)

        r = self._get_concrete_hex(state, tx.data[0:4])
        if r is None:
            return


        offsets = state.solve_n(offset, 3000)
        with self.locked_context('storage_writes', dict) as storage_writes:
            contract_function = (md.name, md.get_func_name(r))
            if contract_function not in storage_writes:
                storage_writes[contract_function] = set()
            for off in offsets:
                storage_writes[contract_function].add(off)

    def did_evm_read_storage_callback(self, state, offset, value, **kwargs):
        m = self.manticore
        world = state.platform
        tx = world.all_transactions[-1]
        md = m.get_metadata(tx.address)

        r = self._get_concrete_hex(state, tx.data[0:4])
        if r is None:
            return

        offsets = state.solve_n(offset, 3000)
        with self.locked_context('storage_reads', dict) as storage_reads:
            contract_function = (md.name, md.get_func_name(r))
            if contract_function not in storage_reads:
                storage_reads[contract_function] = set()
            for off in offsets:
                storage_reads[contract_function].add(off)

#Initialize accounts
user_account = m.create_account(balance=1000)
contract_account = m.solidity_create_contract(source_code, owner=user_account)
p = EVMUseDef()
m.register_plugin(p)


symbolic_data = m.make_symbolic_buffer(320)
symbolic_value = m.make_symbolic_value()
m.transaction(  caller=user_account,
                   address=contract_account,
                   value=symbolic_value,
                   data=symbolic_data
                 )
print "READS", p.context['storage_reads']
print "WRITES", p.context['storage_writes']

print "It makes no sense to try f3() after 1 tx"

m.finalize()
print "[+] Look for results in %s"% m.workspace


