from manticore import *
from manticore.core.smtlib import ConstraintSet
from manticore.platforms import evm
from manticore.core.state import State
from manticore.core.executor import Executor
import logging,sys,types

def loggerSetState(logger, stateid):
    logger.filters[0].stateid = stateid

class ContextFilter(logging.Filter):
    '''
    This is a filter which injects contextual information into the log.
    '''
    def filter(self, record):
        if hasattr(self, 'stateid') and isinstance(self.stateid, int):
            record.stateid = '[%d]' % self.stateid
        else:
            record.stateid = ''
        return True

ctxfilter = ContextFilter()

logging.basicConfig(format='%(asctime)s: [%(process)d]%(stateid)s %(name)s:%(levelname)s: %(message)s', stream=sys.stdout)

for loggername in ['MANTICORE', 'VISITOR', 'EXECUTOR', 'CPU', 'REGISTERS', 'SMT', 'MEMORY', 'MAIN', 'PLATFORM']:
    logging.getLogger(loggername).addFilter(ctxfilter)
    logging.getLogger(loggername).setState = types.MethodType(loggerSetState, logging.getLogger(loggername))
    logging.getLogger('SMT').setLevel(logging.DEBUG)

logging.getLogger('SMT').setLevel(logging.INFO)
logging.getLogger('MEMORY').setLevel(logging.INFO)
logging.getLogger('LIBC').setLevel(logging.INFO)
logging.getLogger('MANTICORE').setLevel(logging.INFO)
def pack(i, size=32):
    assert size >=1
    o = [0] * size
    for x in range(size):
        o[(size-1) - x] = i & 0xff
        i >>= 8
    return ''.join(map(chr,o))



#Make the constraint store
constraints = ConstraintSet()
#make the ethereum world state
world = evm.EVMWorld(constraints)

#make a bunch of user accounts
user_account = world.create_account(address=None, balance=1000)
attacker_account = world.create_account(address=None, balance=0)


#And now make the contract account to analyze
'''
pragma solidity ^0.4.13;

contract Test {
    uint private sellerBalance=0;
    
    function Test(uint initialBalance){
        sellerBalance += initialBalance;
    }
    
    function target(uint value) returns (bool){

        sellerBalance += value; // possible overflow
        assert(sellerBalance >= value); // auditor assert

    } 

}
'''

bytecote = '606060405260008055341561001357600080fd5b604051602080610115833981016040528080519060200190919050505b8060008082825401925050819055505b505b60c5806100506000396000f30060606040526000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff1680639811c7c114603d575b600080fd5b3415604757600080fd5b605b60048080359060200190919050506075565b604051808215151515815260200191505060405180910390f35b60008160008082825401925050819055508160005410151515609357fe5b5b9190505600a165627a7a7230582061a5978237a74c48ff9f0aeadd9d2bae62116a5a44fc2130964499c20f2129f40029'.decode('hex')

#initialize contract with "50"
contract_account = world.create_contract(origin=user_account, 
                                              price=0, 
                                              address=None, 
                                              balance=0, 
                                              init=bytecote + pack(50),
                                              run=True)

#This is how the world looks like now...
print world

#Start the attack, this is a symbolic transaction. It should generate several world states.
symbolic_data = constraints.new_array(256, name='DATA', index_max=256)
world.transaction(address=contract_account,
                    origin=user_account,
                    price=0,
                    data=symbolic_data,
                    caller=user_account,
                    value=0,
                    header={'timestamp':1})

initial_state = State(constraints, world)
initial_state.input_symbols.append(symbolic_data)

executor = Executor(initial_state, workspace="./workspace")

executor.run()

#explore resulted states for one with funds in the attacker_account or whatever
# in ./workspace



