from manticore import *
from manticore.core.smtlib import ConstraintSet, Operators, solver
from manticore.platforms import evm
from manticore.core.state import State


class SEthereum(Manticore):
    def transaction(self, transaction):
        self.transactions.append(transaction)
        return transaction

    def __init__(self):
        #Make the constraint store
        constraints = ConstraintSet()
        #make the ethereum world state
        world = evm.EVMWorld(constraints)

        self.code = {}
        self.transactions = []
        super(SEthereum, self).__init__(State(constraints, world))

    #Callbacks
    def terminate_transaction_callback(self, state, state_id, e):
        ''' INTERNAL USE '''
        step = state.context.get('step',0)
        state.context['step'] = step + 1
        if step < len(self.transactions):
            self.transactions[step](self, state, state.platform)
            self.enqueue(state)
            e.testcase = False
        else:
            self.report(state, state.platform, e)

    def will_execute_instruction_callback(self, state, instruction):
        assert state.constraints == state.platform.constraints
        assert state.platform.constraints == state.platform.current.constraints

        #print state.platform.current
        #print solver.check(state.constraints)
        with self.locked_context('coverage', set) as coverage:
            coverage.add((state.platform.current.address, state.platform.current.pc))

    def did_read_code(self, state, offset, size):
        with self.locked_context('code_data', set) as code_data:
            for i in range(offset, offset+size):
                code_data.add(i)

    def run(self, **kwargs):
        #now when this transaction ends
        self._executor.subscribe('will_terminate_state', self.terminate_transaction_callback)
        self._executor.subscribe('will_execute_instruction', self.will_execute_instruction_callback)
        self._executor.subscribe('did_read_code', self.did_read_code)
        self._executor.subscribe('symbolic_sha3', self.symbolic_sha3)
        self._executor.subscribe('concrete_sha3', self.concrete_sha3)


        super(SEthereum, self).run(**kwargs)

    def report(self, state, world, e):
        for account, storage in world.storage.items():
            self.code[account] = storage['code']
        print "="*20
        print "REPORT:", e
        #print world
        for address, memlog, topics in state.platform.logs:
            try:
                print "LOG:", hex(address), '"'+(''.join(map(chr, memlog[64:])))+'"', topics
            except Exception,e:
                print e,"LOG:", address,  repr(memlog), topics

        #print state.constraints
        for expr in state.input_symbols:
            res = state.solve_one(expr)
            try:
                print expr.name+':',  res.encode('hex')
            except:
                print expr.name+':',  res


    def coverage(self, account_address):
        seen = self.context['coverage'].union( self.context.get('code_data', set()))
        runtime_bytecode = self.code[account_address]

        class bcolors:
            HEADER = '\033[95m'
            OKBLUE = '\033[94m'
            OKGREEN = '\033[92m'
            WARNING = '\033[93m'
            FAIL = '\033[91m'
            ENDC = '\033[0m'
            BOLD = '\033[1m'
            UNDERLINE = '\033[4m'

        output = ''
        offset = 0
        count = 0
        total = 0
        for i in evm.EVMDecoder.decode_all(runtime_bytecode) :
            
            if (account_address, offset) in seen:
                output += bcolors.OKGREEN
                output += "** 0x%04x %s\n"%(offset, i)
                output += bcolors.ENDC
                count += 1
            else:
                output += "   0x%04x %s\n"%(offset, i)
            
            total += 1
            offset += i.size

        output += "Total assembler lines: %d\n"% total
        output += "Total assembler lines visited: %d\n"% count
        output += "Coverage: %2.2f%%\n"%  (count*100.0/total)

        return output


    def symbolic_sha3(self, state, data, known_hashes):
        #print "SYMBOLIC HASH!"
        with self.locked_context('known_sha3', set) as known_sha3:
            state.platform._sha3.update(known_sha3)
        #print "symbolic_sha3", state, data, known_hashes
    def concrete_sha3(self, state, buf, value):
        #print "CONCRETE HASH!"
        with self.locked_context('known_sha3', set) as known_sha3:
            known_sha3.add((buf,value))
        #print "NEW KNOWN HASH", value

