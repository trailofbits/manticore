from manticore import Manticore
from manticore.core.smtlib import ConstraintSet, Operators, solver, issymbolic
from manticore.platforms import evm
from manticore.platforms.evm import pack_msb
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
        for account, storage in state.platform.storage.items():
            self.code[account] = storage['code']

        if e.message != 'REVERT' and step < len(self.transactions):
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
                code_data.add((state.platform.current.address, i))

    def run(self, **kwargs):
        #now when this transaction ends
        self._executor.subscribe('will_terminate_state', self.terminate_transaction_callback)
        self._executor.subscribe('will_execute_instruction', self.will_execute_instruction_callback)
        self._executor.subscribe('did_read_code', self.did_read_code)
        self._executor.subscribe('symbolic_sha3', self.symbolic_sha3)
        self._executor.subscribe('concrete_sha3', self.concrete_sha3)


        super(SEthereum, self).run(**kwargs)

    def report(self, state, world, e):
        def compare_buffers(a, b):
            if len(a) != len(b):
                return False
            cond = True
            for i in range(len(a)):
                cond = Operators.AND(a[i]==b[i], cond)
                if cond is False:
                    return False
            return cond

        print "="*20
        print "REPORT:", e, "\n"

        print "LOGS:"
        for address, memlog, topics in state.platform.logs:
            try:
                print  "\t", hex(state.solve_one(address)), repr(state.solve_one(memlog)), topics
            except Exception,e:
                print  "\t", address,  repr(memlog), topics

        #print state.constraints
        print "INPUT SYMBOLS"
        for expr in state.input_symbols:
            res = state.solve_one(expr)
            state.constrain(compare_buffers(expr, res))
            try:
                print "\t", expr.name+':',  res.encode('hex')
            except:
                print "\t", expr.name+':',  res

        print "BALANCES"
        for address, account in world.storage.items():
            if issymbolic(account['balance']):
                m,M = solver.minmax(world.constraints, account['balance'])
                if m==M:
                    print "\t", hex(address), M
                else:
                    print "\t", hex(address), "range:[%x, %x]"%(m,M)                
            else:
                print "\t", hex(address), account['balance']
            


    def coverage(self, account_address):
        seen = self.context['coverage'] #.union( self.context.get('code_data', set()))
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

