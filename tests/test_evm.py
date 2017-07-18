import struct
import unittest
import json
from manticore.platforms import evm
from manticore.core import state
from manticore.core.smtlib import Operators, ConstraintSet
import os

def i(x):
    if isinstance(x, (int, long)):
        return x
    assert isinstance(x, (str, unicode))
    if not x.startswith('0x'):
        x = '0x' + x
    return int(x, 0)

def _test_evm_concrete(self, testcase, testname):
    print testname
    header = {}
    env = testcase['env']
    for key in env:
        if key.startswith('previous'):
            _key = str(key[8:].lower())
        else:
            _key = str(key[7:].lower())
        try:
            header[_key] = i(env[key])
        except:
            print "XXXXXX" , key, env[key]

    pre = testcase['pre']
    world = {}
    for address in pre.keys():
        iaddress = i(address)
        world[iaddress] = {}
        world[iaddress]['code'] = pre[address][u'code'][2:].decode('hex')
        world[iaddress]['nonce'] = i(pre[address][u'nonce'])
        world[iaddress]['balance'] = i(pre[address][u'balance'])
        world[iaddress]['storage'] = {}
        for key, value in pre[address][u'storage'].items():
            world[iaddress]['storage'][key] = value

    exe = testcase['exec']
    transaction = {}
    for key in exe.keys():
        pkey = str(key)
        if key == 'gasPrice':
            pkey = 'price'
        if key in ['data', 'code']:
            value = exe[key][2:].decode('hex')
        else:
            value = i(exe[key])

        transaction[pkey] = value

    constraints = ConstraintSet()
    platform = evm.EVMWorld(constraints)
    for address, contract in world.items():
        #CONTRACT['NONCE'] NOT USED fixme
        platform.create_account(address=address, balance=contract['balance'], code=contract['code'], storage=contract['storage'])
    
    address = transaction['address']
    origin = transaction['origin']
    price = transaction['price']
    data = transaction['data']
    caller = transaction['caller']
    value = transaction['value']
    platform.transaction(address, origin, price, data, caller, value, header)
    
    throw = False
    try:
        platform.run()
    except state.TerminateState as e:                
        if e.message != 'STOP':
            throw = True

    if 'post' in testcase:
        pos = testcase['post']
        world = {}
        for address in pos.keys():
            iaddress = i(address)
            world[iaddress] = {}
            world[iaddress]['code'] = pos[address][u'code'][2:].decode('hex')
            world[iaddress]['nonce'] = i(pos[address][u'nonce'])
            world[iaddress]['balance'] = i(pos[address][u'balance'])
            world[iaddress]['storage'] = {} 
            for key, value in pos[address][u'storage'].items():
                world[iaddress]['storage'][i(key)] = i(value)
        self.assertEqual( world, platform.storage)
    else:
        print throw, "should be True" #self.assertTrue(throw)



class TestMeta(type):
    def __new__(mcs, name, bases, _dict):

        def gen_test(test_dict, test_name):
            def test(self):
                _test_evm_concrete(self, test_dict, test_name)
            return test


        dirname = os.path.join(os.path.dirname(__file__), 'EVMTests')
        for filename in os.listdir(dirname):
            if filename.endswith('.json'):
                js = file(os.path.join(dirname, filename)).read()
                tests = json.loads(js)
                for test_name in tests.keys():
                    if test_name in ('BlockNumberDynamicJump0_foreverOutOfGas','jump0_foreverOutOfGas', '01a5cf9db140969b2a2410361164fc41c64c070805b82116d217240d4e304f6f', '08d5011d0a278a4d86298cf5a49d99df2662e279100f62fcdbd994df3fe58fbe','3a537f4a02067e6c5a8cf348bdffdb4e6b25475055503a8a5c16690cd51d1060',
'4341c8f00034ada5203fad4bccf429d2cec28a58dc83e53f4a957694d653dbd4','5340ec41425169e8d8771356443a0a312d3e3c809059eb092b0e2a2f8efb0921', '607ba70d1799c9345e522410e3313582cb9a3e8aecfcb00b3d510e7bbcae522b', '5fc1b8e024dc710ad40a90f6fc18938a90ef020751e3370572d2d4b407e43e63',
'sha3_3', 'ABAcalls0', 'ABAcalls2', 'ABAcallsSuicide0', 'ABAcallsSuicide1'):
                        break
                    #print filename, test_name, tests[test_name]
                    name = 'test_%s_%s'%(filename[:-5],test_name)
                    name = str(name.replace('.', '_'))
                    _dict[name] = gen_test(tests[test_name], test_name)
                
        return type.__new__(mcs, name, bases, _dict)

class EVMTest(unittest.TestCase):
    _multiprocess_can_split_ = True
    __metaclass__ = TestMeta


if __name__ == '__main__':
    unittest.main()
