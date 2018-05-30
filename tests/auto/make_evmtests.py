from __future__ import print_function
from pprint import pformat
from cStringIO import StringIO

def pretty(value, htchar=' ', lfchar='\n', indent=0, width=100):
    nlch = lfchar + htchar * (indent + 1)
    if type(value) is dict:
        items = [
            nlch + repr(key) + ': ' + pretty(value[key], htchar, lfchar, indent +  1, width)
            for key in value
        ]
        return '{%s}' % (','.join(items) + lfchar + htchar * indent)
    elif type(value) is list:
        items = [
            nlch + pretty(item, htchar, lfchar, indent + 1, width)
            for item in value
        ]
        return '[%s]' % (','.join(items) + lfchar + htchar * indent)
    elif type(value) is tuple:
        items = [
            nlch + pretty(item, htchar, lfchar, indent + 1, width)
            for item in value
        ]
        return '(%s)' % (','.join(items) + lfchar + htchar * indent)
    elif type(value) in (str, unicode):
        if len(value) ==0:
            return repr(value)

        if width is not None and isinstance(value, str):
            width = width - indent
            width = max(1, width)
            o = []
            for pos in range(0, len(value), width): 
                o.append(repr(value[pos: pos+width]) )
            return ('\\' + lfchar + htchar * indent).join(o)
        return repr(value)

    else:
        return repr(value)
pprint = pretty
pp = pretty
def spprint(x, indent=0, width=None,**kwargs):
    if width is not None and isinstance(x, str):
        o = ''
        for pos in range(0, len(x), width): 
            o += ' '*indent + repr(x[pos: pos+width]) + '\\'
        return o
    x = pformat(x, indent=0)
    return (('\n'+' '*indent)).join(x.split('\n'))

def i(x):
    if isinstance(x, (int, long)):
        return x
    assert isinstance(x, (str, unicode))
    if not x.startswith('0x'):
        x = '0x' + x
    return long(x, 0)
def gen_test(testcase, testname, skip):
    output = ''
    if skip:
        output += '''    @unittest.skip('Gas or performance related')\n'''

    output += '    def test_%s(self):\n'% (os.path.split(testname)[1].replace('-','_'))
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
            print("XXXXXX" , key, env[key])
    output += '        header =' + pprint (header, indent=18) +'\n'

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

    #output += "        pre_world =" + pprint( world, indent=22)+'\n'
    pre_world = world
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

    pos_world = None
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
        output += "        pos_world = " + pprint(world, indent=27) + '\n'
    
    else:
        output += "        pos_world = None\n"
    pos_world = world


    #CONTRACT['NONCE'] NOT USED fixme
    output += '''
        constraints = ConstraintSet()
        platform = evm.EVMWorld(constraints)'''
    
    for address, contract in pre_world.items():
        output +='''           
        platform.create_account(address=%s, 
                                balance=%s, 
                                code=%s, 
                                storage=%s
                                )''' % (pp(address),
                                        pp(contract['balance']), 
                                        pp(contract['code'],width=60, indent=37), 
                                        pp(contract['storage'],width=80, indent=40))

        output +='''           
        platform.create_account(address=%s, 
                                balance=%s, 
                                code=%s, 
                                storage=%s
                                )''' % (pp(transaction['caller']),
                                        pp(contract['balance']), 
                                        pp(contract['code'],width=60, indent=37), 
                                        pp(contract['storage'],width=80, indent=40))


    output += '''        
        address = %s
        origin = %s
        price = %s
        data = %s
        caller = %s
        value = %s''' % (
    pp(transaction['address']),
    pp(transaction['origin']),
    pp(transaction['price']),
    pp(transaction['data']),
    pp(transaction['caller']),
    pp(transaction['value']) )
    output += '''        
        #platform.transaction(address, origin, price, data, caller, value, header)
        bytecode = platform.storage[address]['code']
        new_vm = EVM(constraints, address, origin, price, data, caller, value, bytecode, header, global_storage=platform.storage)
        
  
        throw = False
        try:
            #platform.run()
            new_vm.run()
        except state.TerminateState as e:                
            if e.message != 'STOP':
                throw = True

        if pos_world is None:
            self.assertTrue(throw)
        else:
            self.assertEqual( pos_world, platform.storage)
'''

    
    return output

import sys, os, json
if __name__ == '__main__':
    filename = os.path.abspath(sys.argv[1])

    assert filename.endswith('.json')

    print('''
import struct
import unittest
import json
from manticore.platforms import evm
from manticore.core import state
from manticore.core.smtlib import Operators, ConstraintSet
import os


class EVMTest_%s(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff=None 
'''%  os.path.split(sys.argv[1][:-5])[1]) 

    js = file(filename).read()
    tests = dict(json.loads(js))

    #print "#processed ", len(tests.keys()), tests.keys()
    count = 0
    for test_name, testcase in tests.items():
        count +=1
        #print "#count", count , test_name, '0c423e4e26c7938c2a82ce40d05a549d617b32303a824ba5a93cb2fb0b037dfd'
        skip = False
        if test_name in ('BlockNumberDynamicJump0_foreverOutOfGas','jump0_foreverOutOfGas', '01a5cf9db140969b2a2410361164fc41c64c070805b82116d217240d4e304f6f', '08d5011d0a278a4d86298cf5a49d99df2662e279100f62fcdbd994df3fe58fbe','3a537f4a02067e6c5a8cf348bdffdb4e6b25475055503a8a5c16690cd51d1060',
'4341c8f00034ada5203fad4bccf429d2cec28a58dc83e53f4a957694d653dbd4','5340ec41425169e8d8771356443a0a312d3e3c809059eb092b0e2a2f8efb0921', '607ba70d1799c9345e522410e3313582cb9a3e8aecfcb00b3d510e7bbcae522b', '5fc1b8e024dc710ad40a90f6fc18938a90ef020751e3370572d2d4b407e43e63',
'sha3_3', 'ABAcalls0', 'ABAcalls2', 'ABAcallsSuicide0', 'ABAcallsSuicide1', '0c423e4e26c7938c2a82ce40d05a549d617b32303a824ba5a93cb2fb0b037dfd', '18ee3a269d4408f34f22a0a86c28d2538b48933ceee730a9ae5615bcc21d5435',
'1dc82eaa4472991b1d8e7a2042e6e6ba59ddc6e6157736fad05d01c5f07d74f1', '2011723095c2f01a6061cea476f2d5aef6f89d9bf8fd65bf19ccbbbfd7f12235',
'2174a06c481ddff76d7720354934d536b2e65a338db6ed4854a12ad261c0f934', '2c09481e499e7bf0edf21dd42c04cf041d1ef8ab74dfbabc7022791a8f6e35b3',
'319756923d422ba192da410609ba055adf5964f6d53c23543680721128591fa0','41f8c240c088571b00f7c78e9592c29b2f3b155d9be1089255de4faee3b7fe52',
'4445aef149dec5c59375104384d94a7c5a1075a465adec36657fe6774bbc200e', '45ae12b67afd7aa490f9c321d137f92d94b04ec0efad268423fc8471d639356f',
'46e1952a729b786f5f96f160e6fab13a4b78f182a925405df40669a18de94915', '47f0ac8ae67ffd1821270650cb6e6088cb234aabff79f0d0d7d9376c1a3c33bc',
'499925dd735dd0e62b168507249b64bd19e07ee8abbf185ade4c2cb12a7600f6', '5944d95306be93af8c45c13ec099314aeba52434af09012abd0eb61a80e5d874',
'5d20205dd04102c2227ddb5624753ef45832d25c4094aeb575c3f21c6c6b58d6', '5f2fc70586e44cea7cf78a2222c7cc4540929df1d47d9659508b1f1d0bd12bbe',
'6264fce6e5e03527ceac0b4f6d0637cb847e52cde36e5eee085125ce87f82b28','6a1ae314ad4ae7e0e1627a27aa71bc39d335afbe74e8f9f495953bea9e8dc432',
'6bece201afaedb2fad097d2b7776036166a850565af60697ef3c7735299024ed','7ab1b013a7d76006fe6e61c3e22c05f6dd6a1930117a9c9a9867a8af8e4c0c28',
'9536ae5ed3a92cd577d0c83a96909f64babd8de29f1f8516dc75fc51afec04cf','95766dcaa8d3e71bb028d8f4f9fefd22cb28ee179e7df5bcc2425b105a8d090c',
'9c380b88838dca02ff0f517f64a61514654f7e734b989ed272fdc348de57e501', '9f3c956a07536777d6a8fa162b0331ab06b9f0448d48a719df62a8a5ee0c73fe',
'a5e749f7d3555cfa3cd5b9a1fb7e296bd6d74d37b7eecea5f9404727407ab1dd', 'aef72030bfcd3ea0ded6cc89f3a151eea90987823f3cd2ea5b12b0db7ced5896',
'b61e68d30132efa1c0e891f04b1ebfcfcaac76db5ac4d316cdcbb60bbe32da5c', 'b8c838c8c9fbd570edb5a783b43c429742af8cfe993dbdcae94cba03390fe3f3',
'b96dbf50e26807dc7890f55ff5fce3ac378835a115187671c6882e8fe4256897', 'c008ef3e89c2dedbc5e953b74eadc515fd5cd172ba75ec229c67be66b95ec91a',
'c44dfcdd9c3ebe9c215b5ac20ba1a662523a63e7e9a375200071ab062f23a775','c4ad831e6119348c5c48a840de9bb41efdfbeba5a86aa71d04e8c10611ebe316',
'c4e33c1a7a3f756b3f9f223bccb70dee15a30f559d7648d3da2081c7862cbb16', 'd12665946c07d88384f335af064dbfc679283062bdbb17b56e1b812c3bd80dc9',
'd197d4181060d54d4ce3965aca77fc97809b613b42ba95698d146907fd0946d8', 'd9c6725e08f795f167d187609ab9b356e737841c56744069ad581e80071dc6c3',
'da5e09e2db0ad1cf1d68bd8f0b780cbd2f26f454f37d887bdac9e9fd42e2b1a1', 'e434a52cc9af21ef1204b5cdb333b376900fc5c2ece63b9d34fa4902908a455e',
'e434a52cc9af21ef1204b5cdb333b376900fc5c2ece63b9d34fa4902908a455e', 'e7c8c8665467646d68964497d222df12d6db05efbc5d5de1bf27c471023c1932',
'f76b7c41b0a7d2879851037f8eea928fc7302bd60fd6af4b6e4030a3a24436b4','f8660436772f63f5cd6bb20e12150cdc66f5238f78d872196f49bc9bf7b5d68d',
'fa78200fce12b17e9c320d743ddd7d32094326376fe9f6bf9964b285a9350a7e', 'DynamicJump0_foreverOutOfGas', 'JDfromStorageDynamicJump0_foreverOutOfGas', 'ABAcalls1', 'ABAcalls3', 'CallToNameRegistratorTooMuchMemory1','callcodeToNameRegistrator0'):
            skip = True
        #print filename, test_name, tests[test_name]    
        name = 'test_%s_%s'%(filename[:-5],test_name)
        name = str(name.replace('.', '_'))
        print(gen_test(testcase, test_name, skip))

    print('''
if __name__ == '__main__':
    unittest.main()''')
