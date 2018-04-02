
import unittest
from manticore.ethereum import ABI, EthereumError

class EVMTest_ABI(unittest.TestCase):
    _multiprocess_can_split_ = True
    maxDiff=None 

    def test_ABI_INT(self):
            abi = ABI()

            try:
                abi.parse("intXXX", "\xFF")
                self.assertTrue(False)
            except NotImplementedError:
                pass

            try:
                abi.parse("int3000", "\xFF")
                self.assertTrue(False)
            except NotImplementedError:
                pass

            try:
                abi.parse("int-8", "\xFF")
                self.assertTrue(False)
            except NotImplementedError:
                pass

            for i in range(8, 257, 1):
                try:
                    datatype = "int"+str(i)
                    data = "\xFF"*32
                    abi.parse(datatype, data)
                    self.assertEqual(i % 8, 0)
                except EthereumError:
                    self.assertNotEqual(i % 8, 0)

if __name__ == '__main__':
    unittest.main()
