
import unittest

from manticore.utils.event import Signal

class Sender(object):
    def __init__(self):
        self.sig = Signal()
        self.sig2 = Signal()

class ManticoreDriver(unittest.TestCase):
    def setUp(self):
        self.state = {}

    def tearDown(self):
        pass

    def setReceived(self, key, val):
        self.state[key] = val

    def setReceived2(self, key, val):
        self.state[key] = val


    def test_basic(self):
        s = Sender()

        def recv():
            self.state['received'] = True

        self.state['received'] = False

        s.sig += recv

        s.sig()

        self.assertEqual(self.state['received'], True)

    def test_method(self):
        s = Sender()
        s.sig += self.setReceived
        
        s.sig('received', True)

        self.assertEqual(self.state['received'], True)

    def test_disconnect(self):
        s = Sender()

        s.sig.connect(self.setReceived)

        s.sig -= self.setReceived

        s.sig('received', True)

        self.assertNotIn('received', self.state)

    def test_predicate(self):
        s = Sender()

        s.sig.connect(self.setReceived)
        s.sig2.connect(self.setReceived2, lambda: False)

        s.sig('true', True)
        s.sig2('false', True)

        self.assertEqual(self.state['true'], True)
        self.assertNotIn('false', self.state)

