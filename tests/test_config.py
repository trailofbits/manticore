import unittest

from manticore.utils import config

class ConfigTest(unittest.TestCase):
    def test_create_group(self):
        consts = config.get_group('smt')
        self.assertIsInstance(consts, config._group)
        self.assertEquals(consts.name, 'smt')

    def test_repeated_get(self):
        g1 = config.get_group('name')
        g2 = config.get_group('name')
        self.assertIs(g1, g2)

    def test_basic_var(self):
        g = config.get_group('test')
        g.add('runtime', default='def', description='This value controls something')

        # this should not raise
        self.assertEquals(g.runtime, 'def')
        self.assertEquals(g.get_description('runtime'), 'This value controls something')

    def test_default_vars(self):
        g = config.get_group('test')
        g.add('val1', default='foo')
        g.add('val2', default='foo')

        g.val2 = 'bar'

        self.assertFalse(g._vars['val1'].was_set)
        self.assertTrue(g._vars['val2'].was_set)


