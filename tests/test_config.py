import io
import tempfile
import unittest

from manticore.utils import config


class ConfigTest(unittest.TestCase):
    def setUp(self):
        config._groups = {}

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

    def test_double_add(self):
        g = config.get_group('test1')
        g.add('val1', default='foo')
        with self.assertRaises(config.ConfigError):
            g.add('val1')

    def test_update(self):
        g = config.get_group('update')
        g.add('val', default='default', description='description')
        g.update('val', 34)
        g.update('val2', 56)

        o = g._var_object('val')
        self.assertEqual(o.value, 34)
        self.assertEqual(o.default, 'default')
        self.assertEqual(o.description, 'description')
        self.assertEqual(g.val2, 56)

    def test_getattr(self):
        g = config.get_group('attrs')
        with self.assertRaises(AttributeError):
            g.nonexistent

    def test_iter(self):
        g = config.get_group('few')
        g.add('one')
        g.add('two')
        l = list(g)
        self.assertEqual(len(l), 2)
        self.assertTrue('one' in g)
        self.assertFalse('three' in g)

    def test_parse(self):
        ini = '''
        [group]
        var1 = val
        var2 = 234
        var3 = [1,2,3]
        var4 = [[;;]]
        '''
        f = io.StringIO(ini)
        config.parse_ini(f)

        g = config.get_group('group')
        self.assertEqual(g.var1, 'val')
        self.assertEqual(g.var2, 234)
        self.assertEqual(g.var3, [1, 2, 3])
        self.assertEqual(g.var4, '[[;;]]')  # unparsed vals are just strs

    def test_describe(self):
        g = config.get_group('group')
        g.add('val', default=34, description='its a val')

        summary = config.describe_options()
        self.assertIn('group.val', summary)
        self.assertIn('default: 34', summary)
        self.assertIn('its a val', summary)

    def test_overrides(self):
        with tempfile.NamedTemporaryFile('w+') as conf:
            conf.file.write('''
            [group]
            var1 = val1
            ''')
            conf.file.close()

            config.load_overrides(conf.name)
            g = config.get_group('group')
            self.assertEqual(g.var1, 'val1')

    def test_default_overrides(self):
        # no default ini to load
        config.load_overrides()
        self.assertEqual(len(config._groups), 0)


