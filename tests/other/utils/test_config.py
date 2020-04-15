import io
import argparse
import tempfile
import unittest

from manticore.utils import config


class ConfigTest(unittest.TestCase):
    def setUp(self):
        config._groups = {}

    def test_create_group(self):
        consts = config.get_group("smt")
        self.assertIsInstance(consts, config._Group)
        self.assertEqual(consts.name, "smt")

    def test_repeated_get(self):
        g1 = config.get_group("name")
        g2 = config.get_group("name")
        self.assertIs(g1, g2)

    def test_basic_var(self):
        g = config.get_group("test")
        g.add("runtime", default="def", description="This value controls something")

        # this should not raise
        self.assertEqual(g.runtime, "def")
        self.assertEqual(g.get_description("runtime"), "This value controls something")

        with self.assertRaises(config.ConfigError):
            g.get_description("nonexistent")

    def test_default_vars(self):
        g = config.get_group("test")
        g.add("val1", default="foo")
        g.add("val2", default="foo")

        g.val2 = "bar"

        self.assertFalse(g._vars["val1"].was_set)
        self.assertTrue(g._vars["val2"].was_set)

    def test_double_add(self):
        g = config.get_group("test1")
        g.add("val1", default="foo")
        with self.assertRaises(config.ConfigError):
            g.add("val1")

    def test_update(self):
        g = config.get_group("update")
        g.add("val", default="default", description="description")
        g.update("val", 34)
        g.update("val2", 56)

        o = g._var_object("val")
        self.assertEqual(o.value, 34)
        self.assertEqual(o.default, "default")
        self.assertEqual(o.description, "description")
        self.assertEqual(g.val2, 56)

    def test_group_temp_vals(self):
        g = config.get_group("test")
        g.add("val", default=123)

        self.assertEqual(g.val, 123)

        with g.temp_vals():
            self.assertEqual(g.val, 123)
            g.val = 456
            self.assertEqual(g.val, 456)
            g.val = 789
            self.assertEqual(g.val, 789)

            with g.temp_vals():
                g.val = 123456
                self.assertEqual(g.val, 123456)

            self.assertEqual(g.val, 789)

        self.assertEqual(g.val, 123)

        t = g.temp_vals()
        with t:
            with self.assertRaises(config.ConfigError) as e:
                with t:
                    pass

        self.assertEqual(str(e.exception), "Can't use temporary group recursively!")

    def test_getattr(self):
        g = config.get_group("attrs")
        with self.assertRaises(AttributeError):
            g.nonexistent

    def test_iter(self):
        g = config.get_group("few")
        g.add("one")
        g.add("two")
        l = list(g)
        self.assertEqual(len(l), 2)
        self.assertTrue("one" in g)
        self.assertFalse("three" in g)

    def test_get_config_keys(self):
        g = config.get_group("few")
        g.add("one")
        g.add("two")
        keys = list(config.get_config_keys())
        self.assertIn("few.one", keys)
        self.assertIn("few.two", keys)

    def test_parse(self):
        conf = """
        group:
            var1: val
            var2: 234
            var3: [1, 2, 3]
            var4: []
        """
        f = io.StringIO(conf)
        config.parse_config(f)

        g = config.get_group("group")
        self.assertEqual(g.var1, "val")
        self.assertEqual(g.var2, 234)
        self.assertEqual(g.var3, [1, 2, 3])
        self.assertEqual(g.var4, [])

    def test_parse_badconfig(self):
        conf = "bad config"
        f = io.StringIO(conf)
        # this shouldn't raise
        with self.assertRaises(config.ConfigError):
            config.parse_config(f)

    def test_overrides(self):
        with tempfile.NamedTemporaryFile("w+") as conf:
            conf.file.write("group: {var1: val1}")
            conf.file.close()

            config.load_overrides(conf.name)
            g = config.get_group("group")
            self.assertEqual(g.var1, "val1")

        with self.assertRaises(FileNotFoundError):
            config.load_overrides("a_hopefully_nonexistent_file.ini")

    def test_default_overrides(self):
        # no default ini to load
        config.load_overrides()
        self.assertEqual(len(config._groups), 0)

    def test_save(self):
        g = config.get_group("set_vars")
        g.add("set", default="0")
        g.set = 1

        g = config.get_group("unset_vars")
        g.add("unset", default="0")

        s = io.StringIO()
        config.save(s)
        saved = s.getvalue()

        self.assertIn("set_vars:", saved)
        self.assertNotIn("unset_vars:", saved)

    def test_add_config_vars(self):
        g = config.get_group("few")
        g.add("one", default=0, description="desc")
        g.add("two", default="x", description="desc2t")

        parser = argparse.ArgumentParser("Description")
        config.add_config_vars_to_argparse(parser)
        usage = parser.format_help()

        # There are no public methods to get at the added options so far, so we're just checking with
        # usage string
        self.assertIn("--few.one", usage)
        self.assertIn("--few.two", usage)

    def test_bad_group_name(self):
        g = config.get_group("few")

        # Shouldn't be able to make a var named 'name'
        with self.assertRaises(config.ConfigError):
            g.add("name", default=0, description="desc")

        with self.assertRaises(config.ConfigError):
            g.update("name", default=0, description="desc")

    def test_process_cli(self):

        g = config.get_group("grp")
        g.add("shouldchange", default=123)

        with tempfile.NamedTemporaryFile("w+") as conf:
            conf.file.write('cli: {overwritten: 1, unchanged: "val"}\ngrp: {val: 1}')
            conf.file.close()

            parser = argparse.ArgumentParser("Desc")
            parser.add_argument("--overwritten", type=int, default=0)
            parser.add_argument("--config", default=None)
            parser.add_argument("--unchanged", default=None)

            config.add_config_vars_to_argparse(parser)

            args = parser.parse_args(
                ["--overwritten=42", "--grp.shouldchange=23", f"--config={conf.name}"]
            )

            config.process_config_values(parser, args)

        # Make sure that cmdline flags get precedence
        g = config.get_group("cli")
        self.assertEqual(g.overwritten, 42)
        self.assertEqual(g.unchanged, "val")

        # Make sure that we can update defined vars
        g = config.get_group("grp")
        self.assertEqual(g.val, 1)
        self.assertEqual(g.shouldchange, 23)
