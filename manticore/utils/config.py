"""
This file implements a configuration system.

The config values and constant are gathered from three sources:

    1. default values provided at time of definition
    2. yml files (i.e. ./manticore.yml)
    3. command line arguments

in that order of priority.
"""
import argparse
import logging
from typing import Dict
from itertools import product
from enum import Enum
import os
import yaml
from difflib import SequenceMatcher

def similar(a, b):
    return SequenceMatcher(None, a, b).ratio()

logger = logging.getLogger(__name__)

class ConfigError(Exception):
    pass


class _Var:
    def __init__(self, name: str = "", default=None, description: str = None,
                 defined: bool = True):
        self.name = name
        self.description = description
        self._value = None
        self.default = default
        self.defined = defined

    @property
    def value(self):
        if self._value is None:
            return self.default
        else:
            return self._value

    @value.setter
    def value(self, val):
        self._value = val

    @property
    def was_set(self) -> bool:
        return self._value is not None


class _Group:
    """
    Configuration group to which you can add variables by simple doing:
        group.add('some_var', default=123, description='..')

    And then use their value in the code as:
        group.some_var

    Can also be used with a `with-statement context` so it would revert the value, e.g.:
    group.var = 100
    with group.temp_vals():
        group.var = 123
        # group.var is 123 for the time of with statement
    # group.var is back to 100

    Note that it is not recommended to use it as a default argument value for a function as it will be evaluated once.
    Also don't forget that a given variable can be set through CLI or .yaml file!
    (see config.py)
    """

    def __init__(self, name: str):
        # To bypass __setattr__
        object.__setattr__(self, "_name", name)
        object.__setattr__(self, "_vars", {})

    @property
    def name(self) -> str:
        return self._name

    def _fail(self, *args, **kwargs):
        raise ConfigError("Frozen group")

    def add(self, name: str, default=None, description: str = None):
        """
        Add a variable named |name| to this value group, optionally giving it a
        default value and a description.

        Variables must be added with this method before they can be set or read.
        Reading a variable replaces the variable that was defined previously, but
        updates the description if a new one is set.

        """
        name = name.replace('-', '_')
        if name in self._vars:
            raise ConfigError(f"{self.name}.{name} already defined.")

        if name == "name":
            raise ConfigError("'name' is a reserved name for a group.")

        v = _Var(name, description=description, default=default)
        self._vars[name] = v

    def update(self, name: str, value=None, default=None,
               description: str = None):
        """
        Like add, but can tolerate existing values; also updates the value.

        Mostly used for setting fields from imported INI files and modified CLI flags.
        """
        name = name.replace('-', '_')
        if name in self._vars:
            description = description or self._vars[name].description
            default = default or self._vars[name].default
        elif name == "name":
            raise ConfigError("'name' is a reserved name for a group.")

        v = _Var(name, description=description, default=default, defined=False)
        v.value = value
        self._vars[name] = v

    def get_description(self, name: str) -> str:
        """
        Return the description, or a help string of variable identified by |name|.
        """
        if name not in self._vars:
            raise ConfigError(f"{self.name}.{name} not defined.")

        return self._vars[name].description

    def updated_vars(self):
        """
        Return all vars that were explicitly set or updated with new values.
        """
        return filter(lambda x: x.value is not None, self._vars.values())

    def _var_object(self, name: str) -> _Var:
        try:
            return self._vars[name]
        except KeyError:
            potentials = sorted(self._vars.keys(), key=lambda x: similar(x, name))
            raise KeyError(
                f"Group '{self.name}' has no variable '{name}'. Try '{potentials[-1]}'")

    def __getattr__(self, name):
        return self._var_object(name).value

    def __setattr__(self, name, new_value):
        self._var_object(name).value = new_value

    def __iter__(self):
        return iter(self._vars)

    def __contains__(self, key):
        return key in self._vars

    def keys(self):
        return self._vars.keys()

    def values(self):
        return self._vars.values()

    def items(self):
        return self._vars.items()

    def __getitem__(self, index):
        return self._vars[index].value

    def temp_vals(self) -> "_TemporaryGroup":
        """
        Returns a contextmanager that can be used to set temporary config variables.
        E.g.:
        group.var = 123

        with group.temp_vals():
            group.var = 456
            # var is 456

        # group.var is back to 123
        """
        return _TemporaryGroup(self)


class _TemporaryGroup:
    def __init__(self, group: _Group):
        object.__setattr__(self, "_group", group)
        object.__setattr__(self, "_entered", False)
        object.__setattr__(self, "_saved",
                           {k: v.value for k, v in group._vars.items()})

    def __getattr__(self, item):
        return getattr(self._grp, item)

    def __setattr__(self, key, value):
        if self._entered and key not in self._saved:
            self._saved[key] = getattr(self._group, key).value

    def __enter__(self):
        if self._entered is True:
            raise ConfigError("Can't use temporary group recursively!")

        object.__setattr__(self, "_entered", True)

    def __exit__(self, *_):
        for k in self._saved:
            setattr(self._group, k, self._saved[k])

        object.__setattr__(self, "_entered", False)


class Config:
    _frozen = False
    _groups: Dict[str, "_Group"] = {}

    def get_group(self, name: str) -> _Group:
        """
        Get a configuration variable group named |name|
        """

        try:
            return self._groups[name]
        except KeyError:
            if self._frozen:
                raise ConfigError("Can not add group on frozen configuration constants")

            group = _Group(name)
            self._groups[name] = group

            return group

    def __getitem__(self, name):
        return self.get_group(name)

    def save(self, f):
        """
        Save current config state to an yml file stream identified by |f|

        :param f: where to write the config file
        """

        c = {}
        for group_name, group in self._groups.items():
            section = {}
            for var in group.values():
                if isinstance(var.value, Enum):
                    section[var.name] = var.value.value
                else:
                    section[var.name] = var.value
            if not section:
                continue
            c[group_name] = section

        yaml.safe_dump(c, f, line_break=True)

    def load(self, f, update=True):
        """
        Load config from an yml-formatted configuration from file stream |f|

        :param file f: Where to read the config.
        :param update: If True update current config with file contents
        """
        if not update:
            self.clear()
        try:
            c = yaml.safe_load(f)
            for section_name, section in c.items():
                group = self.get_group(section_name)

                for key, val in section.items():
                    if key in group:
                        obj = group._var_object(key)
                        if isinstance(obj.default, Enum):
                            val = type(obj.default).from_string(val)
                    group.update(key)
                    setattr(group, key, val)
        # Any exception here should trigger the warning; from not being able to parse yaml
        # to reading poorly formatted values
        except Exception:
            raise ConfigError("Failed reading config file. Do you have a local [.]manticore.yml file?")

    def clear(self, f):
        """Clear current config"""
        if not self._frozen:
            self._groups = {}

    def prepare_argument_parser(self, parser=None):
        """
        Import all defined config vars into |parser|, for parsing command line.
        :param args: A container for argparse vars
        :type args: argparse.ArgumentParser. If None it creates one for you
        :return: the argparse.ArgumentParser
        """

        if parser is None:
            parser = argparse.ArgumentParser(
                description="Symbolic execution tool",
                prog="manticore",
                formatter_class=argparse.ArgumentDefaultsHelpFormatter,
            )

        self["config"].add('file', default=".manticore.yml", description="Overriding defaults for configuration values")

        for group_name, group in self._groups.items():
            args = parser.add_argument_group(group_name)
            for key in group:
                obj = group._var_object(key)
                mykey = key.replace('_', '-')
                if obj.default is False:
                    args.add_argument(
                        f"--{group_name}-{mykey}",
                        action="store_true",
                        default=False,
                        help=obj.description,
                    )
                elif obj.default is True:
                    args.add_argument(
                        f"--{group_name}-{mykey}",
                        action="store_false",
                        default=True,
                        help=obj.description,
                    )
                else:
                    args.add_argument(
                        f"--{group_name}-{mykey}",
                        type=type(obj.default),
                        default=obj.default,
                        help=obj.description,
                        action="store",
                    )
        return parser

    def process_config_values(self, parser: argparse.ArgumentParser, args: argparse.Namespace):
        """
        Bring in provided config values to the args parser, and import entries to the config
        from all arguments that were actually passed on the command line

        :param parser: The arg parser
        :param args: The value that parser.parse_args returned
        """
        try:
            # First, load a local config file, if passed or look for one in pwd if it wasn't.
            self.load(open(getattr(args, 'config_file'),'rb'))
        except (FileNotFoundError,ConfigError):
            pass

        # Get a list of defined config vals. If these are passed on the command line,
        # update them in their correct group, not in the cli group
        defined_vars = list(self.get_config_keys())

        command_line_args = vars(args)

        # Bring in the options keys into args
        config_cli_args = self.get_group("cli")

        # Place all command line args into the cli group (for saving in the workspace). If
        # the value is set on command line, then it takes precedence; otherwise we try to
        # read it from the config file's cli group.
        for k in command_line_args:
            default = parser.get_default(k)
            set_val = getattr(args, k)
            if default is not set_val:
                if k not in defined_vars:
                    config_cli_args.update(k, value=set_val)
                else:
                    # Update a var's native group
                    group_name = k.split("-")[0]
                    key = k[len(group_name)+1:]
                    group = get_group(group_name)
                    setattr(group, key, set_val)
            else:
                if k in config_cli_args:
                    setattr(args, k, getattr(config_cli_args, k))


    def get_config_keys(self):
        """
        Return an iterable covering all defined keys so far
        """
        for group_name, group in self._groups.items():
            for key in group:
                yield f"{group_name}.{key}"

    def freeze(self):
        """
        The disable any further modification of the config parameters.
        """
        self._frozen=True
        for group_name, group in self._groups.items():
            object.__setattr__(group, "__setattr__", group._fail)
            object.__setattr__(group, "add", group._fail)
            object.__setattr__(group, "update", group._fail)


# Different modules will declare the config constants
# import config
# cli_cfg = config.get_group("cli")
# cli_cfg.add("config1", default=False, description="Enable some feature")from_

global_default = Config()

def get_group(name):
    return global_default.get_group(name)

def get_default_config():
    return global_default
