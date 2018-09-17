"""
This file implements a configuration system.

The config values and constant are gathered from three sources:

    1. default values provided at time of definition
    2. ini files (i.e. ./manticore.ini)
    3. command line arguments

in that order of priority.
"""

import ast
import configparser
import io
import logging
import os

from itertools import product


_groups = {}


logger = logging.getLogger(__name__)


class ConfigError(RuntimeError):
    pass


class _var:
    def __init__(self, default=None, description: str=None, defined: bool=True):
        self.description = description
        self.value = default
        self.default = default
        self.defined = defined

    @property
    def was_set(self) -> bool:
        return self.value is not self.default


class _group:
    def __init__(self, name: str):
        # To bypass __setattr__
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, '_vars', {})

    def add(self, name: str, default=None, description: str=None):
        """
        Add a variable named |name| to this value group, optionally giving it a
        default value and a description.

        Variables must be added with this method before they can be set or read.
        Reading a variable replaces the variable that was defined previously, but
        updates the description if a new one is set.

        """
        if name in self._vars:
            raise ConfigError("f{self.name}.{name} already defined.")

        v = _var(description=description, default=default)
        self._vars[name] = v

    def update(self, name: str, default=None, description: str=None):
        """
        Like add, but can tolerate existing values.
        """
        if name in self._vars:
            description = description or self._vars[name].description

        v = _var(description=description, default=default, defined=False)
        self._vars[name] = v

    def get_description(self, name: str) -> str:
        """
        Return the description, or a help string of variable identified by |name|.
        """
        if name not in self._vars:
            raise ConfigError("f{self.name}.{name} not defined.")

        return self._vars[name].description

    def was_set(self, name: str) -> bool:
        return self._vars[name].was_set

    def _var_object(self, name: str) -> _var:
        return self._vars[name]

    def __getattr__(self, name):
        if name not in self._vars:
            raise AttributeError(f"Group '{self.name}' has no variable '{name}'")
        return self._vars[name].value

    def __setattr__(self, name, new_value):
        self._vars[name].value = new_value

    def __iter__(self):
        return iter(self._vars)

    def __contains__(self, key):
        return key in self._vars


def get_group(name: str):
    """
    Get a configuration variable group named |name|
    """
    global _groups

    if name in _groups:
        return _groups[name]

    group = _group(name)
    _groups[name] = group

    return group


def save(f):
    """
    Save current config state to an ini file stream identified by |f|

    :param f: where to write the config file
    """
    global _groups

    c = configparser.ConfigParser()
    for group_name, group in _groups.items():
        if not any(group.was_set(v) for v in group):
            continue
        c.add_section(group_name)
        for var in group:
            if not group.was_set(var):
                continue
            c.set(group_name, var, str(getattr(group, var)))
    c.write(f)


def parse_ini(f):
    """
    Load an ini-formatted configuration from file stream |f|

    :param file f: Where to read the config.
    """

    # This currently does some hacky ast parsing on the literals, but this is in service
    # of having a simpler, ini-style configuration without external dependencies, like
    # a YAML parser, and ini files do not have typed values. 

    c = configparser.ConfigParser()
    c.read_file(f)
    for section_name in c.sections():
        group = get_group(section_name)

        for key, v in c.items(section_name):
            try:
                val = ast.literal_eval(v)
            except ValueError:
                val = v

            group.update(key)
            setattr(group, key, val)


def load_overrides(path=None):
    """
    Load config overrides from the ini file at |path|, or from default paths. If a path
    is provided and it does not exist, raise an exception

    Default paths: ./mcore.ini, ./.mcore.ini, ./manticore.ini, ./.manticore.ini.
    """
    possible_names = ['mcore.ini', 'manticore.ini']
    names = [os.path.join('.', ''.join(x)) for x in product(['', '.'], possible_names)]

    if path is not None:
        names = [path]

    for name in names:
        if os.path.exists(name):
            logger.info(f'Reading configuration from {name}')
            with open(name, 'r') as ini_f:
                parse_ini(ini_f)
            break
    else:
        if path is not None:
            raise FileNotFoundError(f"'{path}' not found for config overrides")


def describe_options():
    """
    """
    global _groups

    s = io.StringIO()

    for group_name, group in _groups.items():
        for key in group:
            obj = group._var_object(key)
            if not obj.defined:
                continue
            s.write(f"{group_name}.{key}\n")
            s.write(f"  default: {obj.default}\n")
            s.write(f"  {obj.description}\n")

    return s.getvalue()

