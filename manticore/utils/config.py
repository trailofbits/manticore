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

_groups: Dict[str, "_Group"] = {}


logger = logging.getLogger(__name__)


class ConfigError(Exception):
    pass


class ConfigEnum(Enum):
    """Used as configuration constant for choosing flavors"""

    def title(self):
        return self._name_.title()

    @classmethod
    def from_string(cls, name):
        return cls.__members__[name]


class _Var:
    def __init__(self, name: str = "", default=None, description: str = None, defined: bool = True):
        self.name = name
        self.description = description
        self._value = default
        self.default = default
        self.defined = defined

    @property
    def was_set(self) -> bool:
        return self.value is not self.default

    @property
    def value(self):
        return self._value

    @value.setter
    def value(self, val):
        # Forgiveness/Enums support from_string
        if isinstance(self.default, Enum) and isinstance(val, str):
            self._value = self.default.from_string(val)
        else:
            self._value = val


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

    def add(self, name: str, default=None, description: str = None):
        """
        Add a variable named |name| to this value group, optionally giving it a
        default value and a description.

        Variables must be added with this method before they can be set or read.
        Reading a variable replaces the variable that was defined previously, but
        updates the description if a new one is set.

        """
        if name in self._vars:
            # Be kind when double-adding the same exact config
            existing = self._vars[name]
            if default == existing.default and description == existing.description:
                return
            raise ConfigError(f"{self.name}.{name} already defined.")

        if name == "name":
            raise ConfigError("'name' is a reserved name for a group.")

        v = _Var(name, description=description, default=default)
        self._vars[name] = v

    def update(self, name: str, value=None, default=None, description: str = None):
        """
        Like add, but can tolerate existing values; also updates the value.

        Mostly used for setting fields from imported INI files and modified CLI flags.
        """
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
        return filter(lambda x: x.was_set, self._vars.values())

    def _var_object(self, name: str) -> _Var:
        return self._vars[name]

    def __getattr__(self, name):
        try:
            return self._vars[name].value
        except KeyError:
            raise AttributeError(f"Group '{self.name}' has no variable '{name}'")

    def __setattr__(self, name, new_value):
        self._vars[name].value = new_value

    def __iter__(self):
        return iter(self._vars)

    def __contains__(self, key):
        return key in self._vars

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
        object.__setattr__(self, "_saved", {k: v.value for k, v in group._vars.items()})

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


def get_group(name: str) -> _Group:
    """
    Get a configuration variable group named |name|
    """
    global _groups

    if name in _groups:
        return _groups[name]

    group = _Group(name)
    _groups[name] = group

    return group


def save(f):
    """
    Save current config state to an yml file stream identified by |f|

    :param f: where to write the config file
    """
    global _groups

    c = {}
    for group_name, group in _groups.items():
        section = {}
        for var in group.updated_vars():
            if isinstance(var.value, Enum):
                section[var.name] = var.value.value
            else:
                section[var.name] = var.value
        if not section:
            continue
        c[group_name] = section

    yaml.safe_dump(c, f, line_break=True)


def parse_config(f):
    """
    Load an yml-formatted configuration from file stream |f|

    :param file f: Where to read the config.
    """

    try:
        c = yaml.safe_load(f)
        for section_name, section in c.items():
            group = get_group(section_name)

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


def load_overrides(path=None):
    """
    Load config overrides from the yml file at |path|, or from default paths. If a path
    is provided and it does not exist, raise an exception

    Default paths: ./mcore.yml, ./.mcore.yml, ./manticore.yml, ./.manticore.yml.
    """

    if path is not None:
        names = [path]
    else:
        possible_names = ["mcore.yml", "manticore.yml"]
        names = [os.path.join(".", "".join(x)) for x in product(["", "."], possible_names)]

    for name in names:
        try:
            with open(name, "r") as yml_f:
                logger.info(f"Reading configuration from {name}")
                parse_config(yml_f)
            break
        except FileNotFoundError:
            pass
    else:
        if path is not None:
            raise FileNotFoundError(f"'{path}' not found for config overrides")


def add_config_vars_to_argparse(args):
    """
    Import all defined config vars into |args|, for parsing command line.
    :param args: A container for argparse vars
    :type args: argparse.ArgumentParser or argparse._ArgumentGroup
    :return:
    """
    global _groups
    for group_name, group in _groups.items():
        for key in group:
            obj = group._var_object(key)
            args.add_argument(
                f"--{group_name}.{key}",
                type=type(obj.default),
                default=obj.default,
                help=obj.description,
            )


def process_config_values(parser: argparse.ArgumentParser, args: argparse.Namespace):
    """
    Bring in provided config values to the args parser, and import entries to the config
    from all arguments that were actually passed on the command line

    :param parser: The arg parser
    :param args: The value that parser.parse_args returned
    """
    # First, load a local config file, if passed or look for one in pwd if it wasn't.
    if hasattr(args, "config"):
        load_overrides(args.config)

    # Get a list of defined config vals. If these are passed on the command line,
    # update them in their correct group, not in the cli group
    defined_vars = list(get_config_keys())

    command_line_args = vars(args)

    # Bring in the options keys into args
    config_cli_args = get_group("cli")

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
                group_name, key = k.split(".")
                group = get_group(group_name)
                setattr(group, key, set_val)
        else:
            if k in config_cli_args:
                setattr(args, k, getattr(config_cli_args, k))


def get_config_keys():
    """
    Return an iterable covering all defined keys so far
    """
    global _groups
    for group_name, group in _groups.items():
        for key in group:
            yield f"{group_name}.{key}"
