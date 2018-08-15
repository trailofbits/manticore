import configparser
import os
import copy

#  These are not stored in __main__.py as they are used outside of the CLI
defaults = {
    'env': [],
    'files': [],
    'offset': 16,
    'policy': 'random',
    'procs': 1,
    'timeout': 0,
    'v': 1,
    'txaccount': 'attacker',
    'solver_timeout': 240000,
    'cache_dict_max_size': 150000,
    'cache_dict_flush_perc': 25
}


def _config(path: str = None) -> configparser.ConfigParser:
    """
    Initialize the defaults and override with settings from configuration.
    order of precedence;
        path kwarg
        ./.manticorerc
        ${HOME}/.manticorerc

    :param path: path to a config file
    :return:
    """
    global settings
    settings = copy.deepcopy(defaults)
    config_name = '.manticorerc'
    conf_file = configparser.ConfigParser()
    _user_config_path = os.path.join(os.getenv('HOME', None), config_name)
    _cwd_config_path = os.path.join(os.getcwd(), config_name)
    if path and os.path.exists(path) and os.path.isfile(path):
        conf_file.read(path)
    elif os.path.exists(_cwd_config_path) and os.path.isfile(_cwd_config_path):
        conf_file.read(_cwd_config_path)
    elif os.path.exists(_user_config_path) and os.path.isfile(_user_config_path):
        conf_file.read(_user_config_path)
    return conf_file
