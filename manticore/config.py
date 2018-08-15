import configparser
import os


def _config(path=None) -> configparser.ConfigParser:
    config_name = '.manticorerc'
    settings = configparser.ConfigParser()
    _user_config_path = os.path.join(os.getenv('HOME', None), config_name)
    _cwd_config_path = os.path.join(os.getcwd(), config_name)
    if path and os.path.exists(path) and os.path.isfile(path):
        settings.read(path)
    elif os.path.exists(_cwd_config_path) and os.path.isfile(_cwd_config_path):
        settings.read(_cwd_config_path)
    elif os.path.exists(_user_config_path) and os.path.isfile(_user_config_path):
        settings.read(_user_config_path)
    return settings


settings: configparser.ConfigParser = _config()
