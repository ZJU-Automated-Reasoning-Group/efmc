import json
import os

CONFIG_FILES = [
    'config.json',
    '../config.json',
    'config.json.sample',
    '../config.json.sample',
]


def config_file_list():
    return CONFIG_FILES


def check_config_exists(name):
    if name is not None:
        if os.path.exists(name):
            return True
        else:
            return False

    for file in CONFIG_FILES:
        if os.path.exists(file):
            return True
    return False


def get_default_solver_from_config(name):
    for fname in CONFIG_FILES:
        if not os.path.exists(fname):
            continue
        with open(fname, 'r') as f:
            config = json.load(f)
        return config[name]['bin']
    else:
        raise Exception("Please configure config.json correctly or run from " +\
            "the correct directory")


def get_default_tmp_dir():
    for fname in CONFIG_FILES:
        if not os.path.exists(fname):
            continue
        with open(fname, 'r') as f:
            config = json.load(f)
        return config["tempdir"]
    else:
        raise Exception("Please configure config.json correctly or run from " +\
            "the correct directory")