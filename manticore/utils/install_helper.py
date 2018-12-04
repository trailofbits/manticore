REQUIREMENTS_TO_IMPORTS = {
    'native': {
        'capstone': 'capstone',
        'pyelftools': 'elftools',
        'unicorn': 'unicorn'
    }
}


def ensure_native_deps():
    if not _has_native:
        raise ImportError(
            'Missing some packages for native binary analysis. Please install them with pip install manticore[native].'
        )


def _has_deps(deps):
    for pkg, import_name in REQUIREMENTS_TO_IMPORTS[deps].items():
        try:
            __import__(import_name)
        except ImportError:
            return False

    return True


_has_native = _has_deps('native')

