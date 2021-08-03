from typing import Dict, Iterable, Tuple

# see <https://stackoverflow.com/a/20885799>
try:
    import importlib.resources as pkg_resources
except ImportError:
    # Try backported to PY<37 `importlib_resources`.
    import importlib_resources as pkg_resources


ASP_TEMPLATES = {
    'guess': {
        'inputs': ['guess.lp'],
        'args': ['--warn', 'no-atom-undefined'],
        'docstring': ''
    },
    'maxclosure': {
        'inputs': ['count_closure.py.lp'],
        'args': ['--outf=3', '--warn', 'no-atom-undefined'],
        'docstring': ''
    },
    'plain': {
        'inputs': ['guess.lp', 'main_plain.py.lp'],
        'args': ['--warn', 'no-atom-undefined'],
        'docstring': 'No optimisation'
    },
    'subsetclos': {
        'inputs': ['guess.lp', 'main_iter.py.lp'],
        'args': ['--warn', 'no-atom-undefined'],
        'docstring': 'Minimal cardinality wrt the closure, and selected constraints for ties'
    },
    'minclos': {
        'inputs': ['guess.lp', 'main_countclos.py.lp'],
        'args': ['--warn', 'no-atom-undefined', '--quiet=1'],
        'docstring': 'Minimal cardinality wrt the closure constraints, and selected constraints for ties'
    }
}


def all_templates() -> Iterable[str]:
    return ASP_TEMPLATES.keys()


def template(name: str) -> Dict:
    return ASP_TEMPLATES.get(name, dict([]))


def clingo_args(name: str) -> Tuple[str]:
    return tuple(template(name).get('args', []))


def clingo_program(name: str) -> str:
    asp_template = template(name)
    asp_prog = ''
    for res in asp_template.get('inputs', []):
        asp_prog += pkg_resources.read_text(__package__, res)
    return asp_prog
