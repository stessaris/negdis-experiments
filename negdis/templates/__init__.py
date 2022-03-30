from dataclasses import dataclass
from io import TextIOBase
import json
from os import PathLike
from pathlib import Path
from string import Template
from typing import Any, Dict, Iterable, Tuple
import uuid

# see <https://stackoverflow.com/a/20885799>
try:
    import importlib.resources as pkg_resources
except ImportError:
    # Try backported to PY<37 `importlib_resources`.
    import importlib_resources as pkg_resources


Defaults = {
    'predicate_holds': 'ndis_holds',
    'predicate_action': 'ndis_action',
    'predicate_choice': 'ndis_choice',
    'predicate_fixed': 'ndis_fixed',
    'predicate_selected': 'ndis_selected',
    'predicate_constraint': 'ndis_constraint',
    'predicate_constraint_name': 'ndis_constr_name',
    'predicate_constraint_action': 'ndis_constr_action',
    'predicate_rule_head_pttrn': 'ndis_pttrn_in_head',
    'functor_declare': 'decl'
}

@dataclass
class SolverConf():
    """Keeps the parameters for a solver configuration."""
    id: str
    inputs: Iterable[str]
    args: Iterable[str]
    docstring: str
    solver: str = 'clingo'
    template: str = ''
    mapping: Tuple[Tuple[str, str]] = tuple()

    @classmethod
    def from_dict(cls, data: Dict[str, Any], root: Path = None) -> 'SolverConf':
        if root is None:
            root = Path()
        def input_path(p: str) -> str:
            ppath = root.joinpath(p).absolute()
            if ppath.exists():
                return str(ppath)
            else:
                return p

        return cls(
            id=data.get('id', int(uuid.uuid4().hex[:6], base=16)),
            inputs=tuple(input_path(p) for p in data.get('inputs', [])),
            args=tuple(str(a) for a in data.get('args', [])),
            docstring=data.get('docstring', ''),
            solver=data.get('solver', 'clingo'),
            template=data.get('template', ''),
            mapping=tuple(data.get('mapping', {}).items())
        )

    @classmethod
    def from_file(cls, fd: TextIOBase, root: Path = None) -> 'SolverConf':
        if root is None:
            try:
                fd_dir = Path(fd.name).parent
                if fd_dir.is_dir():
                    root = fd_dir
            except Exception:
                pass

        return cls.from_dict(json.load(fd), root=root)


    def program(self, mapping: Dict[str, str] = None, eval: bool = True) -> str:
        """Returns the ASP program by joining evaluating the template definition and the inputs.

        Args:
            mapping (Dict[str, str], optional): use this mapping for the variables in the template
            eval (bool, optional): if true replaces the variables in the template with their values. Defaults to True.

        Returns:
            str: the full program
        """
        def templ_string(path: str) -> str:
            try:
                return Path(path).read_text()
            except Exception:
                pass
            try:
                return pkg_resources.read_text(__package__, path)
            except Exception:
                return ''

        src_template = '\n'.join(templ_string(res) for res in self.inputs) + '\n' + self.template
        if eval:
            return evaluate_template(src_template, dict(self.mapping) if mapping is None else {**dict(self.mapping), **mapping})
        return src_template


def all_templates() -> Iterable[str]:
    return templates_conf().keys()


def template(name: str) -> SolverConf:
    return templates_conf().get(name)


def evaluate_template(templ: str, mapping: Dict[str, Any] = None) -> str:
    if mapping is None:
        mapping = dict()
    return Template(templ).substitute({**Defaults, **mapping})


def read_templates_conf(fd: TextIOBase, root: PathLike = None) -> Dict[str, SolverConf]:
    new_templates: Dict[str, SolverConf] = dict()

    if root is None:
        try:
            fd_path = Path(fd.name)
            if fd_path.exists():
                root = fd_path.parent
        except Exception:
            root = Path()

    try:
        add_configurations_from_data(json.load(fd), root=root)
    except Exception:
        pass

    return add_templates_conf(new_templates)


def add_configurations_from_data(data: Iterable[Dict], root: PathLike = None) -> Dict[str, SolverConf]:
    new_templates: Dict[str, SolverConf] = dict()
    for tmpl_conf in data:
            sconf = SolverConf.from_dict(tmpl_conf, root=root)
            new_templates[sconf.id] = sconf
    return add_templates_conf(new_templates)


_ASP_TEMPLATES = dict()

def templates_conf() -> Dict[str, SolverConf]:
    return _ASP_TEMPLATES


def add_templates_conf(templates: Dict[str, SolverConf]) -> Dict[str, SolverConf]:
    global _ASP_TEMPLATES
    _ASP_TEMPLATES = {**_ASP_TEMPLATES, **templates}
    return _ASP_TEMPLATES


add_configurations_from_data(json.loads(pkg_resources.read_text(__package__, 'solver_configurations.json')))