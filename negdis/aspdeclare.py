#!/usr/bin/env python

"""Use clingo ASP solver to minimise the set of constraints that exclude a set of traces. See the negdis project for details.
"""

__version__ = '1.1'

import argparse
from io import StringIO, TextIOBase
import json
import logging
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
from typing import Callable, Dict, Iterable, Sequence, Set, Tuple, TextIO, Union

from . import templates as tmpl
from .templates import SolverConf

NAME_MAP = dict()

# make sure that when running in a venv the PATH is correct
#  solves the problem that venv executables are not picked up when running as jupyter kernel
if os.path.dirname(sys.executable) not in os.pathsep.split(os.environ['PATH']):
    os.environ['PATH'] = os.path.dirname(sys.executable) + os.pathsep + os.environ['PATH']


def asp_facts(predicate: str, facts: Iterable, out: TextIO = None):
    if out is None:
        out = sys.stdout
    for a in facts:
        print('{}({}).'.format(predicate, ','.join(a) if isinstance(a, (list, tuple)) else a), file=out)


def asp_actionname(name: str) -> str:
    return '"' + name + '"'


def asp_constraint(name: str, actions: Iterable[str]) -> str:
    return name + '(' + ','.join(asp_actionname(a) for a in actions) + ')'


def parse_constraint(constraint: str, namemap: Dict[str, str] = NAME_MAP) -> Tuple[str, Sequence[str]]:
    def normalise_constraint(name: str) -> str:
        nname = name.lower().replace(' ', '_')
        if nname != name and nname not in namemap:
            namemap[nname] = name
            logging.info(f'Constraint name normalised: {name} -> {nname}')
        return nname

    def normalise_activities(activities: Sequence[str]) -> Sequence[str]:
        return [a.replace('\\', '\\\\').replace('"', '\\"') for a in activities]

    m = re.fullmatch(r'\s*(?P<name>[\w ]+)\((?P<args>[\w, -_]+)\)\s*', constraint)
    if m:
        cname = normalise_constraint(m.group('name').strip())
        args = normalise_activities([a.strip() for a in m.group('args').split(',')])
        return cname, args
    else:
        logging.fatal('cannot parse <{}> constraint'.format(constraint))
        return None, None


def choices2asp(fp: TextIO, actions: Set[str], out: TextIO = None, tid: int = 0, choicep: str = None) -> int:
    """Converts JSON files as produced by `negdis discover negative`:

    [ {choices: [<constraint>, ...], trace: [<event>, ...]}, ... ]

    into ASP facts.

    Args:
        fp ([type]): [description]
        out ([type], optional): [description]. Defaults to sys.stdout.
        tcount (int, optional): [description]. Defaults to 0.

    Returns:
        int: the last id of the trace
    """
    if out is None:
        out = sys.stdout
    if choicep is None:
        choicep = tmpl.Defaults['predicate_choice']

    choice_pred = []
    choices = json.load(fp)
    tc = tid
    for choice in choices:
        tc += 1
        actions.update(choice.get('trace', []))
        for c_str in choice.get('choices', []):
            cname, args = parse_constraint(c_str)
            if cname is not None:
                actions.update(args)
                choice_pred.append((str(choice.get('id', tc)), asp_constraint(cname, args)))

    asp_facts(choicep, choice_pred, out=out)
    return tid


def constraints2asp(inf: TextIO, actions: Set[str], outf: TextIO = None, holdsp: str = None, actionp: str = None):

    if outf is None:
        outf = sys.stdout

    if holdsp is None:
        holdsp = tmpl.Defaults['predicate_holds']

    holds_facts = []
    for line in inf:
        cname, args = parse_constraint(line)
        if cname is not None:
            actions.update(args)
            holds_facts.append(asp_constraint(cname, args))

    asp_facts(holdsp, holds_facts, out=outf)


def read_declare_patterns(infile) -> Set[str]:
    decl_templates = set()
    for line in infile:
        m = re.match(r'\A\s*(?P<name>(\w|_|\s)+)\s*\([^)]*\)\s*:', line)
        if m:
            decl_templates.add(m.group('name').lower())
    logging.info('Known templates: {}'.format(decl_templates))
    return decl_templates


def rules2asp(inf: TextIO, outf: TextIO = None, holdsp: str = None, actionp: str = None, templates: Set[str] = None):
    """Convert a set of rules of the form:

    head <- body_term_1 & ... & body_term_n

    to a set of ASP rules

    Args:
        inf ([type]): [description]
        outf ([type], optional): [description]. Defaults to sys.stdout.
    """
    if outf is None:
        outf = sys.stdout

    if holdsp is None:
        holdsp = tmpl.Defaults['predicate_holds']

    if actionp is None:
        actionp = tmpl.Defaults['predicate_action']

    def parse_rule(expr):
        atom_exp = r'(¬|-|!)?\s*(\b(\w|_)+\b\((\w|\s|,)*\))'
        imp_exp = r'(⊑|<-)'
        and_exp = r'(&)'

        var_exp = r'\b[A-Z_](\w|_)*\b'

        rule_exp = f'^\\s*(?P<head>{atom_exp})\\s*{imp_exp}\s*(?P<body>{atom_exp}(\\s*{and_exp}\\s*{atom_exp})*)\\s*$'

        def atoms(expr):
            return [(m.group(1), m.group(2)) for m in re.finditer(atom_exp, expr)]

        def all_vars(expr):
            vs = set()
            for ar in re.findall(r'\([^)]*\)', expr):
                vs.update([m.group(0) for m in re.finditer(var_exp, ar)])
            return vs

        m = re.match(rule_exp, expr)
        if m:
            head = atoms(m.groupdict()['head'])[0]
            head_vars = all_vars(m.groupdict()['head'])
            body = atoms(m.groupdict()['body'])
            body_vars = all_vars(m.groupdict()['body'])
            return head, body, head_vars.union(body_vars), head_vars.difference(body_vars)
        else:
            logging.info('Unsupported rule, discarding rule "{}"'.format(expr.strip()))
            return(None,) * 4

    def rule2asp(head, body, unbound) -> str:
        def holds(atom):
            return ('-' if atom[0] else '') + ('{}({})'.format(holdsp, atom[1]) if holdsp else atom[1])

        def bound(v):
            return '{}({})'.format(actionp, v)

        return holds(head) + ' :- ' + ', '.join([holds(a) for a in body] + [bound(v) for v in unbound]) + '.'

    for line in inf:
        head, body, variables, unbound = parse_rule(line)
        if head:
            print(rule2asp(head, body, unbound), file=outf)


def asp_problem(choices: TextIO, rules: TextIO = None, positives: TextIO = None, main: Union[str, TextIO] = '', outf: TextIO = None, actionp: str = None):
    """Generate the minimisation ASP problem to be fed into the solver

    Args:
        choices ([type]): [description]
        rules ([type], optional): [description]
        positives ([type], optional): [description]
        main ([type], optional): [description]
        outf (io.TextIOBase, optional): [description]. Defaults to sys.stdout.
        templates (Set[str], optional): [description]. Defaults to None

    Returns:
        [type]: [description]
    """
    if outf is None:
        outf = sys.stdout

    if actionp is None:
        actionp = tmpl.Defaults['predicate_action']

    def section(name):
        print('\n' + ('%' * 30) + '\n%%%% ' + name + '\n', file=outf)

    actions = set()
    section('Choices')
    choices2asp(choices, actions, out=outf)
    if positives is not None:
        section('Positive')
        constraints2asp(positives, actions, outf=outf)

    section('Actions')
    asp_facts(actionp, [asp_actionname(a) for a in actions], out=outf)

    if rules is not None:
        section('Declare rules')
        rules2asp(rules, outf=outf)

    section('Main')
    if isinstance(main, str):
        outf.write(main)
    else:
        outf.write(tmpl.evaluate_template(main.read(), dict()))


def run_clingo(program: Union[str, TextIOBase], clingo: os.PathLike='clingo', models: int=1, args: Sequence[str]=[], timeout: float = None) -> Dict:

    is_asprin = clingo.lower().endswith('asprin')

    clingo_cmd = [clingo]
    if models != 1:
        clingo_cmd += ['--models', str(models)]
    if timeout is not None and not is_asprin:
        clingo_cmd.append('--time-limit={}'.format(int(timeout)))
    if is_asprin:
        # remove arguments not supported by asprin
        def valid(arg: str) -> bool:
            return not arg.startswith('--outf=')
        clingo_cmd += [str(a) for a in args if valid(a)]
    else:
        clingo_cmd += [str(a) for a in args]

    logging.info('running: ' + ' '.join(shlex.quote(str(a)) for a in clingo_cmd))
    hard_timeout = timeout * 1.2 if timeout is not None else None
    timedout = False
    try:
        if isinstance(program, TextIOBase):
            cp = subprocess.run(clingo_cmd, timeout=hard_timeout, capture_output=True, text=True, stdin=program)
        else:
            cp = subprocess.run(clingo_cmd, timeout=hard_timeout, capture_output=True, text=True, input=program)
    except subprocess.TimeoutExpired as e:
        logging.warning('Clingo process timed out')
        return {
            'cmd': e.cmd,
            'timeout': e.timeout,
            'stdout': e.stdout.decode(),
            'stderr': e.stderr.decode()
        }

    try:
        clingo_out = json.loads(cp.stdout)
    except json.JSONDecodeError as e:
        logging.info(f'Error parsing clingo JSON output: {e}')
        clingo_out = {'stdout': cp.stdout}

    clingo_out['stderr'] = cp.stderr
    clingo_out['cmd'] = cp.args
    clingo_out['returnstatus'] = cp.returncode

    return clingo_out

def parse_clingo_json(clingo_out: Dict, namemap: Dict[str, str] = NAME_MAP, selectedp: str = None) -> Sequence[Sequence[str]]:
    if selectedp is None:
        selectedp = tmpl.Defaults['predicate_selected']

    def get_selected(atoms):
        selected = []
        for a in atoms:
            m = re.match(r'\A\s*' + selectedp + r'\((?P<cname>([\w]+))\((?P<args>(.+))\)\)\s*\Z', a)
            if m:
                cname = namemap.get(m.group('cname'), m.group('cname'))
                args = [a.strip().strip('"') for a in m.group('args').split(',')]
                selected.append('{}({})'.format(cname, ','.join(args)))
        return selected

    return [get_selected(witness.get('Value', [])) for call in clingo_out.get('Call', []) for witness in call.get('Witnesses', {})]


def solve_optimisation_problem(data_id: str, choices: TextIO, rules: TextIO, positives: TextIO, main: Union[str, TextIO], models: int, solver: str, extra_args: Sequence[str], timeout: float, raw: bool = False) -> Dict:
    if data_id is None:
        try:
            data_id = Path(choices.name).stem
        except Exception:
            data_id = ''

    if not raw and not any(a.startswith('--outf=') for a in extra_args):
        extra_args = ['--outf=2'] + extra_args
    with StringIO() as asp_if:
        asp_problem(choices, rules=rules, positives=positives, main=main, outf=asp_if)

        clingo_out = run_clingo(asp_if.getvalue(), clingo=solver, models=models, timeout=timeout, args=extra_args)

    results = {'id': data_id} if data_id else dict()
    if 'Call' in clingo_out:
        # it's the clingo JSON output
        results['selected'] = parse_clingo_json(clingo_out)
    results['clingo'] = clingo_out

    return results


def optimise(mode: Union[str, SolverConf], choices: TextIO, rules: TextIO, positives: TextIO = None, data_id: str = None, models: int = 1, outf: TextIO = None, raw: bool = False, timeout: float = None, mapping: Dict[str, str] = None) -> Dict:
    template = solver_configuration(mode)
    return solve_optimisation_problem(
        data_id=data_id,
        choices=choices, rules=rules, positives=positives,
        main=template.program(mapping=mapping),
        models=models,
        solver=template.solver,
        extra_args=list(template.args),
        timeout=timeout,
        raw=raw
    )


def update_templates(src: Union[os.PathLike, TextIOBase]) -> Dict[str, SolverConf]:
    if isinstance(src, TextIOBase):
        return tmpl.read_templates_conf(src)
    else:
        with open(src) as fd:
            return tmpl.read_templates_conf(fd)


def templates() -> Dict[str, SolverConf]:
    return tmpl.templates_conf()

def solver_configuration(opt_mode: Union[str, SolverConf]) -> SolverConf:
    return opt_mode if isinstance(opt_mode, SolverConf) else templates()[opt_mode]

####################################################
#
# CLI interface


def print_version(args: argparse.Namespace) -> int:
    print('{} {}'.format(os.path.basename(__file__), __version__))
    return 0


def convert_rules(args: argparse.Namespace) -> int:
    """Convert a set of rules of the form head <- body to a set of ASP rules"""
    rules2asp(args.rules, outf=args.out)
    return 0


def convert_choices(args: argparse.Namespace) -> int:
    """Convert a negdis choice file to a set of ASP facts"""
    choices2asp(args.choices, set(), out=args.out)
    return 0


def generate_problem(args: argparse.Namespace) -> int:
    """Generate the ASP file for the input"""

    asp_problem(args.choices, rules=args.rules, positives=args.pos,
        main=tmpl.template(args.defmain).program() if args.defmain else args.main,
        outf=args.out)
    return 0


def run_cmd(args: argparse.Namespace) -> int:

    try:
        data_id = Path(args.choices).stem
    except Exception:
        data_id = ''

    results = solve_optimisation_problem(
        data_id=data_id,
        choices=args.choices, rules=args.rules, positives=args.pos,
        main=tmpl.template(args.defmain).program() if args.defmain else args.main,
        models=args.models,
        solver=args.clingo if args.clingo else tmpl.template(args.defmain).solver,
        extra_args=shlex.split(args.extra) + (tmpl.template(args.defmain).args if args.defmain else []),
        timeout=args.timeout,
        raw=args.raw
    )

    if args.json:
        json.dump(results, args.out)
    else:
        if args.raw or 'selected' not in results:
            clingo_results = results.get('clingo', dict())
            if 'stdout' in clingo_results:
                args.out.write(clingo_results['stdout'])
            else:
                json.dump(clingo_results, args.out)
        else:
            for model in sorted(results.get('selected', []), key=len):
                print('[' + ', '.join([f'"{s}"' for s in sorted(model)]) + ']', file=args.out)
            try:
                if results['clingo']['Models']['More'] != 'no':
                    print('Missing models...', file=args.out)
            except Exception:
                pass

    return results['clingo']['returnstatus']


def main(cargs) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter, prog=os.path.basename(__file__))
    parser.add_argument("-v", "--verbose", help="increase output verbosity", action='count', default=0)
    parser.add_argument('--version', action='version', version='%(prog)s {}'.format(__version__))
    subparsers = parser.add_subparsers()

    def add_command(name: str, action: Callable, help: str = None) -> argparse.ArgumentParser:
        sp = subparsers.add_parser(name, help=action.__doc__ if help is None else help)
        sp.set_defaults(func=action)
        return sp

    _ = add_command('version', print_version)

    cmd_parser = add_command('rules', convert_rules)
    cmd_parser.add_argument('rules', type=argparse.FileType(), help='file with the rules')
    cmd_parser.add_argument('--out', type=argparse.FileType('w'), default=sys.stdout, help='output file')

    cmd_parser = add_command('choices', convert_choices)
    cmd_parser.add_argument('choices', type=argparse.FileType(), help='negdis choice file')
    cmd_parser.add_argument('--out', type=argparse.FileType('w'), default=sys.stdout, help='output file')

    cmd_parser = add_command('asp', generate_problem)
    cmd_parser.add_argument('--out', type=argparse.FileType('w'), default=sys.stdout, help='output file')
    cmd_parser.add_argument('--defmain', type=str, default=None, choices=sorted(tmpl.all_templates()), help='use default ASP main file with optimization options (one of [%(choices)s])')
    cmd_parser.add_argument('--main', type=argparse.FileType(), help='main ASP file to be prepended')
    cmd_parser.add_argument('--pos', type=argparse.FileType(), help='positive Declare constraints')
    cmd_parser.add_argument('--rules', type=argparse.FileType(), help='Declare rules file')
    cmd_parser.add_argument('--templ', type=argparse.FileType(), help='Declare templates file')
    cmd_parser.add_argument('choices', type=argparse.FileType(), help='negdis choice file')

    cmd_parser = add_command('run', run_cmd)
    cmd_parser.add_argument('--out', type=argparse.FileType('w'), default=sys.stdout, help='output file')
    cmd_parser.add_argument('--defmain', type=str, default=None, choices=sorted(tmpl.all_templates()), help='use default ASP main file with optimization options (one of [%(choices)s])')
    cmd_parser.add_argument('--json', action='store_true', default=False, help='JSON output')
    cmd_parser.add_argument('--raw', action='store_true', default=False, help='raw clingo output')
    cmd_parser.add_argument('--models', '-n', type=int, default=1, help='generates more optimal models (0 for all)')
    cmd_parser.add_argument('--clingo', type=str, help='clingo executable')
    cmd_parser.add_argument('--extra', type=str, default='', help='clingo extra arguments')
    cmd_parser.add_argument('--timeout', type=float, default=None, help='timeout for clingo executable')
    cmd_parser.add_argument('--main', type=argparse.FileType(), help='main ASP file to be prepended')
    cmd_parser.add_argument('--pos', type=argparse.FileType(), help='positive Declare constraints')
    cmd_parser.add_argument('--rules', type=argparse.FileType(), help='Declare rules file')
    cmd_parser.add_argument('--templ', type=argparse.FileType(), help='Declare templates file')
    cmd_parser.add_argument('choices', type=argparse.FileType(), help='negdis choice file')

    if len(cargs) < 1:
        parser.print_help(sys.stderr)
        return 0

    args = parser.parse_args(cargs)
    if args.verbose > 1:
        logging.basicConfig(level=logging.DEBUG)
    elif args.verbose > 0:
        logging.basicConfig(level=logging.INFO)

    return args.func(args)


def cli():
    sys.exit(main(sys.argv[1:]))


if __name__ == "__main__":
    cli()
