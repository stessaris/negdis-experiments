#!/usr/bin/env python

"""Use clingo ASP solver to minimise the set of constraints that exclude a set of traces. See the negdis project for details.
"""

__version__ = '1.0'

import argparse
import io
import json
import logging
import os
import re
import shlex
import subprocess
import sys
import tempfile
from typing import Any, Callable, Dict, Iterable, Sequence, Set, Tuple, TextIO, Union

from . import templates as tmpl

HOLDS_PRED = 'holds'
ACTION_PRED = 'action'
CHOICE_PRED = 'choice'

NAME_MAP = dict()


def asp_facts(predicate: str, facts: Iterable, out: io.TextIOBase = sys.stdout):
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

    m = re.fullmatch(r'\s*(?P<name>[\w ]+)\((?P<args>[\w, ]+)\)\s*', constraint)
    if m:
        cname = normalise_constraint(m.group('name').strip())
        args = normalise_activities([a.strip() for a in m.group('args').split(',')])
        return cname, args
    else:
        logging.fatal('cannot parse <{}> constraint'.format(constraint))
        return None, None


def choices2asp(fp, actions: Set[str], out=sys.stdout, tid: int = 0) -> int:
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
    choice_pred = []
    choices = json.load(fp)
    tc = tid
    for choice in choices:
        tc += 1
        id = choice.get('id', tc)
        actions.update(choice.get('trace', []))
        for c_str in choice.get('choices', []):
            cname, args = parse_constraint(c_str)
            if cname is not None:
                actions.update(args)
                choice_pred.append((str(id), asp_constraint(cname, args)))

    asp_facts(CHOICE_PRED, choice_pred, out=out)
    return tid


def constraints2asp(inf, actions: Set[str], outf=sys.stdout, holdsp=HOLDS_PRED, actionp=ACTION_PRED):
    holds_facts = []
    for line in inf:
        cname, args = parse_constraint(line)
        if cname is not None:
            actions.update(args)
            holds_facts.append(asp_constraint(cname, args))

    asp_facts(HOLDS_PRED, holds_facts, out=outf)


def get_templates(infile) -> Set[str]:
    decl_templates = set()
    for line in infile:
        m = re.match(r'\A\s*(?P<name>(\w|_|\s)+)\s*\([^)]*\)\s*:', line)
        if m:
            decl_templates.add(m.group('name').lower())
    logging.info('Known templates: {}'.format(decl_templates))
    return decl_templates


def rules2asp(inf, outf=sys.stdout, holdsp=HOLDS_PRED, actionp=ACTION_PRED, templates: Set[str] = None):
    """Convert a set of rules of the form:

    head <- body_term_1 & ... & body_term_n

    to a set of ASP rules

    Args:
        inf ([type]): [description]
        outf ([type], optional): [description]. Defaults to sys.stdout.
    """

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

        def all_templates(expr):
            return set(m.group(1) for m in re.finditer(r'\b((\w|_)+)\(', expr))

        m = re.match(rule_exp, expr)
        if m:
            head = atoms(m.groupdict()['head'])[0]
            head_vars = all_vars(m.groupdict()['head'])
            body = atoms(m.groupdict()['body'])
            body_vars = all_vars(m.groupdict()['body'])
            if templates is not None:
                unknown_templates = all_templates(expr).difference(templates)
                if len(unknown_templates) > 0:
                    logging.info('Unknown template(s) {}, discarding rule "{}"'.format(unknown_templates, expr.strip()))
                    return (None,) * 4
            return head, body, head_vars.union(body_vars), head_vars.difference(body_vars)
        else:
            logging.info('Unsupported rule, discarding rule "{}"'.format(expr.strip()))
            return(None,) * 4

    def rule2asp(head, body, variables, unbound, holdsp=HOLDS_PRED, actionp=ACTION_PRED) -> str:
        def holds(atom):
            return ('-' if atom[0] else '') + ('{}({})'.format(holdsp, atom[1]) if holdsp else atom[1])

        def bound(variables):
            return ['{}({})'.format(actionp, v) for v in variables]

        return holds(head) + ' :- ' + ', '.join([holds(a) for a in body] + bound(unbound)) + '.'

    for line in inf:
        head, body, variables, unbound = parse_rule(line)
        if head:
            print(rule2asp(head, body, variables, unbound, holdsp=holdsp, actionp=actionp), file=outf)


def asp_problem(choices, rules=None, positives=None, main=Union[str, Iterable], outf: io.TextIOBase = sys.stdout, templates: Set[str] = None):
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

    def section(name):
        print('\n' + ('%' * 30) + '\n%%%% ' + name + '\n', file=outf)

    actions = set()
    section('Choices')
    choices2asp(choices, actions, out=outf)
    if positives is not None:
        section('Positive')
        constraints2asp(positives, actions, outf=outf)

    section('Actions')
    asp_facts(ACTION_PRED, [asp_actionname(a) for a in actions], out=outf)

    if rules is not None:
        section('Declare rules')
        rules2asp(rules, outf=outf, templates=templates)

    section('Main')
    if isinstance(main, str):
        print(main, file=outf)
    else:
        for line in main:
            print(line, file=outf)


def run_clingo(infile, outf: TextIO = None, clingo='clingo', models=1, args=[], timeout: float = None, capture: bool = False) -> subprocess.CompletedProcess:
    clingo_cmd = [clingo, '--warn', 'no-atom-undefined']
    if models != 1:
        clingo_cmd += ['--models', str(models)]
    if timeout is not None:
        clingo_cmd.append('--time-limit={}'.format(int(timeout)))
    clingo_cmd += args

    clingo_cmd.append(infile)

    logging.info('running {}'.format(clingo_cmd))
    hard_timeout = timeout * 1.2 if timeout is not None else None
    try:
        if capture:
            cp = subprocess.run(clingo_cmd, timeout=hard_timeout, capture_output=True, text=True)
            if outf is not None:
                outf.write(cp.stdout)
        else:
            cp = subprocess.run(clingo_cmd, timeout=hard_timeout, stdout=outf, text=True)

        return cp
    except subprocess.TimeoutExpired:
        logging.warning('Clingo process timed out')
        return None


def parse_clingo_JSON(clingo_out: str, namemap: Dict[str, str] = NAME_MAP) -> Dict[str, Any]:
    def get_selected(atoms):
        selected = []
        for a in atoms:
            m = re.match(r'\A\s*selected\((?P<cname>([\w]+))\((?P<args>(.+))\)\)\s*\Z', a)
            if m:
                cname = namemap.get(m.group('cname'), m.group('cname'))
                args = [a.strip().strip('"') for a in m.group('args').split(',')]
                selected.append('{}({})'.format(cname, ','.join(args)))
        return selected

    clingo_out_obj = json.loads(clingo_out)
    models = []
    for call in clingo_out_obj.get('Call', []):
        for witness in call.get('Witnesses', {}):
            models.append(get_selected(witness.get('Value', [])))

    return {'selected': models, 'clingo': clingo_out_obj}


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
    choices2asp(args.choices, out=args.out)
    return 0


def generate_problem(args: argparse.Namespace) -> int:
    """Generate the ASP file for the input"""

    if args.defmain is not None:
        asp_main = tmpl.clingo_program(args.defmain)
    else:
        asp_main = args.main if args.main is not None else []

    asp_problem(args.choices, rules=args.rules, positives=args.pos, main=asp_main, outf=args.out, templates=get_templates(args.templ) if args.templ else None)
    return 0


def run_problem(args: argparse.Namespace) -> int:
    """Generate the ASP file for the input and run clingo"""

    if args.defmain is not None:
        asp_main = tmpl.clingo_program(args.defmain)
    else:
        asp_main = args.main if args.main is not None else []

    fp = tempfile.NamedTemporaryFile(delete=False, mode='w+', encoding='utf-8')
    asp_if = fp.name
    logging.info('writing ASP file to {}'.format(asp_if))
    asp_problem(args.choices, rules=args.rules, positives=args.pos, main=asp_main, outf=fp, templates=get_templates(args.templ) if args.templ else None)
    fp.close()

    extra_args = shlex.split(args.extra)
    if args.defmain is not None:
        extra_args.extend(tmpl.clingo_args(args.defmain))
    if args.json or not args.raw:
        extra_args.append('--outf=2')

    cp = run_clingo(asp_if, outf=args.out if args.raw else None, clingo=args.clingo, models=args.models, timeout=args.timeout, args=extra_args, capture=not args.raw)

    if not args.raw and cp is not None:
        # parse clingo JSON output
        result = parse_clingo_JSON(cp.stdout)
        if not args.json:
            for model in sorted(result['selected'], key=len):
                print('[' + ', '.join([f'"{s}"' for s in sorted(model)]) + ']', file=args.out)
            if result['clingo']['Models']['More'] != 'no':
                print('Missing models...')
        else:
            result['args'] = {k: str(v) for k, v in vars(args).items()}
            result['clingo']['cmd'] = cp.args
            json.dump(result, args.out)

        if result['clingo']['Models']['More'] != 'no':
            logging.info('Missing models')

    os.remove(asp_if)
    return cp.returncode if cp is not None else 1


def main(cargs) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter, prog=os.path.basename(__file__))
    parser.add_argument("-v", "--verbose", help="increase output verbosity", action='count', default=0)
    parser.add_argument('--version', action='version', version='%(prog)s {}'.format(__version__))
    subparsers = parser.add_subparsers()

    def add_command(name: str, action: Callable, help: str = None) -> argparse.ArgumentParser:
        sp = subparsers.add_parser(name, help=action.__doc__ if help is None else help)
        sp.set_defaults(func=action)
        return sp

    cmd_parser = add_command('version', print_version)

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

    cmd_parser = add_command('run', run_problem)
    cmd_parser.add_argument('--out', type=argparse.FileType('w'), default=sys.stdout, help='output file')
    cmd_parser.add_argument('--defmain', type=str, default=None, choices=sorted(tmpl.all_templates()), help='use default ASP main file with optimization options (one of [%(choices)s])')
    cmd_parser.add_argument('--json', action='store_true', default=False, help='JSON output')
    cmd_parser.add_argument('--raw', action='store_true', default=False, help='raw clingo output')
    cmd_parser.add_argument('--models', '-n', type=int, default=1, help='generates more optimal models (0 for all)')
    cmd_parser.add_argument('--clingo', type=str, default='clingo', help='clingo executable')
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


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
