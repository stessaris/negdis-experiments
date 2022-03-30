#!/usr/bin/env python

"""Use clingo ASP solver to minimise the set of constraints that exclude a set of traces. See the negdis project for details.
"""

import argparse
from ast import arg
from io import StringIO, TextIOBase
import json
import logging
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import textwrap
from typing import Any, Callable, Dict, Iterable, Sequence, Set, Tuple, TextIO, Union

from . import templates as tmpl
from . import __version__
from .templates import SolverConf

NAME_MAP = dict()

# make sure that when running in a venv the PATH is correct
#  solves the problem that venv executables are not picked up when running as jupyter kernel
if os.path.dirname(sys.executable) not in os.pathsep.split(os.environ['PATH']):
    os.environ['PATH'] = os.path.dirname(sys.executable) + os.pathsep + os.environ['PATH']


class ASPenc():
    @classmethod
    def comment(cls, text: str) -> str:
        return '\n' + textwrap.indent(text, '% ', predicate=lambda line: True)

    @classmethod
    def const(cls, name: str) -> str:
        if name.isnumeric() or re.fullmatch(r'[a-z][a-zA-Z0-9]*', name):
            return name
        else:
            return '"' + name.replace('\\', r'\\').replace('"', r'\"') + '"'

    @classmethod
    def decode_const(cls, name: str) -> str:
        name = name.strip()
        if name[0] != '"':
            return name
        return name.strip('"').replace(r'\\', '\\').replace(r'\"', '"')

    @classmethod
    def constraint(cls, name: str, actions: Iterable[str], quote: bool = True) -> str:
        if quote:
            args = [cls.const(name.lower())] + [cls.const(a) for a in actions]
        else:
            args = [name, *actions]
        return r'${functor_declare}(' + ','.join(args) + ')'

    @classmethod
    def predicate(cls, name: str, *args: str) -> str:
        return name + '(' + ','.join(args) + ')'

    @classmethod
    def rule(cls, head: str, body: Iterable[str]) -> str:
        return head + ' :- ' + ', '.join(body) + '.'

    @classmethod
    def fact(cls, predicate: str, *args: str) -> str:
        return cls.predicate(predicate, *args) + '.'

    @classmethod
    def choicep(cls, trace: str, constraint: str) -> str:
        return cls.predicate(r'${predicate_choice}', trace, constraint)

    @classmethod
    def holdsp(cls, constraint: str) -> str:
        return cls.predicate(r'${predicate_holds}', constraint)

    @classmethod
    def all_actionsp(cls, name: str) -> str:
        return cls.predicate(r'${predicate_action}', name)

    @classmethod
    def all_constraintsp(cls, constr: str) -> str:
        return cls.predicate(r'${predicate_constraint}', constr)

    @classmethod
    def in_headp(cls, name: str, arity: Union[str, int]) -> str:
        return cls.predicate(r'${predicate_rule_head_pttrn}', name, str(arity))

    @classmethod
    def fixedp(cls, constr: str) -> str:
        return cls.predicate(r'${predicate_fixed}', constr)

    @classmethod
    def selectedp(cls, constr: str) -> str:
        return cls.predicate(r'${predicate_selected}', constr)

    @classmethod
    def constraint_namep(cls, constr: str, name: str, arity: Union[str, int]) -> str:
        return cls.predicate(r'${predicate_constraint_name}', constr, name, str(arity))

    @classmethod
    def constraint_actionp(cls, constr: str, action: str) -> str:
        return cls.predicate(r'${predicate_constraint_action}', constr, action)

    @classmethod
    def decode_constraint(cls, funct: str) -> Tuple[str, Iterable[str]]:
        m = re.fullmatch(tmpl.Defaults['functor_declare'] + r'\((?P<args>(.+))\)', funct.strip())
        if m:
            args = m.group('args').split(',')
            return cls.decode_const(args[0]), (cls.decode_const(a) for a in args[1:])

    @classmethod
    def constraints_from_model(cls, atoms: Iterable[str]) -> Sequence[str]:
        selectedp = tmpl.Defaults['predicate_selected']
        selected = []
        for a in atoms:
            m = re.fullmatch(r'\s*' + selectedp + r'\((?P<constr>(.+))\)\s*', a)
            if m:
                name, args = cls.decode_constraint(m.group('constr'))
                selected.append('{}({})'.format(name, ','.join(args)))
        return selected


def parse_constraint(constraint: str, namemap: Dict[str, str] = NAME_MAP) -> Tuple[str, Sequence[str]]:
    m = re.fullmatch(r'\s*(?P<name>[\w]+)\((?P<args>[\w, -_]+)\)\s*', constraint)
    if m:
        cname = m.group('name').strip()
        args = [a.strip() for a in m.group('args').split(',')]
        return cname, args
    else:
        logging.fatal('cannot parse <{}> constraint'.format(constraint))
        return None, None


def choices2asp(fp: TextIO, actions: Set[str], out: TextIO = None, tid: int = 0) -> int:
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
 
    traces = set()
    choices = json.load(fp)
    tc = tid
    for choice in choices:
        trace = tuple(choice.get('trace', []))
        if trace in traces:
            # do not include repeated traces
            continue
        traces.add(trace)
        tc += 1
        actions.update(trace)
        for c_str in choice.get('choices', []):
            cname, args = parse_constraint(c_str)
            if cname is not None:
                actions.update(args)
                print(ASPenc.choicep(str(choice.get('id', tc)), ASPenc.constraint(cname, args, quote=True)) + '.', file=out)
    return tid


def constraints2asp(inf: TextIO, actions: Set[str], outf: TextIO = None):

    if outf is None:
        outf = sys.stdout

    for line in inf:
        cname, args = parse_constraint(line)
        if cname is not None:
            actions.update(args)
            print(ASPenc.fixedp(ASPenc.constraint(cname, args, quote=True)), file=outf)
 

def read_declare_patterns(infile) -> Set[str]:
    decl_templates = set()
    for line in infile:
        m = re.match(r'\A\s*(?P<name>(\w|_|\s)+)\s*\([^)]*\)\s*:', line)
        if m:
            decl_templates.add(m.group('name').lower())
    logging.info('Known templates: {}'.format(decl_templates))
    return decl_templates


def rules2asp(inf: TextIO, outf: TextIO = None):
    """Convert a set of rules of the form:

    head <- body_term_1 & ... & body_term_n

    to a set of ASP rules

    Args:
        inf ([type]): [description]
        outf ([type], optional): [description]. Defaults to sys.stdout.
    """
    if outf is None:
        outf = sys.stdout

    def parse_rule(expr):
        atom_exp = r'([-¬!]?)\s*(\b[\w_]+\b)\(([\w\s,]*)\)'
        imp_exp = r'(⊑|<-)'
        and_exp = r'(&)'

        var_exp = r'\b[A-Z_](\w|_)*\b'

        rule_exp = f'^\\s*(?P<head>{atom_exp})\\s*{imp_exp}\s*(?P<body>{atom_exp}(\\s*{and_exp}\\s*{atom_exp})*)\\s*$'

        def atoms(expr):
            return [(m.group(1), m.group(2), tuple(a.strip() for a in m.group(3).split(','))) for m in re.finditer(atom_exp, expr)]

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
            return ('-' if atom[0] else '') + ASPenc.holdsp(ASPenc.constraint(atom[1], atom[2], quote=False))

        def bound(v):
            return ASPenc.all_actionsp(v)

        return ASPenc.rule(holds(head), [holds(a) for a in body] + [bound(v) for v in unbound])

    max_arity = 1
    decl_pttrn_in_head = set()
    for line in inf:
        head, body, variables, unbound = parse_rule(line)
        if head:
            if not head[0]:
                # the pattern appear positive in head
                decl_pttrn_in_head.add((head[1], str(len(head[2]))))
                max_arity = max(max_arity, len(head[2]))
            print(rule2asp(head, body, unbound), file=outf)

    print(ASPenc.comment('patterns appearing in the head of a rule'), file=outf)
    for name, arity in decl_pttrn_in_head:
        print(ASPenc.in_headp(ASPenc.const(name), arity) + '.', file=outf)

    print(ASPenc.comment('consider all constraints potentially generated by rules'), file=outf)
    for i in range(1, max_arity + 1):
        avars = [f'A{j}' for j in range(1, i+1)]
        rhead = ASPenc.all_constraintsp('C')
        rbody = [
            'C = ' + ASPenc.constraint('P', avars, quote=False),
            ASPenc.in_headp('P', i)
        ] + [ASPenc.all_actionsp(v) for v in avars]
        print(ASPenc.rule(rhead, rbody), file=outf)



def asp_problem(choices: TextIO, rules: TextIO = None, positives: TextIO = None, main: Union[str, TextIO] = '', outf: TextIO = None):
    """Generate the minimisation ASP problem to be fed into the solver

    Args:
        choices ([type]): [description]
        rules ([type], optional): [description]
        positives ([type], optional): [description]
        main ([type], optional): [description]
        outf (io.TextIOBase, optional): [description]. Defaults to sys.stdout.

    Returns:
        [type]: [description]
    """
    if outf is None:
        outf = sys.stdout

    def asp_section(name):
        print('\n' + ('%' * 30) + '\n%%%% ' + name + '\n', file=outf)

    def asp_comment(txt: str):
        print(ASPenc.comment(txt), file=outf)

    actions = set()
    asp_section('Choices')
    asp_comment('constraints in choices are in all possible constraints')
    print(ASPenc.rule(ASPenc.all_constraintsp('C'), [ASPenc.choicep('_', 'C')]), file=outf)
    outf.write('\n')
    choices2asp(choices, actions, out=outf)

    if positives is not None:
        asp_section('Positive')
        asp_comment('positive constraints holds by assumption')
        print(ASPenc.rule(ASPenc.holdsp('C'), [ASPenc.fixedp('C')]), file=outf)
        outf.write('\n')
        asp_comment('positive constraints constraints in choices are in all possible constraints')
        print(ASPenc.rule(ASPenc.all_constraintsp('C'), [ASPenc.fixedp('C')]), file=outf)
        constraints2asp(positives, actions, outf=outf)
        outf.write('\n')

    asp_section('Actions')
    for a in actions:
        print(ASPenc.all_actionsp(ASPenc.const(a)) + '.', file=outf)

    asp_section('Declare rules')
    asp_comment(f'selected constraints holds')
    print(ASPenc.rule(ASPenc.holdsp('C'), [ASPenc.selectedp('C')]), file=outf)
    outf.write('\n')
    if rules is not None:
        rules2asp(rules, outf=outf)

    asp_section('Constraints structure')
    max_arity = 3
    for i in range(1, max_arity+1):
        asp_comment(f'Constraints of arity {i}')
        avars = [f'A{j}' for j in range(1, i+1)]
        rhead = ASPenc.constraint_namep('C', 'P', i)
        rbody = [
            ASPenc.all_constraintsp('C'),
            'C = ' + ASPenc.constraint('P', avars, quote=False),
        ]
        print(ASPenc.rule(rhead, rbody), file=outf)
        for j in range(i):
            rhead = ASPenc.constraint_actionp('C', avars[j])
            print(ASPenc.rule(rhead, rbody), file=outf)

    asp_section('Main')
    if isinstance(main, str):
        outf.write(main)
    else:
        outf.write(main.read())

    asp_comment('print selected constraints')
    print(r'#show ${predicate_selected}/1.', file=outf)


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

def parse_clingo_json(clingo_out: Dict) -> Sequence[Sequence[str]]:
    return [ASPenc.constraints_from_model(witness.get('Value', [])) for call in clingo_out.get('Call', []) for witness in call.get('Witnesses', {})]


def solve_optimisation_problem(data_id: str, choices: TextIO, rules: TextIO, positives: TextIO, main: Union[str, TextIO], models: int, solver: str, extra_args: Sequence[str], timeout: float, raw: bool = False, mapping: Dict[str, Any] = None) -> Dict:
    if data_id is None:
        try:
            data_id = Path(choices.name).stem
        except Exception:
            data_id = ''

    if not raw and not any(a.startswith('--outf=') for a in extra_args):
        extra_args = ['--outf=2'] + extra_args
    with StringIO() as asp_if:
        asp_problem(choices, rules=rules, positives=positives, main=main, outf=asp_if)

        clingo_out = run_clingo(
            evaluate_template(asp_if.getvalue(), mapping=mapping),
            clingo=solver, models=models, timeout=timeout, args=extra_args)

    results = {'id': data_id} if data_id else dict()
    if 'Call' in clingo_out:
        # it's the clingo JSON output
        results['selected'] = parse_clingo_json(clingo_out)
    results['clingo'] = clingo_out

    return results


def optimise(mode: Union[str, SolverConf], choices: TextIO, rules: TextIO, positives: TextIO = None, data_id: str = None, models: int = 1, outf: TextIO = None, raw: bool = False, timeout: float = None, mapping: Dict[str, str] = dict()) -> Dict:
    solver_conf = solver_configuration(mode)
    return solve_optimisation_problem(
        data_id=data_id,
        choices=choices, rules=rules, positives=positives,
        main=solver_conf.program(eval=False),
        models=models,
        solver=solver_conf.solver,
        extra_args=list(solver_conf.args),
        timeout=timeout,
        raw=raw,
        mapping={**dict(solver_conf.mapping), **mapping}
    )


def update_templates(src: Union[os.PathLike, TextIOBase]) -> Dict[str, SolverConf]:
    if isinstance(src, TextIOBase):
        return tmpl.read_templates_conf(src)
    else:
        with open(src) as fd:
            return tmpl.read_templates_conf(fd)


def configurations() -> Dict[str, SolverConf]:
    return tmpl.templates_conf()

def evaluate_template(asp: str, mapping: Dict[str, Any]=None) -> str:
    return tmpl.evaluate_template(asp, mapping=mapping)

def solver_configuration(opt_mode: Union[str, SolverConf, TextIOBase]) -> SolverConf:
    if isinstance(opt_mode, SolverConf):
        return opt_mode
    if isinstance(opt_mode, TextIOBase):
        return SolverConf.from_file(opt_mode)
    if isinstance(opt_mode, Dict):
        return SolverConf.from_dict(opt_mode)
    if isinstance(opt_mode, str) and opt_mode in configurations():
        return configurations()[opt_mode]
    raise RuntimeError(f'Cannot build solver configuration from {opt_mode}')


def compose_asp_main(*src: Union[str, TextIOBase, SolverConf, Dict]) -> str:
    asp_prog = ''
    for s in src:
        if isinstance(s, str):
            asp_prog += solver_configuration(s).program(eval=False) if s in configurations() else s
        elif isinstance(s, (SolverConf, Dict)):
            asp_prog += solver_configuration(s).program(eval=False)
        elif isinstance(s, TextIOBase):
            asp_prog += s.read()
    return asp_prog


####################################################
#
# CLI interface


def print_version(args: argparse.Namespace) -> int:
    print('{} {}'.format(os.path.basename(__file__), __version__))
    return 0


def convert_rules(args: argparse.Namespace) -> int:
    """Convert a set of rules of the form head <- body to a set of ASP rules"""
    
    with StringIO() as asp_if:
        rules2asp(args.rules, outf=asp_if)
        args.out.write(evaluate_template(asp_if.getvalue()))
    return 0


def convert_choices(args: argparse.Namespace) -> int:
    """Convert a negdis choice file to a set of ASP facts"""
    with StringIO() as asp_if:
        choices2asp(args.choices, set(), out=asp_if)
        args.out.write(evaluate_template(asp_if.getvalue()))
    return 0


def cli_solver_conf(args: argparse.Namespace) -> SolverConf:
    conf_id = 'unknown'
    input_files = []
    solver_args = []
    docstring = ''
    solver = 'clingo'
    template = ''
    mapping = dict()
    if args.conf:
        solver_conf = solver_configuration(args.conf)
        conf_id = solver_conf.id
        input_files.extend(solver_conf.inputs)
        solver_args.extend(solver_conf.args)
        docstring = solver_conf.docstring
        solver = solver_conf.solver
        template += solver_conf.template
        mapping = dict(solver_conf.mapping)
    elif args.defmain:
        for solver_conf in (configurations()[sc] for sc in args.defmain if sc in configurations()):
            conf_id = solver_conf.id
            input_files.extend(solver_conf.inputs)
            solver_args.extend(solver_conf.args)
            docstring += ('\n' if len(docstring) > 0 else '') + solver_conf.docstring
            solver = solver_conf.solver
            template += solver_conf.template
            mapping = {**mapping, **dict(solver_conf.mapping)}

    if args.main:
        template += compose_asp_main(*args.main)

    if hasattr(args, 'clingo') and args.clingo:
        solver = args.clingo

    if hasattr(args, 'extra') and args.extra:
        solver_args.extend(shlex.split(args.extra))

    return SolverConf(
        id=conf_id,
        inputs=tuple(input_files),
        args=tuple(solver_args),
        docstring=docstring,
        solver=solver,
        template=template,
        mapping=tuple(mapping.items())
    )

def generate_problem(args: argparse.Namespace) -> int:
    """Generate the ASP file for the input"""

    solver_conf = cli_solver_conf(args)

    logging.info(solver_conf)

    with StringIO() as asp_if:
        asp_problem(args.choices, rules=args.rules, positives=args.pos,
            main=solver_conf.program(eval=False),
            outf=asp_if)
        args.out.write(asp_if.getvalue() if args.noeval else evaluate_template(asp_if.getvalue(), mapping=dict(solver_conf.mapping)))
    return 0


def run_cmd(args: argparse.Namespace) -> int:

    try:
        data_id = Path(args.choices).stem
    except Exception:
        data_id = ''

    solver_conf = cli_solver_conf(args)
    logging.info(solver_conf)

    results = solve_optimisation_problem(
        data_id=data_id,
        choices=args.choices, rules=args.rules, positives=args.pos,
        main=solver_conf.program(eval=False),
        models=args.models,
        solver=solver_conf.solver,
        extra_args=solver_conf.args,
        timeout=args.timeout,
        raw=args.raw,
        mapping=dict(solver_conf.mapping)
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
    cmd_parser.add_argument('--defmain', action='append', type=str, default=None, choices=sorted(configurations().keys()), help='use default ASP main file with optimization options (one of [%(choices)s])')
    cmd_parser.add_argument('--main', action='append', type=argparse.FileType(), help='main ASP file to be prepended')
    cmd_parser.add_argument('--pos', type=argparse.FileType(), help='positive Declare constraints')
    cmd_parser.add_argument('--rules', type=argparse.FileType(), help='Declare rules file')
    cmd_parser.add_argument('--templ', type=argparse.FileType(), help='Declare templates file')
    cmd_parser.add_argument('--conf', type=argparse.FileType(), help='Solver configuration file (JSON)')
    cmd_parser.add_argument('--noeval', action='store_true', default=False, help='Do not expand the ASP templating')
    cmd_parser.add_argument('choices', type=argparse.FileType(), help='negdis choice file')

    cmd_parser = add_command('run', run_cmd)
    cmd_parser.add_argument('--out', type=argparse.FileType('w'), default=sys.stdout, help='output file')
    cmd_parser.add_argument('--defmain', action='append', type=str, default=None, choices=sorted(configurations().keys()), help='use default ASP main file with optimization options (one of [%(choices)s])')
    cmd_parser.add_argument('--json', action='store_true', default=False, help='JSON output')
    cmd_parser.add_argument('--raw', action='store_true', default=False, help='raw clingo output')
    cmd_parser.add_argument('--models', '-n', type=int, default=1, help='generates more optimal models (0 for all)')
    cmd_parser.add_argument('--clingo', type=str, help='clingo executable')
    cmd_parser.add_argument('--extra', type=str, default='', help='clingo extra arguments')
    cmd_parser.add_argument('--timeout', type=float, default=None, help='timeout for clingo executable')
    cmd_parser.add_argument('--main', action='append', type=argparse.FileType(), help='main ASP file to be prepended')
    cmd_parser.add_argument('--pos', type=argparse.FileType(), help='positive Declare constraints')
    cmd_parser.add_argument('--rules', type=argparse.FileType(), help='Declare rules file')
    cmd_parser.add_argument('--templ', type=argparse.FileType(), help='Declare templates file')
    cmd_parser.add_argument('--conf', type=argparse.FileType(), help='Solver configuration file (JSON)')
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
