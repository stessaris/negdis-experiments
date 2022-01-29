% custom output, use the `--outf=3` option
#const cout = 0.
#const maxiter = 100.

#script(python)

import json

# see API docs at <https://potassco.org/clingo/python-api/current>
import clingo


MAX_MODELS = 100
CUSTOM_OUT = False
MAX_ITER = 100

SELECTED_PRED = '${predicate_selected}'
HOLDS_PRED = '${predicate_holds}'


def step_atom(n: int) -> 'clingo.Symbol':
    return clingo.Function('step', [n])


def main(ctl: 'clingo.Control'):

    if ctl.get_const('cout') is not None:
        CUSTOM_OUT = True if ctl.get_const('cout').number != 0 else False
    if ctl.get_const('maxiter') is not None:
        MAX_ITER = ctl.get_const('maxiter').number

    conf: 'clingo.Configuration' = ctl.configuration
    # conf.solve.models = MAX_MODELS
    conf.solver.heuristic = 'Domain'
    conf.solve.enum_mode = 'domRec'

    MAX_MODELS = int(conf.solve.models) if int(conf.solve.models) > 0 else float('inf')

    prog = [('base', [])]

    ctl.ground(prog)

    mcount = 0
    no_goods = []
    for t in range(0, MAX_ITER):
        if mcount > MAX_MODELS:
            break

        if CUSTOM_OUT:
            print(('-' * 10) + ' Step {}'.format(t) + ('-' * 20))

        if t > 0:
            ctl.release_external(step_atom(t - 1))
        ctl.ground([('step_prog', [t])])
        ctl.assign_external(step_atom(t), True)

        # add constraints to prevent supersets of previous step models
        with ctl.backend() as backend:
            for model in no_goods:
                backend.add_rule([], [backend.add_atom(s) for s in model])

        with ctl.solve(yield_=True) as sh:
            no_goods = []
            for m in sh:
                if mcount > MAX_MODELS:
                    break
                mcount += 1

                if CUSTOM_OUT:
                    selected = []
                    holds = []
                    constraint = []
                    for s in m.symbols(atoms=True):
                        if s.name == SELECTED_PRED:
                            selected.append(s.arguments[0])
                        elif s.name == HOLDS_PRED:
                            holds.append(s.arguments[0])
                            constraint.append(s)
                    print('Answer({}) {}: {} {}'.format(t, mcount, sorted(selected), sorted(holds)))
                    no_goods.append(constraint)
                else:
                    no_goods.append([s for s in m.symbols(atoms=True) if s.name == HOLDS_PRED])

    if CUSTOM_OUT:
        print(json.dumps(ctl.statistics['summary'], indent=2))


#end.


% compute subset minimal answer sets with heuristics
%   requires the `--heuristic=Domain` command option
%   see the Clingo guide Section 10.3: Computing Subset Minimal Answer Sets with Heuristics
%   to get more models use the `--enum-mod=domRec` option with `-n`
%   and `--quiet=1` to avoid printing of tentative models
#heuristic ${predicate_selected}(C) : ${predicate_constraint}(C). [1@1,false]

#program step_prog(t).
#external step(t).
:- step(t), #count { C : ${predicate_holds}(C) } > t.
:- step(t), #count { C : ${predicate_holds}(C) } < t.
