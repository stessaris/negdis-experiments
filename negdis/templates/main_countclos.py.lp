% custom output, use the `--outf=3` option
#const cout = 0.

#script(python)

# clingo must be run with the `--quiet=1` option!

import json

MAX_MODELS = 100
CUSTOM_OUT = False

SELECTED_PRED = '${predicate_selected}'

def main(ctl: 'clingo.Control'):

    if ctl.get_const('cout') is not None:
        CUSTOM_OUT = True if ctl.get_const('cout').number != 0 else False

    conf: 'clingo.Configuration' = ctl.configuration
    # conf.solve.models = MAX_MODELS
    conf.solve.opt_mode = 'optN'

    prog = [('base', [])]

    ctl.ground(prog)
    if CUSTOM_OUT:
        with ctl.solve(yield_=True) as sh:
            for m in sh:
                if m.optimality_proven:
                    print(','.join(sorted(str(s.arguments[0]) for s in m.symbols(atoms=True) if s.name == SELECTED_PRED)))

        print(json.dumps(ctl.statistics['summary'], indent=2))
    else:
        # WARNING: unless the `--quiet=1` is given all the tentative models are produced (e.g. in JSON)
        ctl.solve()

#end.

% compute models with the minimal cardinality for selected constraints
%   to get more models use the `--opt-mode=optN` option with `-n`
%   and `--quiet=1` to avoid printing of tentative models, also in the JSON output!!
#minimize{1@2,C: ${predicate_holds}(C)}.
#minimize{1@1,C: ${predicate_selected}(C)}.
