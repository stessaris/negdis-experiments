% custom output, use the `--outf=3` option
#const cout = 0.

#script(python)

import json

MAX_MODELS = 100
CUSTOM_OUT = False

SELECTED_PRED = 'selected'

def main(ctl: 'clingo.Control'):

    if ctl.get_const('cout') is not None:
        CUSTOM_OUT = True if ctl.get_const('cout').number != 0 else False

    conf: 'clingo.Configuration' = ctl.configuration
    # conf.solve.models = MAX_MODELS

    prog = [('base', [])]

    ctl.ground(prog)
    if CUSTOM_OUT:
        with ctl.solve(yield_=True) as sh:
            for m in sh:
                print(','.join(sorted(str(s.arguments[0]) for s in m.symbols(atoms=True) if s.name == SELECTED_PRED)))

        print(json.dumps(ctl.statistics['summary'], indent=2))
    else:
        ctl.solve()

#end.
