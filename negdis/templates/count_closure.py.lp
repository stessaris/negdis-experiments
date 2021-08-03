% custom output, use the `--outf=3` option
#const cout = 1.

#script(python)

# see API docs at <https://potassco.org/clingo/python-api/current>
# import clingo

CUSTOM_OUT = True

HOLDS_PRED = 'holds'

def main(ctl: 'clingo.Control'):

    if ctl.get_const('cout') is not None:
        CUSTOM_OUT = True if ctl.get_const('cout').number != 0 else False

    ctl.configuration.solve.models = 1

    prog = [('base', [])]

    ctl.ground(prog)
    if CUSTOM_OUT:
        holds_size = 0
        with ctl.solve(yield_=True) as sh:
            for m in sh:
                holds_size = max(holds_size, len([s.arguments[0] for s in m.symbols(atoms=True) if s.name == HOLDS_PRED]))

        print(holds_size)
    else:
        ctl.solve()

#end.

holds(C) :- choice(_, C).

#show holds/1.