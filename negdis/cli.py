#!/usr/bin/env python

import sys

from . import tools, aspdeclare, __version__

def negdis_cli():
    sys.exit(tools.Negdis().exec(*sys.argv[1:]).returncode)

def aspdeclare_cli():
    sys.exit(aspdeclare.main(sys.argv[1:]))

def main():
    cmds = ('negdis', 'aspdeclare', 'version')
    if len(sys.argv) < 2 or sys.argv[1] not in cmds:
        print(f'Usage: {sys.argv[0]} {"|".join(cmds)} [arguments]', file=sys.stderr)
        sys.exit(1)
    cmd = sys.argv[1]
    sys.argv = [sys.argv[0]] + sys.argv[2:]
    if cmd == 'negdis':
        negdis_cli()
    elif cmd == 'aspdeclare':
        aspdeclare_cli()
    else:
        print(__version__)


if __name__ == "__main__":
    main()
