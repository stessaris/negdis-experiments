"""Helper functions for negdis file manipulation and reporting using Jupyter
"""

__version__ = '1.1'

import io
import itertools
import json
import logging
from operator import itemgetter
import os
from pathlib import Path
import shutil
import statistics as stats
from subprocess import CalledProcessError, check_output, run
import sys
import tempfile
from typing import Dict, Iterable, Tuple
import xml.etree.ElementTree as ET

from . import aspdeclare

NEGDIS_DIST = Path(__file__).parent.parent.joinpath('dist').resolve()

def version() -> str:
    return '{} {}'.format(os.path.basename(__file__), __version__)


def cat(*pathsegments) -> str:
    """Read the content of a text file and returns a string with its content.

    Takes the same arguments as the pathlib.Path function. The function forces UTF-8 encoding.

    Returns:
        str: the content of the file
    """
    return Path(*pathsegments).read_text(encoding='utf-8')


def tmpfname(suffix: str = None) -> str:
    """Returns the name of a temporary file. The file is created and closed but not deleted.

    Args:
        suffix (str, optional): optional suffix for the file name. Defaults to None.

    Returns:
        str: the name of the file (path)
    """
    with tempfile.NamedTemporaryFile(suffix=suffix, delete=False, mode='w+', encoding='utf-8') as fp:
        fname = fp.name
    return fname


def xes_size(pathname: str) -> int:
    if sys.platform != 'win32' and shutil.which('xmllint'):
        # use xmllint tool
        return int(check_output('sed \'s/xmlns="[^"]*"//g\' "{}" | xmllint --xpath \'count(//trace)\' -'.format(pathname), shell=True))
    else:
        # no xmllint, slow way
        return sum(1 for ev, el in ET.iterparse(pathname) if el.tag == '{http://www.xes-standard.org/}trace')


def merge_xes(files, out=sys.stdout):
    def append_traces(xes_doc: ET, *more_docs: ET):
        log_node = xes_doc.getroot()
        for xe in more_docs:
            for t in xe.iterfind('{http://www.xes-standard.org/}trace'):
                log_node.append(t)

    # get original namespaces
    namespaces = dict([node for _, node in ET.iterparse(files[0], events=['start-ns'])])
    for ns, uri in namespaces.items():
        ET.register_namespace(ns, uri)

    first_et = ET.parse(files[0])
    append_traces(first_et, *[ET.parse(fn) for fn in files[1:]])

    first_et.write(out, encoding='UTF-8', xml_declaration=True)


def count_choices(fn, top=10):
    c_count = {}
    with open(fn) as fp:
        c_data = json.load(fp)
        for choices in [t.get('choices', []) for t in c_data]:
            for c in choices:
                c_count[c] = c_count.get(c, 0) + 1

    for k, v in itertools.islice(sorted(c_count.items(), key=itemgetter(1), reverse=True), top):
        print('{}: {} ({}%)'.format(k, v, int(100 * v / len(c_data))))


def run_negdis(*args: str, negdis='negdis', dist=NEGDIS_DIST, timeit=True, outf=sys.stdout, **kwargs):
    negdiscmd = shutil.which(negdis)
    if negdiscmd is None and dist is not None:
        if sys.platform.startswith('linux'):
            negdiscmd = Path(dist).joinpath('linux', 'negdis')
        elif sys.platform.startswith('darwin'):
            negdiscmd = Path(dist).joinpath('darwin', 'negdis')
        elif sys.platform.startswith('win32'):
            negdiscmd = Path(dist).joinpath('win32', 'negdis.exe')
    if negdiscmd is None:
        return 'Negdis command {} not found'.format(negdis)
    timecmd = [shutil.which('time'), '-p'] if timeit and sys.platform != 'win32' and shutil.which('time') else []
    cmd = [str(negdiscmd)] + [str(a) for a in args]
    cp = run(timecmd + cmd, capture_output=True, text=True, **kwargs)
    if outf is not None:
        print(cp.stdout, file=outf)
        return 'Running: ' + ' '.join(cmd) + '\n' + cp.stderr
    else:
        return cp


def count_sat(constraints: Iterable[str], logfile: os.PathLike, templates: os.PathLike, nosize: bool = False, dist=NEGDIS_DIST) -> Tuple[int, int]:
    """
    Return the number of traces in the logfile satisfying all the constraints, and the size of the log.
    """
    logsize = None if nosize else xes_size(logfile)

    cp = run_negdis('check', 'constraints', '-t', templates, logfile, dist=dist, timeit=False, outf=None, input='\n'.join(constraints))

    logging.debug(cp.stdout)

    negdis_out = json.loads(cp.stdout)

    sat_traces = [all([b for b in trace.get('sat').values()]) for trace in negdis_out]

    return (sum(sat_traces), logsize)


def fitness(constraints: Iterable[str], positive_log: os.PathLike, negative_log: os.PathLike, templates: os.PathLike, dist=NEGDIS_DIST) -> Tuple[float, int, int, int]:
    """
    Calculate the fitness of the constraints wrt the validation logs. Returns None if the value cannot be calculated.
    """
    pcorrect = 0
    ncorrect = 0
    ptotal = 0
    ntotal = 0

    if positive_log is not None and templates is not None:
        sat, count = count_sat(constraints, positive_log, templates, nosize=False, dist=dist)
        pcorrect = sat
        ptotal = count
    if negative_log is not None and templates is not None:
        sat, count = count_sat(constraints, negative_log, templates, nosize=False, dist=dist)
        ncorrect = count - sat
        ntotal = count

    total = ptotal + ntotal
    f_value = (pcorrect + ncorrect) / total if total > 0 else None

    return (f_value, pcorrect, ncorrect, ptotal, ntotal)


def optimise_choices(choices: os.PathLike, opt_mode: str, rules: os.PathLike, timeout: int = None, models: int = 20, val_pos: os.PathLike = None, val_neg: os.PathLike = None, templates: os.PathLike = None, dist: os.PathLike = NEGDIS_DIST, outdir: os.PathLike = None, report_fp: io.TextIOBase = sys.stdout):
    """Optimise the choices files.

    Args:
        choices (os.PathLike): [description]
        opt_mode (str): [description]
        rules (os.PathLike): [description]
        timeout (int, optional): [description]. Defaults to None.
        models (int, optional): [description]. Defaults to 20.
        val_pos (os.PathLike, optional): [description]. Defaults to None.
        val_neg (os.PathLike, optional): [description]. Defaults to None.
        templates (os.PathLike, optional): [description]. Defaults to None.
        dist (os.PathLike, optional): [description]. Defaults to NEGDIS_DIST.
        outdir (os.PathLike, optional): [description]. Defaults to None.
        report_fp (io.TextIOBase, optional): [description]. Defaults to sys.stdout.
    """

    def _say(txt):
        if report_fp is not None:
            print(txt, file=report_fp)

    cf = Path(choices)
    od_path = cf.parent if outdir is None else Path(outdir)
    of = od_path.joinpath(cf.stem + f'_opt_{opt_mode}.json')

    cmd = ['run', '--out', str(of), '--defmain', opt_mode, '--models', str(models), '--json']
    if rules is not None:
        cmd += ['--rules', str(Path(rules).resolve())]
    if timeout is not None:
        cmd += ['--timeout', str(timeout)]
    cmd.append(str(cf))

    _say('-' * 60)
    _say('Optimising {} using {} -> {}'.format(cf, opt_mode, of))
    _say('-' * 20)
    _say('aspdeclare command: {}'.format(' '.join(cmd)))
    aspdeclare.main(cmd)

    if report_fp is not None:
        optimisation_stats(of, val_pos, val_neg, templates, dist=dist, outf=report_fp, print_models=10)


def optimisation_stats(report: os.PathLike, plog: os.PathLike, nlog: os.PathLike, templates: os.PathLike, dist: os.PathLike = NEGDIS_DIST, outf: io.TextIOBase = sys.stdout, print_models: int = 10) -> Dict:
    """
    docstring
    """
    def _say(txt):
        if outf is not None:
            print(txt, file=outf)

    with open(report) as fp:
        result = json.load(fp)
        models = result.get('selected', [])
        clingo_out = result.get('clingo', {})

        calls = len(clingo_out.get('Call', []))
        last_cpu = clingo_out.get('Time', {}).get('CPU', 0.0)
        more_models = clingo_out.get('Models', {}).get('More', 'no') == 'yes'

        if print_models > 0:
            _say('-' * 20)
            _say('Models (only first {}/{}):'.format(print_models, len(models)))


        f_values = []
        msizes = []
        for constraints in sorted(models, key=len):
            f_value, pcorrect, ncorrect, psize, nsize = fitness(constraints, plog, nlog, templates, dist=dist)
            if isinstance(f_value, float):
                f_values.append(f_value)
            msizes.append(len(constraints))

            if print_models > 0:
                _say(', '.join(sorted(constraints)))
                if psize > 0:
                    _say('Positive satisfying: {}/{}'.format(pcorrect, psize))
                if nsize > 0:
                    _say('Negative unsatisfied: {}/{}'.format(ncorrect, nsize))
                if f_value is not None:
                    _say('Fitness: {}'.format(f_value))
                print_models += -1

    report_id = os.path.splitext(os.path.basename(report))[0]
    rep_stats = {
        'id': report_id,
        'fname': os.path.realpath(report),
        'models': len(msizes),
        'min': min(msizes) if len(msizes) > 0 else None,
        'max': max(msizes) if len(msizes) > 0 else None,
        'size_mean': stats.mean(msizes) if len(msizes) > 0 else None, 
        'fitness_mean': stats.mean(f_values) if len(f_values) > 0 else None,
        'cpu': last_cpu,
        'calls': calls,
        'more': more_models
    }

    _say(rep_stats)

    return rep_stats


def show_hwinfo(outf=sys.stdout):
    try:
        if sys.platform.startswith('linux'):
            out = check_output('lscpu; lsmem', shell=True, text=True)
        elif sys.platform.startswith('darwin'):
            out = check_output('sw_vers;system_profiler SPHardwareDataType|grep -v "\(UUID\)\|\(Serial\)"', shell=True, text=True)
        elif sys.platform.startswith('win32'):
            out = check_output(['systeminfo'], text=True)
        else:
            out = ''
        print(out, file=outf)
    except CalledProcessError as e:
        print("Can't get HW info: {}".format(e))
