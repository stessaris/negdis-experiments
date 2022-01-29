"""Helper functions for negdis file manipulation and reporting using Jupyter
"""

__version__ = '2.0'

from contextlib import contextmanager
from io import StringIO, TextIOBase
import itertools
import json
import logging
from operator import itemgetter
import os
from pathlib import Path
import shlex
import shutil
import stat
import statistics as stats
from subprocess import CalledProcessError, CompletedProcess, check_output, run
import sys
import tempfile
from typing import Dict, Generator, Iterable, Sequence, TextIO, Tuple, Union
import xml.etree.ElementTree as ET

from negdis.templates import SolverConf

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


@contextmanager
def ensure_file(in_f: Union[os.PathLike, TextIOBase], suffix: str = None) -> Generator[Path, None, None]:
    fpath = None
    if isinstance(in_f, TextIOBase):
        fpath = Path(tmpfname(suffix=suffix))
        with fpath.open('w') as fd:
            shutil.copyfileobj(in_f, fd)
    try:
        yield fpath if fpath is not None else Path(in_f)
    finally:
        if fpath is not None:
            fpath.unlink()


@contextmanager
def ensure_fd(in_f: Union[os.PathLike, TextIOBase], mode: str = 'r') -> Generator[TextIOBase, None, None]:
    fd = None if isinstance(in_f, TextIOBase) else open(in_f, mode=mode)
    try:
        yield in_f if fd is None else fd
    finally:
        if fd is not None:
            fd.close()


@contextmanager
def as_file(content: Union[str, TextIOBase], suffix: str = None) -> Generator[Path, None, None]:
    """Context that makes sure that the content is available as a temporary named file, which is deleted upon exiting.

    Args:
        content (Union[str, TextIOBase]): content or readable file
        suffix (str, optional): suffix to be appended to the temporary file name. Defaults to None.

    Yields:
        Generator[Path, None, None]: [description]
    """
    fpath = Path(tmpfname(suffix=suffix))
    with fpath.open('w') as fd:
        if isinstance(content, TextIOBase):
            shutil.copyfileobj(content, fd)
        else:
            fd.write(content)
    try:
        yield fpath
    finally:
        fpath.unlink(missing_ok=True)


def xes_size(pathname: str) -> int:
    if sys.platform != 'win32' and shutil.which('xmllint'):
        # use xmllint tool
        return int(check_output('sed \'s/xmlns="[^"]*"//g\' "{}" | xmllint --xpath \'count(//trace)\' -'.format(pathname), shell=True))
    else:
        # no xmllint, slow way
        return sum(1 for ev, el in ET.iterparse(pathname) if el.tag == '{http://www.xes-standard.org/}trace')


def merge_xes(files, out: TextIO = None):
    if out is None:
        out = sys.stdout

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


def count_choices(fn: Union[os.PathLike, TextIOBase], top=10):
    c_count = {}
    c_count_unique = {}
    unique_traces = set()
    no_choice = 0
    no_choice_unique = 0
    with ensure_fd(fn) as fp:
        c_data = json.load(fp)
        for t_info in c_data:
            trace_str = ''.join(t_info.get('trace', []))
            choices = t_info.get('choices', [])
            if len(choices) < 1:
                no_choice += 1
                if trace_str not in unique_traces:
                    no_choice_unique += 1
            for c in choices:
                c_count[c] = c_count.get(c, 0) + 1
                if trace_str not in unique_traces:
                    c_count_unique[c] = c_count_unique.get(c, 0) + 1
            unique_traces.add(trace_str)

    print(f'Traces without choices: {no_choice}/{len(c_data)} ({int(100 * no_choice / len(c_data))}%), w/o duplicates: {no_choice_unique}/{len(unique_traces)} ({int(100 * no_choice / len(unique_traces))}%)')
    print('With duplicates:')
    total = len(c_data)
    for k, v in itertools.islice(sorted(c_count.items(), key=itemgetter(1), reverse=True), top):
        print(f' {k}: {v}/{total} ({int(100 * v / total)}%)')
    print('Without duplicates:')
    total = len(unique_traces)
    for k, v in itertools.islice(sorted(c_count_unique.items(), key=itemgetter(1), reverse=True), top):
        print(f' {k}: {v}/{total} ({int(100 * v / total)}%)')


def count_sat(constraints: Iterable[str], logfile: Union[os.PathLike, TextIOBase], templates: Union[os.PathLike, TextIOBase], nosize: bool = False, negdis: 'Negdis' = None) -> Tuple[int, int]:
    """
    Return the number of traces in the logfile satisfying all the constraints, and the size of the log.
    """
    if negdis is None:
        negdis = Negdis.default()
    logsize = None if nosize else xes_size(logfile)

    cp = negdis.check(logfile, StringIO(initial_value='\n'.join(constraints)), templates, timeit=False)

    logging.debug(cp.stdout)

    negdis_out = json.loads(cp.stdout)

    sat_traces = [all([b for b in trace.get('sat').values()]) for trace in negdis_out]

    return (sum(sat_traces), logsize)


def fitness(constraints: Iterable[str], positive_log: os.PathLike, negative_log: os.PathLike, templates: os.PathLike, negdis: 'Negdis' = None) -> Tuple[float, int, int, int]:
    """
    Calculate the fitness of the constraints wrt the validation logs. Returns None if the value cannot be calculated.
    """
    pcorrect = 0
    ncorrect = 0
    ptotal = 0
    ntotal = 0

    if positive_log is not None and templates is not None:
        sat, count = count_sat(constraints, positive_log, templates, nosize=False, negdis=negdis)
        pcorrect = sat
        ptotal = count
    if negative_log is not None and templates is not None:
        sat, count = count_sat(constraints, negative_log, templates, nosize=False, negdis=negdis)
        ncorrect = count - sat
        ntotal = count

    total = ptotal + ntotal
    f_value = (pcorrect + ncorrect) / total if total > 0 else None

    return (f_value, pcorrect, ncorrect, ptotal, ntotal)


def asp_program(choices: Union[os.PathLike, TextIOBase], opt_mode: Union[str, aspdeclare.SolverConf], rules: Union[os.PathLike, TextIOBase], mapping: Dict[str, str] = None) -> str:
    sol_conf = aspdeclare.solver_configuration(opt_mode)
    with ensure_fd(choices) as choices_fd, ensure_fd(rules) as rules_fd:
        with StringIO() as asp_if:
            aspdeclare.asp_problem(choices_fd, rules=rules_fd, positives=None, main=sol_conf.program(mapping), outf=asp_if)

            return asp_if.getvalue()


def optimise_choices(choices: Union[os.PathLike, TextIOBase], opt_mode: Union[str, aspdeclare.SolverConf], rules: Union[os.PathLike, TextIOBase], data_id: str = None, timeout: int = None, models: int = 20, val_pos: os.PathLike = None, val_neg: os.PathLike = None, templates: os.PathLike = None, dist: os.PathLike = None, outdir: os.PathLike = None, results_path: os.PathLike = None, report_fp: TextIO = None, negdis: 'Negdis' = None, mapping: Dict[str, str] = None):
    """Optimise the choices files.
    """
    if report_fp is None:
        report_fp = sys.stdout
    if negdis is None:
        negdis = Negdis(dist=dist) if dist else Negdis.default()


    def _say(txt):
        print(txt, file=report_fp)

    if data_id is None:
        if isinstance(choices, TextIOBase):
            try:
                data_id = Path(choices.name).stem
            except Exception:
                data_id = ''
        else:
            data_id = Path(choices).stem

    try:
        opt_id = opt_mode.id
    except AttributeError:
        opt_id = str(opt_mode)
    _say('-' * 60)
    _say('Optimising {} using {}'.format(choices, opt_id))
    _say('-' * 20)
    with ensure_fd(choices) as choices_fd, ensure_fd(rules) as rules_fd:
        positives_fd = None
        results = aspdeclare.optimise(opt_mode, choices_fd, rules_fd, positives=positives_fd, data_id=data_id, models=models, timeout=timeout, mapping=mapping)

    if outdir or results_path:
        if results_path is None:
            results_path = Path(outdir, f'{data_id}_opt_{opt_id}.json')
        logging.info(f'writing optimisation results to {results_path}')
        with open(results_path, 'w') as out_fd:
            json.dump(results, out_fd, ensure_ascii=False)

    if 'selected' in results:
        optimisation_stats(results, val_pos, val_neg, templates, outf=report_fp, print_models=10, negdis=negdis)
    else:
        clingo_results = results['clingo']
        if clingo_results.get('timeout', False):
            print('solver command {} timed out after {} seconds'.format(clingo_results['cmd'], clingo_results['timeout']))
        report_fp.write(clingo_results['stdout'])


def optimisation_stats(report: Union[Dict, os.PathLike, TextIOBase], plog: os.PathLike, nlog: os.PathLike, templates: os.PathLike, dist: os.PathLike = None, outf: TextIO = None, print_models: int = 10, negdis: 'Negdis' = None) -> Dict:

    if outf is None:
        outf = sys.stdout

    if negdis is None:
        negdis = Negdis(dist=dist) if dist else Negdis.default()

    def _say(txt):
        print(txt, file=outf)

    if isinstance(report, Dict):
        results = report
    else:
        logging.info(f'Stats: reading optimisation results from {report}')
        with ensure_fd(report) as fd:
            results = json.load(fd)

    models = results.get('selected', [])
    clingo_out = results.get('clingo', {})

    calls = len(clingo_out.get('Call', []))
    last_cpu = clingo_out.get('Time', {}).get('CPU', 0.0)
    more_models = clingo_out.get('Models', {}).get('More', 'no') == 'yes'

    if print_models > 0:
        _say('-' * 20)
        _say('Models (only first {}/{}):'.format(print_models, len(models)))


    f_values = []
    msizes = []
    for constraints in sorted(models, key=len):
        f_value, pcorrect, ncorrect, psize, nsize = fitness(constraints, plog, nlog, templates, negdis=negdis)
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

    rep_stats = {
        'id': results.get('id', 'unknown'),
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


def show_hwinfo(outf: TextIO = None):
    if outf is None:
        outf = sys.stdout
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


class Negdis():

    _DEFAULT_RUNNER: 'Negdis' = None

    """Wrapper class for negdis executable."""
    def __init__(self, exe: os.PathLike = None, dist: os.PathLike = None):
        self._negdis_exe = self._find_exe(exe, dist)

    @staticmethod
    def _find_exe(exe: os.PathLike, dist: os.PathLike) -> str:
        negdis_name = 'negdis'
        negdiscmd = shutil.which(exe) if exe else None
        if negdiscmd is not None:
            return negdiscmd
        if dist is not None:
            try:
                platform = next(x for x in ('linux', 'darwin', 'win32') if sys.platform.startswith(x))
                if platform in ('linux', 'darwin'):
                    negdispath = Path(dist).joinpath(platform, negdis_name)
                    if negdispath.is_file():
                        if not os.access(negdispath, os.X_OK):
                            negdispath.chmod(stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH | stat.S_IRUSR | stat.S_IRGRP | stat.S_IROTH)
                        return str(negdispath)
                elif platform == 'win32':
                    negdispath = Path(dist).joinpath(platform, f'{negdis_name}.exe')
                    if negdispath.is_file():
                        return str(negdispath)
            except StopIteration:
                logging.error(f'Unsupported platform {sys.platform}')
        return shutil.which(negdis_name)

    def run(self, *args: str, timeit: bool=False, **kwargs) -> CompletedProcess:
        if self._negdis_exe is None:
            raise RuntimeError('Missing negdis executable')
        timecmd = [shutil.which('time'), '-p'] if timeit and sys.platform != 'win32' and shutil.which('time') else []
        cmd = [self._negdis_exe] + [str(a) for a in args]
        logging.info('Running: ' + ' '.join(shlex.quote(str(a)) for a in cmd))
        cp = run(timecmd + cmd, capture_output=True, text=True, **kwargs)
        return cp

    def _run_to_file(self, cmd: Sequence[str], args: Sequence[str], out: Union[os.PathLike, TextIO], timeit: bool=False, **kwargs) -> CompletedProcess:
        out_path = tmpfname(suffix='.json') if isinstance(out, TextIO) else out

        cmd_line = cmd + (['--out', str(out_path)] if out_path is not None else []) + args
        cp = self.run(*cmd_line, timeit=timeit, **kwargs)

        if isinstance(out, TextIO):
            with open(out_path) as fd:
                shutil.copyfileobj(fd, out)
            os.unlink(out_path)

        return cp

    def version(self) -> str:
        cp = self.run('version')
        return cp.stdout

    def discover(self, pos_logs: Union[os.PathLike, TextIO], neg_logs: Union[os.PathLike, TextIO], templates: Union[os.PathLike, TextIO], outf: Union[os.PathLike, TextIO] = None, fmt: str = 'xes', timeit: bool=False, **kwargs) -> CompletedProcess:

        with ensure_file(pos_logs) as pos_path, ensure_file(neg_logs) as neg_path, ensure_file(templates) as templ_path:
            cp = self._run_to_file(
                ['discover', 'negative'], ['--templ', templ_path, '--fmt', fmt, pos_path, neg_path],
                outf, timeit=timeit, **kwargs)

        return cp

    def compatible(self, pos_logs: Union[os.PathLike, TextIO], constraints: Union[os.PathLike, TextIO], templates: Union[os.PathLike, TextIO], outf: Union[os.PathLike, TextIO] = None, fmt: str = 'xes', timeit: bool=False, **kwargs) -> CompletedProcess:

        with ensure_file(pos_logs) as pos_path, ensure_file(templates) as templ_path:
            cp = self._run_to_file(
                ['discover', 'compatible'], ['--templ', templ_path, '--fmt', fmt, pos_path],
                outf, timeit=timeit, **kwargs)

        return cp

    def check(self, pos_logs: Union[os.PathLike, TextIO], constraints: Union[os.PathLike, TextIO], templates: Union[os.PathLike, TextIO], outf: Union[os.PathLike, TextIO] = None, fmt: str = 'xes', timeit: bool=False, **kwargs) -> CompletedProcess:

        with ensure_file(pos_logs) as pos_path, ensure_file(constraints) as constr_path, ensure_file(templates) as templ_path:
            cp = self._run_to_file(
                ['check', 'constraints'], ['--templ', templ_path, '--fmt', fmt, pos_path, constr_path],
                outf, timeit=timeit, **kwargs)

        return cp

    @classmethod
    def set_default(cls, exe: os.PathLike = None, dist: os.PathLike = None) -> 'Negdis':
        cls._DEFAULT_RUNNER = cls(exe=exe, dist=dist)
        return cls._DEFAULT_RUNNER

    @classmethod
    def default(cls) -> 'Negdis':
        return cls._DEFAULT_RUNNER if cls._DEFAULT_RUNNER else cls.set_default(dist=NEGDIS_DIST)


def run_negdis(*args: str, negdis=None, dist=None, timeit=True, outf: TextIO = None, **kwargs) -> str:
    if outf is None:
        outf = sys.stdout

    negdis_runner = Negdis(exe=negdis, dist=dist) if negdis or dist else Negdis.default()

    cp = negdis_runner.run(*args, timeit=timeit, **kwargs)

    print(cp.stdout, file=outf)
    return 'Running: ' + ' '.join(shlex.quote(str(a)) for a in cp.args) + '\n' + cp.stderr
