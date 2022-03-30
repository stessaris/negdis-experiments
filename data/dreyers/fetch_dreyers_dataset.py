#!/usr/bin/env python


from io import TextIOBase
from pathlib import Path
import shutil
import sys
import urllib.request
import xml.etree.ElementTree as ET


DREYERS_URL = r'https://github.com/tslaats/EventLogs/raw/10db2d389b8190651bda5be578a7dad8123df384/Dreyers%20Foundation.xes'
DREYERS_FNAME = 'Dreyers Foundation.xes'


def fetch_dataset(path: Path, source: str = None):
    if source is None:
        source = DREYERS_URL
    with urllib.request.urlopen(source) as response:
        with path.open(mode='wb') as outf:
            shutil.copyfileobj(response, outf)


def split_log(inf: TextIOBase, outp: TextIOBase, outn: TextIOBase):
    in_trace = False
    in_log = False

    header = r'<?xml version="1.0" encoding="UTF-8" ?>'
    print(header, file=outp)
    print(header, file=outn)
    for event, node in ET.iterparse(inf, events=('start', 'end')):
        if event == 'start':
            if node.tag == 'trace':
                in_trace = True
            elif node.tag == 'log':
                in_log = True
                tag_str = '<{} {}>'.format(node.tag, ' '.join(f'{k}="{v}"' for k,v in node.attrib.items()))
                print(tag_str, file=outp)
                print(tag_str, file=outn)
        elif event == 'end':
            if node.tag == 'trace':
                trace_str = ET.tostring(node, encoding='unicode')
                if positive_trace(node):
                    print(trace_str, file=outp)
                else:
                    print(trace_str, file=outn)
                node.clear()
                in_trace = False
            elif not in_trace and node.tag != 'log':
                node_str = ET.tostring(node, encoding='unicode').strip()
                print(node_str, file=outp)
                print(node_str, file=outn)
    if in_log:
        print('</log>', file=outp)
        print('</log>', file=outn)


def positive_trace(trace: ET.Element) -> bool:
    return trace.tag == 'trace' and trace_name(trace).endswith('_P')


def trace_name(node: ET.Element) -> str:
    for s_node in node.findall('string'):
        if s_node.get('key', 'unknown').lower().endswith('name'):
            return s_node.get('value', '')
    return ''


def setup_dreyers_dataset(dest: Path, source: str = None):
    pos_file = dest.parent.joinpath('{}.pos{}'.format(dest.stem, ''.join(dest.suffixes)))
    neg_file = dest.parent.joinpath('{}.neg{}'.format(dest.stem, ''.join(dest.suffixes)))

    if dest.exists() and pos_file.exists() and neg_file.exists():
        print(f'Dataset already in {dest}, no need to fetch data')
    else:
        fetch_dataset(dest, source=source)
        with dest.open() as inf, pos_file.open(mode='w') as outp, neg_file.open(mode='w') as outn:
            split_log(inf, outp, outn)


def main(*cargs: str) -> int:
    if len(cargs) > 0:
        dest_path = Path(cargs[0])
        if dest_path.is_dir():
            dest_path = dest_path.joinpath(DREYERS_FNAME)
    else:
        dest_path = Path(__file__).parent.joinpath(DREYERS_FNAME)
    try:
        setup_dreyers_dataset(dest_path, source=DREYERS_URL)
    except Exception as e:
        print(f'Error in setting up dataset: {e}', file=sys.stderr)
        return -1
    return 0


if __name__ == "__main__":
    sys.exit(main(*sys.argv[1:]))