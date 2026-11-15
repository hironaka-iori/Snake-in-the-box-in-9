#!/usr/bin/env python3
"""Run milestones/35-231-lean/certify/cert231.py unchanged, with its records and core JSONs kept in
lean435/ (another agent works in milestones/35-231-lean/certify), then convert its 4.19 sources
to 4.35 modules with to435.py.

    cert435.py STEP [cert231 args...]      STEP = keys | cores | cnf | replay | status
    cert435.py to435 --plan P NAME...      sources of NAME (in $CERT231_SCR/out) -> lean435/src (merged)

Records: lean435/data/<step>231_<plan>.jsonl. Core JSONs: lean435/cores (default --core).
"""
import os, runpy, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
CERT = os.path.join(ROOT, 'milestones', '35-231-lean', 'certify')
SCR = os.environ.setdefault('CERT231_SCR', os.path.expanduser('~/l435/cert231work'))

if sys.argv[1:2] == ['to435']:
    names = [x for x in sys.argv[2:] if not x.startswith('--') and not x.endswith('.json.gz')]
    sys.exit(subprocess.call([sys.executable, os.path.join(HERE, 'to435.py'), '--in', os.path.join(SCR, 'out'),
                              '--out', os.path.join(ROOT, 'lean435', 'src')] + names))
sys.path.insert(0, CERT)
sys.dont_write_bytecode = True
import cert231  # noqa: E402
import shutil  # noqa: E402
_cad = os.environ.get('CADICAL') or shutil.which('cadical') or '/usr/local/bin/cadical'
cert231.C.K.TOOLCHAIN_CADICAL = _cad          # gen_k7_core's wrapper reads it at call time (4.19 default path)
cert231.DATA = os.environ.get('CERT435_DATA', os.path.join(ROOT, 'lean435', 'data'))
cert231.CORE = os.environ.get('CERT435_CORE', os.path.join(ROOT, 'lean435', 'cores'))
if os.environ.get('CERT435_SEEDS'):                 # a seed plan of our own (prod435.py: every key a seed)
    cert231.seeds_path = lambda a: os.environ['CERT435_SEEDS']
# the parser's --core default was bound at import time of main(): pass it explicitly
args = sys.argv[1:]
if '--core' not in args:
    args = args[:1] + ['--core', cert231.CORE] + args[1:]
sys.argv = [cert231.__file__] + args
cert231.main()
