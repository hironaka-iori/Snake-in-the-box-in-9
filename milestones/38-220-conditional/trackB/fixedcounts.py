"""Per-window minimum of share12 with the 7 centre counts fixed (lumped: 8 means [8,21]),
CP-SAT, validated against the wincert CNF.  usage: fixedcounts.py SHAPE COUNTS tl out"""
import sys, os, json
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from cpmin import minimize, window_from_dirs
from sawit import check
dirs = json.loads(sys.argv[1]); cnt = json.loads(sys.argv[2]); tl = float(sys.argv[3]); out = sys.argv[4]
al = [(c, c) if c < 8 else (8, 21) for c in cnt]
r = minimize(dirs, tl=tl, wA=24, workers=int(os.environ.get('W', 1)), alpha=al)
r['counts'] = cnt
if 'sel' in r:
    r['valid_cnf'] = bool(check(window_from_dirs(list(dirs)), r['sel']))
with open(out, 'a') as f: f.write(json.dumps(r) + '\n')
print(json.dumps({k: v for k, v in r.items() if k != 'sel'}), flush=True)
