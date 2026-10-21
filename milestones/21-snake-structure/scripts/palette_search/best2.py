"""Best length in the doubling family, walk 0, Q8-record split, sizes in [S-6, S] (piece model)."""
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_sys.path.insert(0, _HERE)

import sys, json, time
from pmodel import run
import dblwalk
w, sz = dblwalk.doubling()[0]
best = None
for T in [int(a) for a in sys.argv[1].split(',')]:
    o = run(5, 4, w, dblwalk.A, dblwalk.B, T, tl=float(sys.argv[2]), lo=[max(1, s - 6) for s in sz], hi=sz)
    print(json.dumps(dict(kind='best_dblwalk', slack=6, **{a: b for a, b in o.items() if a != 'path'})), flush=True)
    if o['result'] == 'SAT': json.dump(o, open('best_dblwalk_%d.json' % o['length'], 'w'))
    if o['result'] != 'SAT': break
