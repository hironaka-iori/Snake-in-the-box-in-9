"""Feasibility (no length target) of the doubling families: walk 0, size floors only."""
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_sys.path.insert(0, _HERE)

import sys, json, time
from pmodel import run
import dblwalk
w, sz = dblwalk.doubling()[0]
for slack in (2, 4, 6):
    o = run(5, 4, w, dblwalk.A, dblwalk.B, 0, tl=120, lo=[max(1, s - slack) for s in sz], hi=sz)
    print(json.dumps(dict(kind='feas_dblwalk', slack=slack, **{a: b for a, b in o.items() if a != 'path'})), flush=True)
