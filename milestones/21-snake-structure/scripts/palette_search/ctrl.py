# Controls: Q8 piece model (record walk) sizes exact -> 99 SAT; sizes in [S, S+1] -> 100 must be UNSAT (a(8)=98).
# Q9 doubling walk 0: lower half sizes exact, upper half sizes in [1, S]: target 116 must be SAT.
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..', '..'))
_sys.path.insert(0, _HERE)
import sys, json; from pmodel import run
from dblwalk import doubling, A, B, W, S
o = run(5, 3, W, A, B, 100, tl=300, lo=S, hi=[s + 1 for s in S]); print('q8 grow', {a: b for a, b in o.items() if a != 'path'}, flush=True)
w, sz = doubling()[0]
o = run(5, 4, w, A, B, 116, tl=300, lo=sz[:17] + [1] * 17, hi=sz); print('q9 ctrl', {a: b for a, b in o.items() if a != 'path'}, flush=True)
