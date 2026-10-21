"""Palette tower for a general palette of Q_h: global SAT in Q_h x Q_k
(milestone 20 Model2 embedded in Q9 by forbidding vertices)."""
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..', '..'))
_sys.path.insert(0, _HERE)

import sys, os, time, json
sys.path.insert(0, _os.path.join(REPO, 'milestones/20-lower-bound-search/scripts'))
from lns2 import Model2
def pc(x): return bin(x).count('1')
def forbid(h, k, A, B):
    A=set(A); B=set(B); bad=[]
    for v in range(512):
        x = v & ((1 << h) - 1); c = v >> h
        if c >= (1 << k) or (x in A and pc(c) % 2) or (x in B and pc(c) % 2 == 0): bad.append(v)
    return bad
def test(h, k, A, B, T, tl):
    m = Model2(set(), T, forbid=forbid(h, k, A, B), solver='cadical195')
    t = time.time(); r, p = m.run(time_budget=tl); m.close()
    return r, round(time.time() - t, 1), p
