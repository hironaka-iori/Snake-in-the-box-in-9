"""Rank palettes by whether they reach the optimum in Q_{h+k}:
a(6..8) = 26, 50, 98 edges, i.e. 27, 51, 99 vertices."""
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..', '..'))
_sys.path.insert(0, _HERE)

import sys, json, time
from ptower import test
from splits import palette, forest, vs
import itertools
OPT = {6: 27, 7: 51, 8: 99}
def cands():
    out = []
    for h in (5, 6):
        for H in itertools.combinations(range(8), h):
            A, B, walk = palette(vs, 8, list(H))
            out.append(dict(src='q8rec', H=list(H), h=h, A=A, B=B, visits=len(walk)))
    return out
if __name__ == '__main__':
    out = sys.argv[1]; tl = float(sys.argv[3])
    C = json.load(open(sys.argv[2]))
    for c in C:
        h = c['h']; res = {}
        for n in range(h + 1, 8):
            k = n - h; r, s, p = test(h, k, c['A'], c['B'], OPT[n], tl)
            res[n] = [r, s]
            if r != 'SAT': break
        c['nAB'] = len(c['A']) + len(c['B']); c['forest'] = forest(c['A'], h) and forest(c['B'], h); c['tower'] = res
        print(json.dumps(c), flush=True); open(out, 'a').write(json.dumps(c) + '\n')
