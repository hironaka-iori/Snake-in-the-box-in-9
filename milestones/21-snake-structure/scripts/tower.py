"""Palette tower: Q_{5+k} = Q5 x Qk with the bank palette (A, B, M).
Even light cells may use A u M, odd cells B u M.  Global SAT (milestone 20
Model2: degrees, two endpoints, cardinality, lazy cycle cuts, colour balance,
hexagon and Q4 capacity cuts), embedded in Q9 by forbidding the unused
light coordinates.  Reports SAT/UNSAT/UNKNOWN for 'at least T vertices'."""
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..'))
_sys.path.insert(0, _HERE)

import sys, time, json
sys.path.insert(0, _os.path.join(REPO, 'milestones', '20-lower-bound-search', 'scripts'))
from lns2 import Model2
def pc(x): return bin(x).count('1')
A = {0,1,2,5,6,13,24,26,27,28,29}; B = {3,4,7,8,9,11,12,16,20,23,31}
M = set(range(32)) - A - B
def forbid(k, palette=True, A=A, B=B):
    bad = []
    for v in range(512):
        x = v & 31; c = v >> 5
        if c >= (1 << k): bad.append(v); continue
        if palette and ((x in A and pc(c) % 2) or (x in B and pc(c) % 2 == 0)): bad.append(v)
    return bad
if __name__ == '__main__':
    k = int(sys.argv[1]); T = int(sys.argv[2]); tl = float(sys.argv[3]); pal = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    PA, PB = A, B
    if len(sys.argv) > 6:
        PA, PB = [set(z) for z in json.load(open(sys.argv[6]))]
    t = time.time()
    m = Model2(set(), T, forbid=forbid(k, pal, PA, PB), solver='cadical195')
    r, p = m.run(time_budget=tl)
    rec = dict(palette_file=sys.argv[6] if len(sys.argv) > 6 else 'bank', k=k, n=5 + k, palette=pal, target=T, free=len(m.free), result=r, secs=round(time.time() - t, 1), cuts=m.cuts)
    if p: rec['path'] = p
    print(json.dumps({a: b for a, b in rec.items() if a != 'path'}), flush=True)
    if len(sys.argv) > 5: open(sys.argv[5], 'a').write(json.dumps(rec) + '\n')
