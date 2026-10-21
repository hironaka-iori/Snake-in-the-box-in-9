"""Single-crossing palette family in Q9 = Q5 x Q4 (bank palette).
Light coordinate 5 (bit 5) is used exactly `cross` times; optionally each
Q8 half (bit 5 = 0 / 1) must contain at least `half` vertices."""
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..'))
_sys.path.insert(0, _HERE)

import sys, time, json
sys.path.insert(0, _os.path.join(REPO, 'milestones', '20-lower-bound-search', 'scripts'))
from lns2 import Model2
from pysat.card import CardEnc, EncType
from tower import forbid
if __name__ == '__main__':
    T = int(sys.argv[1]); cross = int(sys.argv[2]); half = int(sys.argv[3]); tl = float(sys.argv[4])
    m = Model2(set(), T, forbid=forbid(4, True), solver='cadical195')
    x = m.x; zs = []
    for v in range(512):
        if v & 32: continue
        w = v | 32
        if v in x and w in x:
            z = m.new(); zs.append(z)
            m.s.add_clause([-z, x[v]]); m.s.add_clause([-z, x[w]]); m.s.add_clause([z, -x[v], -x[w]])
    enc = CardEnc.equals(zs, cross, top_id=m.top, encoding=EncType.seqcounter); m.top = max(m.top, enc.nv)
    for c in enc.clauses: m.s.add_clause(c)
    if half:
        for side in (0, 32):
            lits = [x[v] for v in x if (v & 32) == side]
            enc = CardEnc.atleast(lits, half, top_id=m.top, encoding=EncType.seqcounter); m.top = max(m.top, enc.nv)
            for c in enc.clauses: m.s.add_clause(c)
    t = time.time(); r, p = m.run(time_budget=tl)
    rec = dict(target=T, cross=cross, half=half, free=len(m.free), result=r, secs=round(time.time() - t, 1), cuts=m.cuts)
    if p: rec['path'] = p
    print(json.dumps({a: b for a, b in rec.items() if a != 'path'}), flush=True)
    open('doubling.jsonl', 'a').write(json.dumps(rec) + '\n')
