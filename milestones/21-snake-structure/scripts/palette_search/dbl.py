"""Global palette SAT in Q9 = Q5 x Q4 with light bit 3 (vertex bit 8) used
exactly `cross` times, each Q8 half >= half vertices; optional cap on the
number of M-slots per half."""
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..', '..'))
_sys.path.insert(0, _HERE)

import sys, json, time
sys.path.insert(0, _os.path.join(REPO, 'milestones/20-lower-bound-search/scripts'))
sys.path.insert(0, _os.path.join(REPO, 'milestones/21-snake-structure/scripts'))
from lns2 import Model2
from qmodel import check
from pysat.card import CardEnc, EncType
from ptower import forbid
A = [0, 1, 2, 6, 19, 20, 21, 23, 24]; B = [4, 5, 7, 12, 16, 17, 18, 25]
def card(m, lits, op, b):
    f = CardEnc.atleast if op == '>=' else (CardEnc.atmost if op == '<=' else CardEnc.equals)
    enc = f(lits, b, top_id=m.top, encoding=EncType.seqcounter if op != '>=' or b < 40 else EncType.totalizer)
    m.top = max(m.top, enc.nv)
    for c in enc.clauses: m.s.add_clause(c)
def build(T, cross, half, A=A, B=B, bit=8):
    m = Model2(set(), T, forbid=forbid(5, 4, A, B), solver='cadical195')
    x = m.x; zs = []
    for v in range(512):
        if v & (1 << bit): continue
        w = v | (1 << bit)
        if v in x and w in x:
            z = m.new(); zs.append(z)
            m.s.add_clause([-z, x[v]]); m.s.add_clause([-z, x[w]]); m.s.add_clause([z, -x[v], -x[w]])
    if cross is not None: card(m, zs, '=', cross)
    if half:
        for side in (0, 1 << bit):
            card(m, [x[v] for v in x if (v & (1 << bit)) == side], '>=', half)
    return m
if __name__ == '__main__':
    T, cross, half, tl = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
    m = build(T, cross, half)
    t = time.time(); r, p = m.run(time_budget=tl)
    rec = dict(kind='dbl', target=T, cross=cross, half=half, free=len(m.free), result=r, secs=round(time.time() - t, 1), cuts=m.cuts)
    if p: rec['length'] = len(p); rec['valid'] = check(p, 9); rec['path'] = p
    print(json.dumps({a: b for a, b in rec.items() if a != 'path'}), flush=True)
    open('dbl.jsonl', 'a').write(json.dumps(rec) + '\n')
