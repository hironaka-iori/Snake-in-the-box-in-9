"""dblwalk for any heavy-coordinate split H (5 of the 8 coordinates) of the
Q8 record: its palette (A, B) and its Q3 walk with piece sizes, doubled
across a fourth light bit; piece model, sizes in [S_i - slack, S_i + up]."""
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..', '..'))
_sys.path.insert(0, _HERE)

import sys, json
from pmodel import run
from walks import canon, q3auts, ap
from splits import palette, vs
def setup(H):
    A, B, W = palette(vs, 8, H)
    L = [c for c in range(8) if c not in H]
    cell = lambda v: sum(((v >> c) & 1) << i for i, c in enumerate(L))
    S = []; prev = None
    for v in vs:
        c = cell(v)
        if c != prev: S.append(0); prev = c
        S[-1] += 1
    return A, B, W, S
def doubling(W, S):
    I = {}
    for a in q3auts():
        v = tuple(ap(a, c) for c in W); I.setdefault(v, tuple(S)); I.setdefault(v[::-1], tuple(S[::-1]))
    seen = set(); out = []
    for a, sa in sorted(I.items()):
        for b, sb in sorted(I.items()):
            if a[-1] != b[0]: continue
            w = list(a) + [c | 8 for c in b]; cw = canon(w)
            if cw in seen: continue
            seen.add(cw); out.append((w, list(sa) + list(sb)))
    return out
if __name__ == '__main__':
    H = [int(a) for a in sys.argv[1].split(',')]
    T, slack, up, tl, out = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), float(sys.argv[5]), sys.argv[6]
    A, B, W, S = setup(H)
    D = doubling(W, S); print('walks', len(D), 'visits', len(D[0][0]), flush=True)
    for idx, (w, sz) in enumerate(D):
        o = run(5, 4, w, A, B, T, tl=tl, lo=[max(1, s - slack) for s in sz], hi=[s + up for s in sz])
        rec = dict(kind='dblwalkH', H=H, idx=idx, walk=w, slack=slack, up=up, **o)
        print(json.dumps({a: b for a, b in rec.items() if a not in ('path', 'walk')}), flush=True)
        open(out, 'a').write(json.dumps(rec) + '\n')
