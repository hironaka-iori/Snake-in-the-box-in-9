"""Fixed doubling walk (two images of the Q8 record walk joined across
light bit 3), pieces sized within [S_i - slack, S_i + up] of the record
sizes carried along, total >= target.  Piece-selection model pmodel."""
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..', '..'))
_sys.path.insert(0, _HERE)

import sys, json, time, itertools
from pmodel import run
from walks import canon, q3auts, ap
A = [0, 1, 2, 6, 19, 20, 21, 23, 24]; B = [4, 5, 7, 12, 16, 17, 18, 25]
W = [0, 2, 3, 7, 3, 1, 0, 4, 5, 7, 5, 1, 0, 4, 6, 2, 6]
S = [3, 6, 5, 7, 7, 7, 5, 6, 5, 7, 7, 7, 1, 7, 8, 6, 5]
def images():
    D = {}
    for a in q3auts():
        v = tuple(ap(a, c) for c in W)
        D.setdefault(v, tuple(S)); D.setdefault(v[::-1], tuple(S[::-1]))
    return D
def doubling():
    I = images(); seen = set(); out = []
    for a, sa in sorted(I.items()):
        for b, sb in sorted(I.items()):
            if a[-1] != b[0]: continue
            w = list(a) + [c | 8 for c in b]
            cw = canon(w)
            if cw in seen: continue
            seen.add(cw); out.append((w, list(sa) + list(sb)))
    return out
if __name__ == '__main__':
    T, slack, up, tl, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]), sys.argv[5]
    sel = [int(a) for a in sys.argv[6].split(',')] if len(sys.argv) > 6 else None
    for idx, (w, sz) in enumerate(doubling()):
        if sel and idx not in sel: continue
        o = run(5, 4, w, A, B, T, tl=tl, lo=[max(1, s - slack) for s in sz], hi=[s + up for s in sz])
        rec = dict(kind='dblwalk', idx=idx, walk=w, slack=slack, up=up, **o)
        print(json.dumps({a: b for a, b in rec.items() if a not in ('path', 'walk')}), flush=True)
        open(out, 'a').write(json.dumps(rec) + '\n')
