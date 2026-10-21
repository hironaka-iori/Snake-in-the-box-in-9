"""Q9 = Q6 x Q3: doubling walks of the Q8 record's Q6 x Q2 walk across a
third light bit, record piece sizes carried along, QModel (degree model)
with the record's Q6 palette, sizes in [S_i - slack, S_i + up]."""
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..', '..'))
_sys.path.insert(0, _HERE)

import sys, json, time, itertools
sys.path.insert(0, _os.path.join(REPO, 'milestones/21-snake-structure/scripts'))
from qmodel import QModel, check
from splits import palette, vs
def pc(x): return bin(x).count('1')
H = [int(a) for a in sys.argv[6].split(',')] if len(sys.argv) > 6 else [0, 1, 3, 4, 6, 7]
L = [c for c in range(8) if c not in H]
A, B, W = palette(vs, 8, H)
cell = lambda v: sum(((v >> c) & 1) << i for i, c in enumerate(L))
S = []; prev = None
for v in vs:
    c = cell(v)
    if c != prev: S.append(0); prev = c
    S[-1] += 1
def ap2(p, t, c): return sum(((c >> i) & 1) << p[i] for i in range(2)) ^ t
def canon3(walk):
    best = None
    for p in itertools.permutations(range(3)):
        for t in range(8):
            if pc(t) % 2: continue
            v = tuple(sum(((c >> i) & 1) << p[i] for i in range(3)) ^ t for c in walk)
            for u in (v, v[::-1]):
                if best is None or u < best: best = u
    return best
def doubling():
    I = {}
    for p in itertools.permutations(range(2)):
        for t in range(4):
            v = tuple(ap2(p, t, c) for c in W); I.setdefault(v, tuple(S)); I.setdefault(v[::-1], tuple(S[::-1]))
    seen = set(); out = []
    for a, sa in sorted(I.items()):
        for b, sb in sorted(I.items()):
            if a[-1] != b[0]: continue
            w = list(a) + [c | 4 for c in b]; cw = canon3(w)
            if cw in seen: continue
            seen.add(cw); out.append((w, list(sa) + list(sb)))
    return out
if __name__ == '__main__':
    T, slack, up, tl, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]), sys.argv[5]
    M = set(range(64)) - set(A) - set(B)
    for idx, (w, sz) in enumerate(doubling()):
        allowed = [M | (set(A) if pc(c) % 2 == 0 else set(B)) for c in w]
        t = time.time()
        Mo = QModel(6, 3, w, target=T, fix_start=False, minsize={i: max(1, s - slack) for i, s in enumerate(sz)},
                    maxsize={i: s + up for i, s in enumerate(sz)}, allowed=allowed, bnd_allowed=M)
        r, p = Mo.solve(tlimit=tl)
        rec = dict(kind='dbl6', H=H, idx=idx, walk=w, sizes=sz, slack=slack, up=up, target=T,
                   result={None: 'UNKNOWN', False: 'UNSAT', True: 'SAT'}[r], secs=round(time.time() - t, 1), cuts=Mo.cuts)
        if p: rec['length'] = len(p); rec['valid'] = check(p, 9); rec['path'] = p
        print(json.dumps({a: b for a, b in rec.items() if a not in ('path', 'walk')}), flush=True)
        open(out, 'a').write(json.dumps(rec) + '\n')
