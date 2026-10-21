"""Random palettes (A, sigma(A)) with A an induced path of Q5 and sigma an
involutive automorphism of Q5, A and sigma(A) disjoint.  Score each by its
palette-tower maxima in Q6 and Q7 (global SAT, tower.Model2)."""
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..'))
_sys.path.insert(0, _HERE)

import sys, random, time, json, itertools
sys.path.insert(0, _os.path.join(REPO, 'milestones', '20-lower-bound-search', 'scripts'))
from lns2 import Model2
from tower import forbid
from pieces import pieces
def auts():
    out = []
    for p in itertools.permutations(range(5)):
        for t in range(32):
            f = [sum(((x >> i) & 1) << p[i] for i in range(5)) ^ t for x in range(32)]
            if all(f[f[x]] == x for x in range(32)) and any(f[x] != x for x in range(32)): out.append(f)
    return out
INV = auts()
def tmax(k, A, B, lo, hi, tl):
    best = None
    for T in range(lo, hi + 1):
        m = Model2(set(), T, forbid=forbid(k, True, A, B), solver='cadical195')
        r, p = m.run(time_budget=tl)
        if r == 'SAT': best = T; continue
        return best, r
    return best, 'SAT'
if __name__ == '__main__':
    L = int(sys.argv[1]); n = int(sys.argv[2]); seed = int(sys.argv[3]); out = sys.argv[4]
    rnd = random.Random(seed)
    P = [p for p in pieces(list(range(32))) if len(p) == L]
    done = 0
    while done < n:
        A = set(rnd.choice(P)); s = rnd.choice(INV); B = set(s[x] for x in A)
        if A & B: continue
        t = time.time()
        q6, r6 = tmax(1, A, B, 24, 28, 20)
        q7, r7 = tmax(2, A, B, 47, 52, 30)
        rec = dict(L=L, A=sorted(A), B=sorted(B), q6=q6, q6_stop=r6, q7=q7, q7_stop=r7, secs=round(time.time() - t, 1))
        print(json.dumps(rec), flush=True); open(out, 'a').write(json.dumps(rec) + '\n'); done += 1
