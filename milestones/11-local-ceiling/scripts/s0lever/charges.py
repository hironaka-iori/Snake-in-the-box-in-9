"""Per-vertex charges gamma(x) = alpha(x) + (share of empty squares) for snakes / adversaries.
Definitions follow work/spectral/SquareIncidence.lean:
  singleton p ab v : v selected, flip a v, flip b v, flip b (flip a v) unselected   (alpha = sum over 36 pairs)
  empty p ab v     : all four corners unselected (anchored at every corner -> totalEmptyAnchored = 4*s0)
Charges (all are lower bounds: sum_x gamma(x) <= T + 2*s0):
  ex   : exact fair share, each empty square Q gives 2/|N(Q)∩S| to every selected vertex adjacent to Q (radius 4)
  dom  : corner rule, each unselected q holds e0(q)/2 (e0 = #empty squares containing q) and splits it equally among
         its selected neighbours (radius 3; exact iff every corner of every empty square has a selected neighbour)
  c3   : direction rule, (Q empty, x in Q^k, t = |Q^k ∩ S|) gives 2/(7t)  (radius 3)
  cheap: 2 e(x)/21 (milestones/11-local-ceiling/scripts/cheap_s0.py)
"""
import json, itertools, sys
from fractions import Fraction as F
import os
R = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../..')) + '/'
pairs = list(itertools.combinations(range(9), 2))
popc = [bin(i).count('1') for i in range(512)]

def squares():
    for b in range(512):
        for i, j in pairs:
            if b >> i & 1 or b >> j & 1: continue
            yield (i, j), (b, b | 1 << i, b | 1 << j, b | 1 << i | 1 << j)
SQ = list(squares())
assert len(SQ) == 4608

def analyse(seq, cyclic):
    S = set(seq); sel = [1 if x in S else 0 for x in range(512)]
    v = len(S)
    alpha = {x: sum(1 for i, j in pairs if not (sel[x ^ 1 << i] or sel[x ^ 1 << j] or sel[x ^ 1 << i ^ 1 << j])) for x in S}
    T = sum(alpha.values())
    s0 = 0; deep = 0
    ex = {x: F(0) for x in S}; c3 = {x: F(0) for x in S}; e = {x: 0 for x in S}
    e0 = [0] * 512
    nQ = []
    for (i, j), Q in SQ:
        if any(sel[q] for q in Q): continue
        s0 += 1
        for q in Q: e0[q] += 1
        nb = [q ^ 1 << k for q in Q for k in range(9) if k not in (i, j)]
        sn = [y for y in nb if sel[y]]
        dirs = {}
        for q in Q:
            for k in range(9):
                if k in (i, j): continue
                if sel[q ^ 1 << k]: dirs[k] = dirs.get(k, 0) + 1
        nQ.append((len(dirs), len(sn)))
        if not sn: deep += 1; continue
        for y in sn:
            ex[y] += F(2, len(sn)); e[y] += 1
            k = [k for k in range(9) if k not in (i, j) and not sel[y ^ 1 << k] and (y ^ 1 << k) in Q][0]
            c3[y] += F(2, 7 * dirs[k])
    # corner rule
    dom = {x: F(0) for x in S}; undominated_mass = F(0)
    for q in range(512):
        if sel[q] or e0[q] == 0: continue
        nbs = [q ^ 1 << k for k in range(9) if sel[q ^ 1 << k]]
        if not nbs: undominated_mass += F(e0[q], 2); continue
        for y in nbs: dom[y] += F(e0[q], 2 * len(nbs))
    ident = (9214 if not cyclic else 9216) - 35 * v
    assert T + 2 * s0 == ident, (T, s0, ident)
    assert sum(ex.values()) == 2 * (s0 - deep)
    assert sum(dom.values()) + undominated_mass == 2 * s0
    g = {}
    for x in S:
        g[x] = dict(alpha=alpha[x], ex=alpha[x] + ex[x], dom=alpha[x] + dom[x], c3=alpha[x] + c3[x],
                    cheap=alpha[x] + F(2 * e[x], 21))
    return dict(v=v, T=T, s0=s0, deep=deep, undom=float(undominated_mass), g=g, nQ=nQ, sel=sel)

if __name__ == '__main__':
    bank = [b['vertex_sequence'] for b in json.load(open(R + 'work/bank9.json'))]
    r = analyse(bank[0], False)
    print('bank0: v', r['v'], 'T', r['T'], 's0', r['s0'], 'T+2s0', r['T'] + 2 * r['s0'], '9214-35v', 9214 - 35 * r['v'],
          'deep', r['deep'], 'undominated mass', r['undom'])
