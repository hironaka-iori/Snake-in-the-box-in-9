"""Structural invariants of the 131-entry Q9 bank (work/bank9.json).

Writes data/invariants.json with, per entry: sorted coordinate usage, light
coordinates, quotient walk (cell sequence) and piece sizes, per-cell vertex
counts, weak cells and their Q4 distance pattern, the parity palette
(A, B, M) of the heavy Q5 and its class up to Q5 symmetry.
Run from the repository root:  python3 milestones/21-snake-structure/scripts/invariants.py
"""
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..'))
_sys.path.insert(0, _HERE)

import json, os, sys
from collections import Counter
from itertools import permutations
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from common import load, pc, light
from bankwalk import quotient
A5 = []
for p in permutations(range(5)):
    for t in range(32):
        A5.append([sum(((x >> i) & 1) << p[i] for i in range(5)) ^ t for x in range(32)])
def canonpair(A, B):
    best = None
    for s in A5:
        a = tuple(sorted(s[x] for x in A)); b = tuple(sorted(s[x] for x in B))
        key = min((a, b), (b, a))
        if best is None or key < best: best = key
    return best
def main(out):
    bank = load(); rows = []; pal = Counter()
    for idx, e in enumerate(bank):
        cc = {int(a): v for a, v in e['coordinate_counts'].items()}
        k = sum(1 for v in cc.values() if v < 15)
        seq, sizes, L, H = quotient(e, k)
        vs = e['vertex_sequence']
        def cell(v): return sum(((v >> c) & 1) << i for i, c in enumerate(L))
        def hv(v): return sum(((v >> c) & 1) << i for i, c in enumerate(H))
        tot = Counter(); nvis = Counter()
        for c, s in zip(seq, sizes): tot[c] += s; nvis[c] += 1
        row = dict(idx=idx, k=k, usage=sorted(cc.values(), reverse=True), light=L,
                   light_counts=[cc[c] for c in L], visits=len(seq), walk=seq, piece_sizes=sizes,
                   cell_counts=[tot[c] for c in range(1 << k)], cell_visits=[nvis[c] for c in range(1 << k)])
        S = set(vs)
        row['undominated'] = sum(1 for x in range(512) if x not in S and not any((x ^ (1 << d)) in S for d in range(9)))
        row['endpoint_distance'] = e['endpoint_distance']
        crossing = L[0]
        a = sum(1 for v in vs if not (v >> crossing) & 1)
        row['crossing_split'] = sorted([a, len(vs) - a], reverse=True)
        if k == 4:
            weak = sorted(c for c in range(16) if tot[c] <= 11)
            row['weak_cells'] = weak
            row['weak_distances'] = sorted(pc(x ^ y) for i, x in enumerate(weak) for y in weak[i + 1:])
            T = {x: set() for x in range(32)}
            for v in vs: T[hv(v)].add(cell(v))
            A = [x for x in range(32) if T[x] and all(pc(c) % 2 == 0 for c in T[x])]
            B = [x for x in range(32) if T[x] and all(pc(c) % 2 == 1 for c in T[x])]
            row['palette_sizes'] = [len(A), len(B), 32 - len(A) - len(B)]
            cp = canonpair(A, B); row['palette_class'] = [list(cp[0]), list(cp[1])]
            pal[json.dumps(row['palette_class'])] += 1
            tr = [hv(x) for x, y in zip(vs, vs[1:]) if cell(x) != cell(y)]
            row['transitions_in_M'] = all(x not in A and x not in B for x in tr)
        rows.append(row)
    summ = dict(
        families=Counter(r['k'] for r in rows),
        weak_distance_patterns=Counter(json.dumps(r.get('weak_distances')) for r in rows if r['k'] == 4),
        palette_sizes=Counter(json.dumps(r['palette_sizes']) for r in rows if r['k'] == 4),
        palette_classes=len(pal),
        transitions_in_M=Counter(r['transitions_in_M'] for r in rows if r['k'] == 4),
        visits=Counter(r['visits'] for r in rows),
        crossing_split=Counter(json.dumps(r['crossing_split']) for r in rows),
        cell_profiles=Counter(json.dumps(sorted(r['cell_counts'], reverse=True)) for r in rows).most_common(6),
        undominated=Counter(r['undominated'] for r in rows))
    json.dump(dict(summary=summ, entries=rows), open(out, 'w'), indent=None, separators=(',', ':'))
    print(json.dumps(summ, indent=1))
if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'invariants.json')
