"""Vectorised minimal exclusion set for a FastAutomaton (potential route).

For every extension (shape, next label) keep `cnt[code]` = number of distinct
excluded windows blocking the transition with symbol code `code`.  A window key
x blocks the codes whose relevant low digits equal x's symbols (an arithmetic
index set), in one or both orientations.  Removing x is safe for the current
potential pi if every code with cnt == 1 among the ones x blocks has
non-negative slack  q*w - p + pi[u] - pi[v].  Passes repeat with a recomputed
potential until nothing more can be dropped.

  python minimize_fast.py --L 7 --k 6 --K 5 --radius 3
"""
import argparse, json, os
from fractions import Fraction as Fr
import numpy as np
from refine import Oracle, DATA
from refine_fast import FastAutomaton, prune, howard, bellman_ford, vertex_bound


def sym_code(alpha, ns):
    code = 0
    for lo, hi in alpha:
        code = code * ns + ((lo if lo == hi else ns) - 1)
    return code


class Blockers:
    def __init__(self, A, keys):
        self.A = A
        ns, k = A.ns, A.k
        self.cnt = [np.zeros(ns ** k, np.int16) for _ in A.ext]
        self.by_shape = {}
        for x in keys:
            self.by_shape.setdefault(x[0], []).append(x)
        self.hits = {}                      # key -> list of (ext index, code array)
        for e, (i, d, nxt, ds, wins) in enumerate(A.ext):
            for cc, (fw, rv) in wins.items():
                step = ns ** cc
                js = np.arange(ns ** (k - cc)) * step
                for x in self.by_shape.get(fw, []):
                    c0 = sym_code(x[1], ns)
                    codes = c0 + js
                    if rv == fw and A.rev[cc][c0] != c0:
                        codes = np.concatenate([codes, A.rev[cc][c0] + js])
                    self.hits.setdefault(x, []).append((e, codes))
                if rv != fw:
                    for x in self.by_shape.get(rv, []):
                        c0 = A.rev[cc][sym_code(x[1], ns)]
                        self.hits.setdefault(x, []).append((e, c0 + js))
        for x, lst in self.hits.items():
            for e, codes in lst:
                self.cnt[e][codes] += 1

    def edges(self):
        A = self.A
        U, V, W = [], [], []
        for e, (i, d, nxt, ds, wins) in enumerate(A.ext):
            codes = np.nonzero(self.cnt[e] == 0)[0]
            U.append(i * A.m1 + codes // A.ns); V.append(nxt * A.m1 + codes % A.m1); W.append(codes % A.ns + 1)
        return (np.concatenate(U).astype(np.int64), np.concatenate(V).astype(np.int64),
                np.concatenate(W).astype(np.int64))

    def removable(self, x, pi, p, q):
        A = self.A
        for e, codes in self.hits[x]:
            i, d, nxt, ds, wins = A.ext[e]
            newly = codes[self.cnt[e][codes] == 1]
            if len(newly) == 0:
                continue
            u = i * A.m1 + newly // A.ns; v = nxt * A.m1 + newly % A.m1; w = newly % A.ns + 1
            if (q * w - p + pi[u] - pi[v] < 0).any():
                return False
        return True

    def remove(self, x):
        for e, codes in self.hits[x]:
            self.cnt[e][codes] -= 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=7)
    ap.add_argument('--k', type=int, default=6)
    ap.add_argument('--K', type=int, default=5)
    ap.add_argument('--radius', type=int, default=3)
    ap.add_argument('--avoid', help='JSON list of {dirs, alpha} windows never to keep (expensive certificates)')
    ap.add_argument('--tag', default='')
    a = ap.parse_args()
    A = FastAutomaton(a.L, a.k, a.K)
    O = Oracle(a.radius)
    if a.avoid:
        for e in json.load(open(a.avoid)):
            O.known[(tuple(e['dirs']), tuple(tuple(x) for x in e['alpha']))] = 'AVOID'
    keys = [x for x, st in O.known.items() if st == 'UNSAT' and 2 <= len(x[1]) <= a.k
            and all(1 <= (lo if lo == hi else A.ns) <= A.ns for lo, hi in x[1])]
    Bk = Blockers(A, keys)
    keep = {x for x in keys if x in Bk.hits}
    print('relevant exclusions', len(keep), flush=True)
    U, V, W = Bk.edges()
    m = prune(A.n, U, V); idx = np.nonzero(m)[0]
    mu, cyc = howard(A.n, U[idx], V[idx], W[idx]); cyc = [idx[e] for e in cyc]
    lam = Fr(int(W[cyc].sum()), len(cyc)); p, q = lam.numerator, lam.denominator
    pi = bellman_ford(A.n, U, V, W, p, q); assert pi is not None
    print('full set: mean', lam, 'range', int(pi.max() - pi.min()), flush=True)
    order = sorted(keep, key=lambda x: (-len(x[1]), -len(set(x[0]))))     # drop long windows first
    while True:
        dropped = 0
        for x in order:
            if x in keep and Bk.removable(x, pi, p, q):
                Bk.remove(x); keep.discard(x); dropped += 1
        U, V, W = Bk.edges()
        pi2 = bellman_ford(A.n, U, V, W, p, q); assert pi2 is not None
        pi = pi2
        print('kept', len(keep), 'dropped', dropped, 'range', int(pi.max() - pi.min()), flush=True)
        if dropped == 0:
            break
    m = prune(A.n, U, V); idx = np.nonzero(m)[0]
    mu, cyc = howard(A.n, U[idx], V[idx], W[idx]); cyc = [idx[e] for e in cyc]
    lam2 = Fr(int(W[cyc].sum()), len(cyc)); assert lam2 == lam, (lam, lam2)
    vb = vertex_bound(A, U, V, W)
    R = int(pi.max() - pi.min()); L = a.L
    C = p * L - q * (L - 1) + R
    Bp = (9179 * q + C - 8 * q) // (p + 35 * q)
    from collections import Counter
    out = {'L': a.L, 'k': a.k, 'K': a.K, 'radius': a.radius, 'min_mean': str(lam), 'potential_range': R,
           'potential_bound_edges': Bp, 'dp_bound_edges': vb - 1, 'edges': int(len(U)),
           'by_centres': dict(Counter(len(x[1]) for x in keep)),
           'exclusions': [{'dirs': list(x[0]), 'alpha': [list(r) for r in x[1]]} for x in sorted(keep)]}
    path = os.path.join(DATA, f'minimal_L{a.L}_k{a.k}_K{a.K}_r{a.radius}{a.tag}.json')
    json.dump(out, open(path, 'w'), indent=1)
    print(json.dumps({k2: v for k2, v in out.items() if k2 != 'exclusions'}))
    print('wrote', path)


if __name__ == '__main__':
    main()
