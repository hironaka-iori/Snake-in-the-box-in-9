"""Minimal set of window exclusions that keeps the direction-automaton bound.

Input: the oracle cache (solver answers).  Output: a small list of UNSAT
window keys such that the automaton using only those keys still has the same
minimum cycle mean and the same exact vertex bound.

Algorithm (dual pruning, then greedy):
  1. Build the automaton with every known UNSAT key; get lambda = p/q and an
     integer potential pi with  q*w - p + pi[u] - pi[v] >= 0  on all allowed
     edges.  Every candidate edge (allowed or not) is given its "blockers",
     the UNSAT keys among its windows.
  2. An exclusion X is redundant for the potential if every edge whose
     blockers are a subset of (dropped ∪ {X}) has non-negative slack under
     pi.  Drop such X greedily, cheapest certification first (fewest centres,
     then smallest ball).  Recompute the potential and repeat until stable.
  3. Verify the final set with the exact DP vertex bound.

  python minimize.py --L 5 --k 4 --K 5 --target-edges 239
"""
import argparse, json, os
from fractions import Fraction as Fr
import numpy as np
from refine import Automaton, Oracle, prune, howard, exact_check, DATA
from direction_bound import bound


def potential_for(A, U, V, W):
    m = prune(A.n, U, V)
    idx = np.nonzero(m)[0]
    mu, cyc = howard(A.n, U[idx], V[idx], W[idx])
    cyc = [idx[e] for e in cyc]
    lam = Fr(int(W[cyc].sum()), len(cyc))
    # the potential must be valid on every allowed edge, not only the pruned core:
    # a finite path may pass through dead-end states near its ends
    pi = exact_check(A.n, U, V, W, lam.numerator, lam.denominator)
    assert pi is not None
    return lam, pi, idx


def all_candidates(A):
    """Every candidate edge with its window keys (no oracle filtering)."""
    U, V, W, WIN = [], [], [], []
    for (c, a), u in A.sid.items():
        for ds_ext, nc in A.dtrans[c]:
            for s in A.sym:
                al = a + (s,)
                U.append(u); V.append(A.sid[(nc, al[1:])]); W.append(s)
                WIN.append(A.windows(ds_ext, al))
    return np.array(U), np.array(V), np.array(W), WIN


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=5)
    ap.add_argument('--k', type=int, default=4)
    ap.add_argument('--K', type=int, default=5)
    ap.add_argument('--target-edges', type=int, default=None)
    ap.add_argument('--greedy-exact', action='store_true')
    ap.add_argument('--radius', type=int, default=3, help='oracle radius (cache entries of that radius)')
    a = ap.parse_args()
    A = Automaton(a.L, a.k, a.K)
    O = Oracle(a.radius)
    U, V, W, WIN = all_candidates(A)
    unsat = {x for ws in WIN for x in ws if O.status(x) == 'UNSAT'}
    blockers = [frozenset(x for x in ws if x in unsat) for ws in WIN]
    print('candidate edges', len(U), 'relevant exclusions', len(unsat), flush=True)

    def allowed_mask(keep):
        return np.array([not (b & keep) for b in blockers])

    keep = set(unsat)
    # inverted index: exclusion -> edges it blocks
    blocked_by = {}
    for i, b in enumerate(blockers):
        for x in b:
            blocked_by.setdefault(x, []).append(i)
    nblock = np.array([len(b) for b in blockers])
    alive = np.array([len(b & keep) for b in blockers])   # number of kept blockers per edge
    mask = alive == 0
    lam, pi, _ = potential_for(A, U[mask], V[mask], W[mask])
    print('full set: mean', lam, flush=True)
    order = sorted(keep, key=lambda x: (len(x[1]), len(set(x[0]))))
    changed = True
    while changed:
        changed = False
        slack = lam.denominator * W - lam.numerator + pi[U] - pi[V]
        for x in order:
            if x not in keep:
                continue
            es = np.array(blocked_by[x])
            newly = es[alive[es] == 1]          # x is their only remaining blocker
            if (slack[newly] >= 0).all():
                keep.discard(x); alive[es] -= 1; changed = True
        mask = alive == 0
        lam2, pi2, _ = potential_for(A, U[mask], V[mask], W[mask])
        assert lam2 == lam, (lam, lam2)
        pi = pi2
        print('kept', len(keep), 'mean', lam, flush=True)
    vb = bound(A, U[mask].astype(np.int64), V[mask].astype(np.int64), W[mask].astype(float))
    print('max vertices', vb, 'max edges', vb - 1, flush=True)
    if a.greedy_exact and a.target_edges is not None and vb - 1 <= a.target_edges:
        # second pass: drop anything whose removal keeps the exact vertex bound
        for x in sorted(keep, key=lambda x: (-len(x[1]), -len(set(x[0])))):
            es = np.array(blocked_by[x]); alive[es] -= 1; tm = alive == 0
            if bound(A, U[tm].astype(np.int64), V[tm].astype(np.int64), W[tm].astype(float)) - 1 <= a.target_edges:
                keep.discard(x)
            else:
                alive[es] += 1
        mask = alive == 0
        vb = bound(A, U[mask].astype(np.int64), V[mask].astype(np.int64), W[mask].astype(float))
        lam, pi, _ = potential_for(A, U[mask], V[mask], W[mask])
        print('after exact greedy: kept', len(keep), 'mean', lam, 'max edges', vb - 1, flush=True)
    if a.target_edges is not None and vb - 1 > a.target_edges:
        # greedy restore by exact bound: add back exclusions until the target holds
        for x in sorted(unsat - keep, key=lambda x: (len(x[1]), len(set(x[0])))):
            keep.add(x); alive[np.array(blocked_by[x])] += 1; mask = alive == 0
            vb = bound(A, U[mask].astype(np.int64), V[mask].astype(np.int64), W[mask].astype(float))
            if vb - 1 <= a.target_edges:
                break
    out = {'L': a.L, 'k': a.k, 'K': a.K, 'radius': a.radius, 'min_mean': str(lam), 'max_vertices': vb,
           'max_edges': vb - 1,
           'exclusions': [{'dirs': list(x[0]), 'alpha': [list(r) for r in x[1]]} for x in sorted(keep)]}
    path = os.path.join(DATA, f'minimal_L{a.L}_k{a.k}_K{a.K}' + (f'_r{a.radius}' if a.radius != 3 else '') + '.json')
    json.dump(out, open(path, 'w'), indent=1)
    print('wrote', path, len(keep), 'exclusions')


if __name__ == '__main__':
    main()
