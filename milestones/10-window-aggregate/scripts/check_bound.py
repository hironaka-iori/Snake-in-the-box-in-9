"""Exact bound of the automaton built from every cached UNSAT window (no minimisation).

    python check_bound.py --L 7 --k 6 --K 7 --avoid ../data/avoid_k6.json

Prints the minimum cycle mean (C Howard), the potential range from Bellman-Ford at that mean,
the potential bound and the exact walk bound (refine_fast.vertex_bound).  This is what the
minimised and certified set can at best reproduce.
"""
import argparse, json, time
from fractions import Fraction as Fr
import numpy as np
from refine import Oracle
from refine_fast import FastAutomaton, prune, bellman_ford, vertex_bound
from howard_fast import min_cycle


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=7)
    ap.add_argument('--k', type=int, default=6)
    ap.add_argument('--K', type=int, default=7)
    ap.add_argument('--radius', type=int, default=3)
    ap.add_argument('--avoid')
    ap.add_argument('--escalate', type=int, default=None)
    a = ap.parse_args()
    t = time.time()
    if a.escalate:
        from refine import TwoLevelOracle
        O = TwoLevelOracle(a.radius, a.escalate)
    else:
        O = Oracle(a.radius)
    if a.avoid:
        for e in json.load(open(a.avoid)):
            O.known[(tuple(e['dirs']), tuple(tuple(x) for x in e['alpha']))] = 'AVOID'
    A = FastAutomaton(a.L, a.k, a.K)
    U, V, W, EXT = A.edges(O)
    m = prune(A.n, U, V); idx = np.nonzero(m)[0]
    mu, cyc = min_cycle(A.n, U[idx], V[idx], W[idx]); cyc = [idx[e] for e in cyc]
    lam = Fr(int(W[cyc].sum()), len(cyc)); P, Q = lam.numerator, lam.denominator
    pi = bellman_ford(A.n, U, V, W, P, Q)
    R = int(pi.max() - pi.min())
    C = P * a.L - Q * (a.L - 1) + R
    B = (9179 * Q + C - 8 * Q) // (P + 35 * Q)
    vb = vertex_bound(A, U, V, W)
    out = {'cached_unsat': sum(1 for s in O.known.values() if s == 'UNSAT'), 'min_mean': str(lam),
           'mean': round(float(lam), 4), 'potential_range': R, 'potential_bound_edges': B,
           'dp_bound_edges': vb - 1, 'seconds': round(time.time() - t)}
    print(json.dumps(out), flush=True)


if __name__ == '__main__':
    main()
