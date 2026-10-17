"""Exact bound from the direction-aware automaton, using only listed exclusions.

The forbidden windows are read from a certificate index (each entry must carry
`drat_trim_verified: true`).  The automaton is rebuilt from scratch; nothing
from the oracle cache is used.  The script reports

  * the minimum cycle mean, with an integer potential checked edge by edge
    (q*w - p + pi[u] - pi[v] >= 0 on every allowed edge), and
  * the exact largest vertex count v such that some allowed count sequence
    has T <= 9214 - 35 v, where T includes endpoint counts >= 4.

  python direction_bound.py --index ../data/direction_certificates.json --L 7 --k 5 --K 5
"""
import argparse, json, os
from fractions import Fraction as Fr
import numpy as np
from refine import Automaton, canon, key, prune, howard, exact_check

HERE = os.path.dirname(os.path.abspath(__file__))


class Listed:
    def __init__(self, keys):
        self.keys = set(keys)

    def status(self, k):
        return 'UNSAT' if k in self.keys else None


def load_index(path):
    data = json.load(open(path))
    keys = []
    for c in data['cases']:
        assert c['drat_trim_verified'], c['case']
        keys.append((tuple(c['dirs']), tuple(tuple(a) for a in c['alpha'])))
    return keys


def bound(A, U, V, W, vmax=260):
    """Largest v with a walk realising T <= 9214 - 35v.

    The first automaton state is reached after t0 = L-1 internal vertices, when
    all L stored directions are real.  The t0-(k-1) earliest internal counts are
    only bounded below by 1; endpoint counts are at least 4 each.
    """
    t0 = A.L - 1
    pre = t0 - (A.k - 1)
    init = np.full(A.n, np.inf)
    for (c, a), s in A.sid.items():
        init[s] = sum(a)
    best = None
    dp = init.copy()
    steps = 0
    for v in range(t0 + 2, vmax + 1):
        n = v - 2
        while steps < n - t0:
            new = np.full(A.n, np.inf)
            np.minimum.at(new, V, dp[U] + W)
            dp = new; steps += 1
        T = 8 + pre + dp.min()
        if T <= 9214 - 35 * v:
            best = v
    return best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--index', required=True)
    ap.add_argument('--L', type=int, default=7)
    ap.add_argument('--k', type=int, default=5)
    ap.add_argument('--K', type=int, default=5)
    ap.add_argument('--out')
    a = ap.parse_args()
    keys = load_index(a.index)
    A = Automaton(a.L, a.k, a.K)
    U, V, W, _ = A.edges(Listed(keys))
    m = prune(A.n, U, V)
    idx = np.nonzero(m)[0]
    mu, cyc = howard(A.n, U[idx], V[idx], W[idx])
    cyc = [idx[e] for e in cyc]
    exact = Fr(int(W[cyc].sum()), len(cyc))
    pi = exact_check(A.n, U, V, W, exact.numerator, exact.denominator)
    assert pi is not None
    slack = exact.denominator * W - exact.numerator + pi[U] - pi[V]
    assert (slack >= 0).all()          # every allowed edge, pruned or not
    vbest = bound(A, U.astype(np.int64), V.astype(np.int64), W.astype(float))
    out = {'L': a.L, 'k': a.k, 'K': a.K, 'listed_exclusions': len(keys), 'states': A.n,
           'edges': int(len(U)), 'min_mean': str(exact), 'cycle': [int(x) for x in W[cyc]],
           'potential_checked_on_every_edge': True, 'potential_range': int(pi.max() - pi.min()),
           'max_vertices': vbest, 'max_edges': vbest - 1}
    print(json.dumps(out))
    if a.out:
        json.dump(out, open(a.out, 'w'), indent=1)


if __name__ == '__main__':
    main()
