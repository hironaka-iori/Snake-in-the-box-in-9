"""Direction-only automaton for the 3-cube charge, and the implied edge bound.

State: canonical shape of the last L transition directions (induced).  Edge: append one
direction; the new L+1 block must be induced.  The edge carries the window of the last k+1
directions (k centres) and weight T(window) = proved lower bound (lb, rigorous) or best witness
(ub, ceiling) of sum_{centres} c from the oracle.  With lambda = min cycle mean of T:

    k * sum_{j=1}^{m-1} c(x_j) >= sum_{windows} T >= lambda (m - k) - R      (R: potential range)
    sum_{x in S} c(x) <= 64512,  c(endpoint) >= 168,  so
    m <= k + (k (64512 - 2*168) + R) / lambda    ~    64512 / (lambda / k) - 1.

usage: shape_aut.py [--k 5] [--L 7]
"""
import argparse, itertools, json, os, sys
from fractions import Fraction as Fr
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', '..', '10-window-aggregate', 'scripts'))
from refine import howard, exact_check
import w3survey as survey
from w3survey import canon, induced, key, FREE

CENSUS = 64512
END = 168


def build(L, k):
    states = sorted({canon(ds) for ds in itertools.product(range(L), repeat=L) if induced(canon(ds))})
    sid = {s: i for i, s in enumerate(states)}
    U, V, KEY = [], [], []
    for s in states:
        for d in range(min(max(s) + 2, 9)):
            ds = s + (d,)
            if not induced(ds):
                continue
            U.append(sid[s]); V.append(sid[canon(ds[1:])])
            KEY.append(key(ds[-(k + 1):], [FREE] * k))
    return len(states), np.array(U), np.array(V), KEY


def bound(lam, k, R=0):
    return k + (k * (CENSUS - 2 * END) + R) / lam


def evaluate(k, L, O, which):
    n, U, V, KEY = build(L, k)
    keys = sorted(set(KEY))
    val = {}
    for kk in keys:
        s = O.get(kk)
        val[kk] = s['lb'] if which == 'lb' else (s['ub'] if s['ub'] is not None else 10 ** 6)
    W = np.array([val[kk] for kk in KEY], np.int64)
    _, cyc = howard(n, U, V, W)
    lam = Fr(int(W[cyc].sum()), len(cyc))
    pi = exact_check(n, U, V, W, lam.numerator, lam.denominator)
    R = int(pi.max() - pi.min()) if pi is not None else None
    return dict(lam=str(lam), per_centre_c=float(lam) / k, per_centre_w3=float(lam) / k / 12,
                m_le=bound(float(lam), k, (R or 0) / lam.denominator), potential_range=R,
                cycle=[list(KEY[e][0]) for e in cyc], states=n, keys=len(keys),
                key_values={str(list(kk[0])): [O.get(kk)['lb'], O.get(kk)['ub']] for kk in keys})


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--k', type=int, default=5)
    ap.add_argument('--L', type=int, default=7)
    a = ap.parse_args()
    O = survey.Oracle()
    out = {w: evaluate(a.k, a.L, O, w) for w in ('lb', 'ub')}
    print(json.dumps(out, indent=1))


if __name__ == '__main__':
    main()
