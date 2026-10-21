"""Subcube census inequalities  sum_{x in S} w_k(x) = N_k - E_k  <=  N_k.

For a vertex set S of Q_n and a subcube dimension k let
    N_k   = C(n,k) 2^(n-k)                        (number of k-subcubes),
    E_k   = number of k-subcubes disjoint from S  (>= 0, the only global input),
    w_k(x)= sum over k-subcubes Q containing x of 1/|Q cap S|.
Then sum_x w_k(x) = N_k - E_k exactly.  k = 2 is the repository identity
T + 2 s0 = 9214 - 35 v (with 2 w_2 - alpha = 36 - n3(x)/3).

A local method that proves mean(w_k) >= mu_k gives v <= N_k / mu_k.  On an
actual set S the best such mu_k is mean_S(w_k) (S itself satisfies every local
constraint), so  floor_k(S) = N_k / mean_S(w_k) = |S| N_k / (N_k - E_k)  is the
best bound any local w_k-method can prove when S is locally snake-like
(the adversaries) -- and the slack E_k/N_k measures how much the global
inequality wastes on real snakes.
Usage: python3 subcube_census.py [kmax]
"""
import json, sys
from itertools import combinations
from fractions import Fraction as F
from math import comb

n = 9


def subcubes(k):
    for dirs in combinations(range(n), k):
        mask = sum(1 << d for d in dirs)
        free = [d for d in range(n) if not mask >> d & 1]
        for bits in range(1 << (n - k)):
            base = 0
            for t, d in enumerate(free):
                if bits >> t & 1:
                    base |= 1 << d
            yield base, dirs


def census(S, k):
    S = set(S)
    w = {x: F(0) for x in S}
    empty = 0
    hist = {}
    for base, dirs in subcubes(k):
        pts = [base]
        for d in dirs:
            pts += [p | 1 << d for p in pts]
        inS = [p for p in pts if p in S]
        c = len(inS)
        hist[c] = hist.get(c, 0) + 1
        if c == 0:
            empty += 1
        else:
            for p in inS:
                w[p] += F(1, c)
    return empty, w, dict(sorted(hist.items()))


if __name__ == '__main__':
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    import os; root = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..') + '/'
    bank = json.load(open(root + 'work/bank9.json'))
    sets = [('bank%d' % i, bank[i]['vertex_sequence']) for i in (0, 45, 100)]
    for nm in ('adversary208', 'adversary224'):
        sets.append((nm, json.load(open(root + 'milestones/11-local-ceiling/data/%s.json' % nm))['S']))
    for nm, S in sets:
        v = len(S)
        for k in range(2, kmax + 1):
            Nk = comb(n, k) * 2 ** (n - k)
            e, w, h = census(S, k)
            internal = [w[x] for x in (S[1:-1] if nm.startswith('bank') else S)]
            mean = sum(w.values()) / v
            print('%-13s v=%d k=%d N_k=%d empty=%d (%.1f%%) mean w=%.4f min w=%.4f floor=N_k/mean=%.1f hist=%s'
                  % (nm, v, k, Nk, e, 100 * e / Nk, float(mean), float(min(internal)), float(Nk / mean), h), flush=True)
