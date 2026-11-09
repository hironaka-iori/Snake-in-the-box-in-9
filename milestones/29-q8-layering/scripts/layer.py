"""Layering bounds for snakes in Q_N from forest data in Q_{N-1} (one cut) or Q_{N-2} (two cuts).

One cut.  A snake with m edges (v = m+1 vertices) using direction i exactly k times splits into
k+1 pieces that alternate between the two halves.  Half a holds floor(k/2)+1 pieces, half b holds
ceil(k/2).  Every internal piece has >= 3 vertices (a 1-vertex internal piece would have both
path neighbours equal to x+e_i; a 2-vertex internal piece a-b gives a chord a'b' between the
neighbours a' = a+e_i, b' = b+e_i).  So for k even, half a has <= 2 short pieces and half b none;
for k odd each half has <= 1 short piece.  Hence

    m + 1 <= G(k) := g3(floor(k/2)+1, t_a) + g3(ceil(k/2), t_b),

with g3(p, t) = max |F| over induced linear forests in Q_{N-1} with exactly p paths, at most t of
them with < 3 vertices (any upper bound for it may be used, e.g. g(p) with <= p paths).  Some
direction has k <= floor(m/N), and G is evaluated as a max over k <= floor(m/N).

Two cuts.  For two directions with k_i + k_j = K <= floor(2m/N), the K+1 pieces walk on the
4-cycle of quarters (Q_{N-2} each), alternating between the classes {00,11} and {01,10}:
    m + 1 <= max over p00+p11 = floor(K/2)+1, p01+p10 = ceil(K/2) of sum_q g(p_q).
"""
import json, sys


def load(path):
    out = {}
    for l in open(path):
        r = json.loads(l)
        out[r['c']] = r
    return out


def G1(k, g3):
    pa, pb = k // 2 + 1, (k + 1) // 2
    ta, tb = (2, 0) if k % 2 == 0 else (1, 1)
    return g3(pa, ta) + (g3(pb, tb) if pb > 0 else 0)


def bound1(N, g3, mmax=None):
    mmax = mmax or (1 << N)
    best = None
    for m in range(1, mmax):
        K = m // N
        if max(G1(k, g3) for k in range(K + 1)) >= m + 1:
            best = m
    return best


def G2(K, g):
    pe, po = K // 2 + 1, (K + 1) // 2
    be = max(g(a) + g(pe - a) for a in range(pe + 1))
    bo = max(g(a) + g(po - a) for a in range(po + 1))
    return be + bo


def bound2(N, g, mmax=None):
    mmax = mmax or (1 << N)
    best = None
    for m in range(1, mmax):
        K = (2 * m) // N
        if max(G2(k, g) for k in range(K + 1)) >= m + 1:
            best = m
    return best


def table_funcs(tab, half):
    """g_le(p), g_eq(p) and g3(p,t) from an exact table; beyond the table use Huang (2^(n-1))."""
    def gle(p):
        if p <= 0:
            return 0
        r = tab.get(p)
        return r['g_le'] if r else half

    def g3(p, t):
        if p <= 0:
            return 0
        r = tab.get(p)
        if not r:
            return half
        return r.get('g3_short%d' % t, r['g_le'])

    def geq(p):
        if p <= 0:
            return 0
        r = tab.get(p)
        return r.get('g_eq', r['g_le']) if r else half
    return gle, geq, g3


if __name__ == '__main__':
    for n in (4, 5, 6):
        tab = load('../data/g%d.jsonl' % n)
        gle, geq, g3 = table_funcs(tab, 1 << (n - 1))
        N = n + 1
        b_le = bound1(N, lambda p, t: gle(p))
        b_eq = bound1(N, lambda p, t: geq(p))
        b_3 = bound1(N, g3)
        print('N=%d (halves Q%d): one cut  m <= %d (<=c paths), %d (exact c), %d (exact c, short pieces)'
              % (N, n, b_le, b_eq, b_3))
        if n <= 5:
            print('N=%d (quarters Q%d): two cuts m <= %d' % (n + 2, n, bound2(n + 2, gle)))
