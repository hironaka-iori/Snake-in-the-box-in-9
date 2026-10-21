"""Pointwise minimum of w_k(x) = sum_{k-subcubes Q containing x} 1/|Q cap S| over
local snake configurations around an internal vertex x (weighted MaxSAT).

Model: ball B(x,k) with x = 0 and path neighbours e0, e1 (by symmetry).
  * x in S with exactly the neighbours e0, e1 in S;
  * every u in S with |u| <= k-1 has 1 or 2 S-neighbours (all neighbours lie in
    the ball); every u in S with |u| = k has at most 2 S-neighbours in the ball;
  * at most two u with |u| <= k-1 have degree 1 (a snake has two endpoints);
  * the selected set induces no cycle (lazy cuts).
Optionally also with a second centre: 'pair' mode requires the configuration to
be valid around e0 as well (ball of radius k around 0 only, so only the
constraints that live inside the ball are used).
Objective: minimise sum_Q 1/c_Q, encoded as maximising
    sum_Q sum_{j>=2} W/(j(j-1)) [c_Q >= j],  W = 840.
"""
import sys
from itertools import combinations
from pysat.formula import WCNF, IDPool
from pysat.card import CardEnc, EncType
from pysat.examples.rc2 import RC2
from fractions import Fraction as F

n = 9
W = 840


def pc(u):
    return bin(u).count('1')


def build(k, extra_cuts):
    ball = [u for u in range(1 << n) if pc(u) <= k]
    pool = IDPool()
    s = {u: pool.id(('s', u)) for u in ball}
    wc = WCNF()
    wc.append([s[0]]); wc.append([s[1]]); wc.append([s[2]])
    for i in range(2, n):
        wc.append([-s[1 << i]])
    deg1 = []
    for u in ball:
        if u == 0:
            continue
        nb = [u ^ (1 << i) for i in range(n) if pc(u ^ (1 << i)) <= k]
        lits = [s[w] for w in nb]
        # at most 2 neighbours if selected
        for cl in CardEnc.atmost(lits, bound=2, vpool=pool, encoding=EncType.seqcounter).clauses:
            wc.append(cl + [-s[u]])
        if pc(u) <= k - 1:
            wc.append([-s[u]] + lits)  # at least one neighbour
            # d1 <-> selected and exactly one neighbour (only need d1 <- ...)
            d = pool.id(('d1', u)); deg1.append(d)
            # if selected and at most one neighbour, then d
            for a in range(len(lits)):
                for b in range(a + 1, len(lits)):
                    pass
            # selected & not(at least 2 nbrs) -> d : encode via pairs: s & (no pair both) -> d
            # equivalently: -s or d or OR over pairs (both) ; use aux p_ab
            pair_lits = []
            for a, b in combinations(range(len(lits)), 2):
                p = pool.id(('p', u, a, b)); pair_lits.append(p)
                wc.append([-p, lits[a]]); wc.append([-p, lits[b]])
            wc.append([-s[u], d] + pair_lits)
    for cl in CardEnc.atmost(deg1, bound=2, vpool=pool, encoding=EncType.seqcounter).clauses:
        wc.append(cl)
    for cyc in extra_cuts:
        wc.append([-s[u] for u in cyc])
    # objective
    for dirs in combinations(range(n), k):
        pts = [0]
        for d in dirs:
            pts += [p | 1 << d for p in pts]
        others = [s[p] for p in pts if p != 0]
        for j in range(2, (1 << k) + 1):
            t = pool.id(('t', dirs, j))
            enc = CardEnc.atleast(others, bound=j - 1, vpool=pool, encoding=EncType.seqcounter)
            for cl in enc.clauses:
                wc.append(cl + [-t])
            wc.append([t], weight=(W * 1) // (j * (j - 1)))
    return ball, s, wc


def cycles(sel):
    sel = set(sel)
    adj = {u: [u ^ (1 << i) for i in range(n) if u ^ (1 << i) in sel] for u in sel}
    seen, out = set(), []
    for u in sel:
        if u in seen:
            continue
        comp, stack = [], [u]
        seen.add(u)
        while stack:
            a = stack.pop(); comp.append(a)
            for b in adj[a]:
                if b not in seen:
                    seen.add(b); stack.append(b)
        if all(len(adj[a]) == 2 for a in comp):
            out.append(comp)
    return out


def wk(sel, k):
    sel = set(sel)
    tot = F(0)
    for dirs in combinations(range(n), k):
        pts = [0]
        for d in dirs:
            pts += [p | 1 << d for p in pts]
        tot += F(1, sum(1 for p in pts if p in sel))
    return tot


def solve(k):
    cuts = []
    while True:
        ball, s, wc = build(k, cuts)
        with RC2(wc, solver='g4') as rc:
            m = rc.compute()
        sel = [u for u in ball if m[s[u] - 1] > 0]
        cyc = cycles(sel)
        if not cyc:
            return wk(sel, k), sel, len(cuts)
        cuts.extend(cyc)


if __name__ == '__main__':
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    val, sel, nc = solve(k)
    print('k', k, 'min w_k at an internal vertex =', val, '=', float(val), 'cuts', nc)
    print('selected (ball radius %d):' % k, len(sel), sorted(sel))
