"""The k6 + w_3 minimum cycle on the FULL product automaton that the Lean k6 check enumerates
(../../23-k6-lean/scripts/gen_lean_automaton6.py: 34 seven-direction shapes x 6^5 counts = 264,384 states,
step = direction d < 9 and new count s; a step is allowed unless a window of 3..7 directions ending at the
new vertex is excluded, both orientations).

Exclusions: every plain-UNSAT key known to the loop (k6loop.Plain merged statuses, ../k6_w3, this run),
restricted to lumped counts ((s,s), s <= 5, or (6,21)) and 2..6 counts.  Keys with other count ranges are
left out (conservative: fewer exclusions can only lower the minimum).
Weights: the 6-window charge lower bound W6 of the step's window (directions ds[1:8], counts t0..t4,s),
    W6 = max(lb6, lb5(left 5) + s(last alpha), s(first alpha) + lb5(right 5)),
lb5 = max(proved threshold, sub-window DP floor), exactly as k6w3loop.Tables, but on dense tables over
every count tuple.  Ceiling: the same with ub6 (SAT witnesses of the 6-window), witnessed steps only.

usage: fullprod.py [--exact]    writes data/fullprod.json
"""
import sys, os, json, time, itertools
ME = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, ME)
sys.path.insert(0, os.path.join(ME, '..', '..', '23-k6-lean', 'scripts'))
from fractions import Fraction as Fr
import numpy as np
import k6w3loop as L
from k6w3loop import *
import gen_lean_automaton6 as GA
canon = GA.canon
prune = k6loop.prune

LUMP = {i: (i, i) for i in range(1, 6)}; LUMP[6] = (6, 21)


def sym(a):
    a = tuple(a)
    if a[0] == a[1] and 1 <= a[0] <= 5:
        return a[0]
    if a == (6, 21):
        return 6
    return None


def grid(n):
    """All count tuples over 1..6 of length n, in cnt_idx order."""
    return list(itertools.product(range(1, 7), repeat=n))


def main():
    t0 = time.time()
    G, P, O, sub = setup()
    keys = set()
    skipped = 0
    for k, st in P.st.items():
        if st != 'UNSAT' or not (2 <= len(k[1]) <= 6):
            continue
        s = tuple(sym(a) for a in k[1])
        if None in s:
            skipped += 1; continue
        keys.add((tuple(k[0]), s))
    keys = sorted(keys, key=lambda k: (len(k[0]), k))
    wshapes, widx, forb = GA.build_tables(keys)
    shp = GA.shapes7()
    print(f'{len(keys)} exclusion keys ({sum(len(k[1]) == 6 for k in keys)} six-centre; {skipped} non-lumped skipped)', flush=True)
    tr = GA.transitions(shp, widx, forb, len(wshapes))
    print(f'transitions built {time.time()-t0:.0f}s rss {rss_mb():.0f}', flush=True)
    single = {s: sub.single_lb(LUMP[s]) for s in range(1, 7)}
    g5 = grid(5); g6 = np.array(grid(6))
    B = {}

    def lb5_dense(c6):
        if c6 not in B:
            arr = np.empty(len(g5), np.int64)
            for x, t in enumerate(g5):
                k = survey.key(c6, [LUMP[s] for s in t])
                st = O.st.get(k)
                arr[x] = max(sub.floor5(k), st['lb'] if st else 0)
            B[c6] = arr
        return B[c6]
    lb6 = {}; ub6 = {}
    for k, st in O.st.items():
        if len(k[1]) != 6:
            continue
        s = tuple(sym(a) for a in k[1])
        if None in s:
            continue
        for c, t in ((k[0], s), (canon(tuple(reversed(k[0]))), tuple(reversed(s)))):
            x = GA.cnt_idx(t)
            if st['lb']:
                lb6.setdefault(c, {})[x] = max(lb6.get(c, {}).get(x, 0), st['lb'])
            if st['ub'] is not None:
                ub6.setdefault(c, {})[x] = min(ub6.get(c, {}).get(x, INF), st['ub'])
    A = {}; Au = {}
    sF = np.array([single[s] for s in g6[:, 0]]); sL = np.array([single[s] for s in g6[:, 5]])
    iL = np.array([GA.cnt_idx(t) for t in g6[:, :5]]); iR = np.array([GA.cnt_idx(t) for t in g6[:, 1:]])

    def dense(c):
        if c not in A:
            w = np.maximum(lb5_dense(canon(c[0:6]))[iL] + sL, sF + lb5_dense(canon(c[1:7]))[iR])
            for x, v in lb6.get(c, {}).items():
                w[x] = max(w[x], v)
            A[c] = w
            u = np.full(len(g6), INF, np.int64)
            for x, v in ub6.get(c, {}).items():
                u[x] = v
            Au[c] = u
        return A[c], Au[c]
    x = np.arange(GA.NT)
    Us, Vs, Ws, Wu = [], [], [], []
    for i, d, j, ok in tr:
        ds = shp[i] + (d,)
        a, u = dense(canon(ds[1:8]))
        xs = x[ok]
        Us.append(i * GA.NC + xs // 6); Vs.append(j * GA.NC + xs % GA.NC); Ws.append(a[xs]); Wu.append(u[xs])
    U = np.concatenate(Us); V = np.concatenate(Vs); W = np.concatenate(Ws); Wub = np.concatenate(Wu)
    del Us, Vs, Ws, Wu, tr
    n = len(shp) * GA.NC
    print(f'{n} states, {len(U)} allowed transitions; weights {time.time()-t0:.0f}s rss {rss_mb():.0f}', flush=True)
    keep = np.nonzero(prune(n, U, V))[0]
    _, cyc = howard(n, U[keep], V[keep], W[keep])
    cyc = [int(keep[e]) for e in cyc]
    lam = Fr(int(W[cyc].sum()), len(cyc))
    cnt = lambda y: [int(y) // 6 ** k % 6 + 1 for k in range(4, -1, -1)]
    out = dict(graph='full product (Lean k6 check), all known plain exclusions with lumped counts',
               exclusion_keys=len(keys), states=n, allowed_transitions=int(len(U)), live_transitions=int(len(keep)),
               lam6=str(lam), mu=float(lam) / 6, m=mbound(float(lam) / 6), len=len(cyc),
               cycle=[[list(shp[U[e] // GA.NC]), cnt(U[e] % GA.NC), cnt(V[e] % GA.NC)[-1], int(W[e])] for e in cyc])
    print(json.dumps({k: v for k, v in out.items() if k != 'cycle'}), flush=True)
    if '--exact' in sys.argv:
        pi, it = GA.bellman_ford(n, U[keep], V[keep], lam.denominator * W[keep] - lam.numerator, 5000)
        out['exact_potential'] = pi is not None
        out['bf_rounds'] = it
        print('exact potential', pi is not None, it, flush=True)
    wit = keep[Wub[keep] < INF]
    out['ceiling'] = None
    if len(wit):
        m2 = prune(n, U[wit], V[wit]); wit = wit[m2]
        if len(wit):
            _, cc = howard(n, U[wit], V[wit], Wub[wit])
            cc = [int(wit[e]) for e in cc]
            lc = Fr(int(Wub[cc].sum()), len(cc))
            out['ceiling'] = dict(lam6=str(lc), mu=float(lc) / 6, m=mbound(float(lc) / 6), len=len(cc),
                                  witnessed_live_transitions=int(len(wit)))
    print('ceiling', out['ceiling'], flush=True)
    json.dump(out, open(os.path.join(L.DATA, 'fullprod.json'), 'w'), indent=1)


if __name__ == '__main__':
    main()
