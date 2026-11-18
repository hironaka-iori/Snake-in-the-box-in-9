"""Shape automaton: states = canonical 8-direction induced-path windows (7 centres); edge s -> t
when t = canon(s[1:] + [d]).  Weight of a state = a per-shape lower bound Y(s) on the 7-window
combined weight.  Min cycle mean (Karp) gives the uniform per-window average along any snake."""
import json, sys, itertools
from fractions import Fraction as F

def canon(ds):
    m = {}; return tuple(m.setdefault(d, len(m)) for d in ds)

def induced(ds):
    v = [0]
    for d in ds: v.append(v[-1] ^ 1 << d)
    if len(set(v)) != len(v): return False
    for i in range(len(v)):
        for j in range(i + 2, len(v)):
            if bin(v[i] ^ v[j]).count('1') == 1: return False
    return True

def shapes(L=8):
    out = []
    def rec(p, k):
        if len(p) == L:
            out.append(tuple(p)); return
        for d in range(k + 1):
            if p and d == p[-1]: continue
            q = p + [d]
            if induced(q): rec(q, max(k, d + 1) if d == k else k)
    rec([0], 1)
    return out

def graph(S):
    Sset = set(S); E = {s: [] for s in S}
    for s in S:
        k = max(s) + 1
        for d in range(min(k + 1, 9)):
            t = canon(list(s[1:]) + [d])
            if t in Sset and t not in E[s]: E[s].append(t)
    return E

def min_cycle_mean(E, w):
    """Karp on the strongly connected graph of states with finite weight; weight on states."""
    V = [s for s in E if w.get(s) is not None]
    idx = {s: i for i, s in enumerate(V)}; n = len(V)
    INF = float('inf')
    D = [[INF] * n for _ in range(n + 1)]
    for i in range(n): D[0][i] = 0
    pred = {}
    for k in range(1, n + 1):
        for s in V:
            ds = D[k - 1][idx[s]]
            if ds == INF: continue
            for t in E[s]:
                if t in idx:
                    j = idx[t]; val = ds + w[t]
                    if val < D[k][j]: D[k][j] = val
    best = INF
    for j in range(n):
        if D[n][j] == INF: continue
        mx = max(F(D[n][j] - D[k][j], n - k) for k in range(n) if D[k][j] != INF)
        best = min(best, mx)
    return best

if __name__ == '__main__':
    S = shapes(); print('shapes', len(S))
    E = graph(S); print('edges', sum(len(v) for v in E.values()))
    real = json.load(open('data/real_shape_min.json'))
    w = {s: real.get(','.join(map(str, s)), [None])[0] for s in S}
    print('shapes with a real witness', sum(1 for s in S if w[s] is not None))
    mu = min_cycle_mean(E, w)
    print('min cycle mean of real per-shape minima (only real shapes):', mu, float(mu))
