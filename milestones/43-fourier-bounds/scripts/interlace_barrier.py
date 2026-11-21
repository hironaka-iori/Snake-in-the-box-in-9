"""Barrier for 'path-spectrum interlacing': for ANY signing M of Q_n (|M_e|=1 on every edge,
zero diagonal), an induced path P_V forces lambda_k(M) >= lambda_k(P_V) = 2cos(k pi/(V+1)) for all
k <= V (Cauchy interlacing).  M can exclude V only if lambda_k(M) < lambda_k(P_V) for some k.
But for every induced forest F of Q_n, lambda_k(M) >= lambda_k(F) (signing is irrelevant on a forest).
So V can be excluded by NO signing if for every k <= V some induced forest F_k has
lambda_k(F_k) >= 2cos(k pi/(V+1)).  We construct F_k as unions of r pairwise non-adjacent copies of a
small tree (stars K_{1,s}); by the symmetry of forest and path spectra the negative side is the same.
Output: largest V0 such that every V <= V0 is unexcludable (a rigorous ceiling, given the
validated packings, which are re-checked to be induced)."""
import random, math, sys
import numpy as np

def pack_stars(n, s, rng, restarts):
    best = []
    N = 1 << n
    for _ in range(restarts):
        used = set(); blocked = set(); stars = []
        order = list(range(N)); rng.shuffle(order)
        for c in order:
            if c in used or c in blocked: continue
            nb = [c ^ (1 << i) for i in range(n)]
            avail = [u for u in nb if u not in used and u not in blocked]
            if len(avail) < s: continue
            # prefer leaves with few fresh blocked neighbours
            rng.shuffle(avail)
            leaves = avail[:s]
            comp = [c] + leaves
            stars.append(comp)
            for v in comp:
                used.add(v)
                for i in range(n): blocked.add(v ^ (1 << i))
        if len(stars) > len(best): best = stars
    return best

def check_induced(n, stars, s):
    U = {v: idx for idx, comp in enumerate(stars) for v in comp}
    assert len(U) == sum(len(c) for c in stars)
    deg = {}
    for v, idx in U.items():
        for i in range(n):
            u = v ^ (1 << i)
            if u in U:
                assert U[u] == idx
                deg[v] = deg.get(v, 0) + 1
    for comp in stars:
        assert deg[comp[0]] == s and all(deg[l] == 1 for l in comp[1:])
    return True

def ceiling(n, packs):
    # packs: dict s -> r (number of copies of K_{1,s}); s=0 means isolated vertices (independent set 2^(n-1))
    def beta(k):
        b = -1e9
        for s, r in packs.items():
            if r <= 0: continue
            # eigenvalues of K_{1,s}: sqrt(s), 0^(s-1), -sqrt(s); r copies
            ev = sorted([math.sqrt(s)] * r + [0.0] * (r * (s - 1)) + [-math.sqrt(s)] * r, reverse=True) if s > 0 else [0.0] * r
            if k <= len(ev): b = max(b, ev[k - 1])
        return b
    V = 1
    while True:
        V1 = V + 1
        if all(beta(k) >= 2 * math.cos(k * math.pi / (V1 + 1)) - 1e-12 for k in range(1, V1 + 1)):
            V = V1
            if V > 2 ** n: break
        else:
            return V

if __name__ == "__main__":
    rng = random.Random(3)
    for n in (6, 7, 8, 9):
        packs = {0: 2 ** (n - 1)}
        for s in range(1, n + 1):
            st = pack_stars(n, s, rng, restarts=int(sys.argv[1]) if len(sys.argv) > 1 else 30)
            check_induced(n, st, s)
            packs[s] = len(st)
        print(n, 'star packings', packs, 'unexcludable up to V =', ceiling(n, packs), flush=True)
