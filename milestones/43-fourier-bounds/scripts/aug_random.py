"""Test: does every snake S in Q_n extend to a 2^(n-1)-vertex set T with
lambda_max(A_s[T]) < sqrt(n)?  (numerical exploration on random snakes).
Also reports the local 'c<=3 packing' augmentation (see README)."""
import sys, random
import numpy as np
from huang_aug import huang, adj_count, greedy

def random_snake(n, rng, tries=200):
    best = []
    for _ in range(tries):
        path = [0]; blocked = {0: 1}
        inS = {0}
        while True:
            v = path[-1]
            cand = []
            for i in range(n):
                u = v ^ (1 << i)
                if u in inS: continue
                # u must have no S-neighbour except v
                if any(((u ^ (1 << j)) in inS) and (u ^ (1 << j)) != v for j in range(n)): continue
                cand.append(u)
            if not cand: break
            u = rng.choice(cand); path.append(u); inS.add(u)
        if len(path) > len(best): best = path
    return best

def packing(n, S):
    """Greedy local Collatz packing: add w with c(w)<=3, cost c/3 per S-neighbour,
    capacity 1 (interior) or 2 (endpoint), I independent. Certified lambda<3 only
    for n=9; numerically re-checked."""
    Sset = set(S); cap = {v: 1.0 for v in S}; cap[S[0]] = cap[S[-1]] = 2.0
    c = adj_count(n, S); I = set()
    for w in sorted(c, key=lambda w: c[w]):
        if c[w] > 3: continue
        if any((w ^ (1 << i)) in I for i in range(n)): continue
        nb = [w ^ (1 << i) for i in range(n) if (w ^ (1 << i)) in Sset]
        if all(cap[u] >= c[w] / 3 - 1e-12 for u in nb):
            for u in nb: cap[u] -= c[w] / 3
            I.add(w)
    return I

if __name__ == "__main__":
    n = int(sys.argv[1]); reps = int(sys.argv[2]); rng = random.Random(7)
    A = huang(n); thr = np.sqrt(n)
    for r in range(reps):
        S = random_snake(n, rng, tries=int(sys.argv[3]) if len(sys.argv) > 3 else 100)
        c = adj_count(n, S)
        best = 0
        for t in range(6):
            ws = list(c); rng.shuffle(ws)
            if t % 2 == 0: ws.sort(key=lambda w: c[w])
            best = max(best, len(greedy(n, A, S, ws, thr)) - len(S))
        P = packing(n, S)
        lam = np.linalg.eigvalsh(A[np.ix_(list(S) + list(P), list(S) + list(P))])[-1]
        print(f"n={n} |S|={len(S)} slack={2**(n-1)-len(S)} greedy|I|={best} packing={len(P)} lam(S+P)={lam:.3f}", flush=True)
