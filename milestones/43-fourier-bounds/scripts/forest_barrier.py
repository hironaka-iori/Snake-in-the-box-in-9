"""Search for an induced forest F of Q_n that spectrally dominates the path P_V on its positive
side: lambda_k(F) >= 2cos(k pi/(V+1)) for k <= floor(V/2).  If F exists then NO signing of Q_n
(entries +-1 on edges, zero diagonal) can exclude induced paths on V vertices by Cauchy interlacing
(for k > V/2 the independent half-cube gives lambda_k >= 0 >= 2cos(k pi/(V+1)); the negative side is
symmetric).  Simulated annealing; the found forest is re-validated (induced, acyclic) and saved."""
import sys, random, math, json
import numpy as np

def score(n, U, V):
    idx = {v: i for i, v in enumerate(U)}
    A = np.zeros((len(U), len(U)))
    for v, i in idx.items():
        for b in range(n):
            j = idx.get(v ^ (1 << b))
            if j is not None: A[i, j] = 1
    ev = np.linalg.eigvalsh(A)[::-1] if U else np.array([])
    K = V // 2
    k = np.arange(1, K + 1)
    t = 2 * np.cos(k * np.pi / (V + 1))
    lam = np.full(K, -10.0); m = min(K, len(ev)); lam[:m] = ev[:m]
    d = lam - t
    return d.min(), np.sort(d)[:5].sum()

def acyclic_add(n, Uset, v):
    nb = [v ^ (1 << b) for b in range(n) if (v ^ (1 << b)) in Uset]
    if len(nb) <= 1: return True
    # nb must lie in distinct components of Uset
    seen = {}
    for s in nb:
        if s in seen: return False
        comp = {s}; stack = [s]
        while stack:
            x = stack.pop()
            for b in range(n):
                y = x ^ (1 << b)
                if y in Uset and y not in comp:
                    comp.add(y); stack.append(y)
        for y in nb:
            if y in comp and y != s: return False
        for y in comp: seen[y] = 1
    return True

def is_forest(n, U):
    Uset = set(U); E = sum(1 for v in U for b in range(n) if (v ^ (1 << b)) in Uset) // 2
    # components
    seen = set(); c = 0
    for s in U:
        if s in seen: continue
        c += 1; stack = [s]; seen.add(s)
        while stack:
            x = stack.pop()
            for b in range(n):
                y = x ^ (1 << b)
                if y in Uset and y not in seen: seen.add(y); stack.append(y)
    return E == len(U) - c

def anneal(n, V, iters, seed, T0=0.05):
    rng = random.Random(seed); N = 1 << n
    Uset = set(); U = []
    cur = score(n, U, V); best = (cur, list(U))
    for it in range(iters):
        T = T0 * (1 - it / iters) + 1e-4
        v = rng.randrange(N)
        if v in Uset:
            Uset.remove(v)
        else:
            if not acyclic_add(n, Uset, v): continue
            Uset.add(v)
        new = score(n, sorted(Uset), V)
        if new >= cur or rng.random() < math.exp((new[0] - cur[0] + 0.2 * (new[1] - cur[1])) / T):
            cur = new
            if cur > best[0]: best = (cur, sorted(Uset))
        else:
            if v in Uset: Uset.remove(v)
            else: Uset.add(v)
        if cur[0] >= 0: break
    return best

if __name__ == "__main__":
    n = int(sys.argv[1]); V = int(sys.argv[2]); iters = int(sys.argv[3]); seeds = int(sys.argv[4])
    for sd in range(seeds):
        (sc, sc5), U = anneal(n, V, iters, sd)
        ok = is_forest(n, U)
        print(f"n={n} V={V} seed={sd} |F|={len(U)} min margin={sc:.4f} forest={ok}", flush=True)
        if sc >= 0 and ok:
            json.dump({"n": n, "V": V, "forest": U}, open(f"../data/forest_n{n}_V{V}.json", "w"))
            break
