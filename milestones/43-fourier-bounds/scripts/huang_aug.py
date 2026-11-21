"""Augmented Huang bound: for a snake S and I disjoint from S with
lambda_max(A_s[S u I]) < sqrt(n), Huang's interlacing gives |S|+|I| <= 2^(n-1).
Greedy/randomised search for large I on given snakes (numerical exploration)."""
import json, sys, random
import numpy as np

def huang(n):
    A = np.zeros((1, 1))
    for k in range(1, n + 1):
        m = A.shape[0]
        I = np.eye(m)
        A = np.block([[A, I], [I, -A]])
    return A

def adj_count(n, S):
    Sset = set(S)
    return {w: sum(((w ^ (1 << i)) in Sset) for i in range(n)) for w in range(1 << n) if w not in Sset}

def lmax(A, T):
    return np.linalg.eigvalsh(A[np.ix_(T, T)])[-1]

def greedy(n, A, S, order, thr):
    T = list(S)
    for w in order:
        T.append(w)
        if lmax(A, T) >= thr - 1e-9:
            T.pop()
    return T

def run(n, S, tries=20, seed=1):
    A = huang(n); thr = np.sqrt(n)
    c = adj_count(n, S)
    best = None
    rng = random.Random(seed)
    for t in range(tries):
        ws = list(c)
        rng.shuffle(ws)
        ws.sort(key=lambda w: c[w] if t % 2 == 0 else 0)
        T = greedy(n, A, S, ws, thr)
        if best is None or len(T) > len(best):
            best = T
    hist = {}
    for w in c.values():
        hist[w] = hist.get(w, 0) + 1
    return best, hist

if __name__ == "__main__":
    f = sys.argv[1]
    d = json.load(open(f))
    S = d["vertex_sequence"]
    n = max(S).bit_length()
    best, hist = run(n, S, tries=int(sys.argv[2]) if len(sys.argv) > 2 else 10)
    print(f"n={n} |S|={len(S)} Huang cap={2**(n-1)} slack={2**(n-1)-len(S)} best |I|={len(best)-len(S)}")
    print("count histogram of outside vertices c(w):", dict(sorted(hist.items())))
