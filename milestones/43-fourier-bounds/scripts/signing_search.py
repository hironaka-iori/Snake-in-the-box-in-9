"""Path-spectrum interlacing over signings of Q_n (numerical exploration).
For a signing M (entries +-1 on cube edges), an induced path on V vertices needs
lambda_k(M) >= 2cos(k pi/(V+1)) and lambda_k(-M) >= 2cos(k pi/(V+1)) for k <= V.
excl(M) = least V violating this; then every snake has <= excl(M)-1 vertices.
Hill climbing on single edge flips, maximizing the violation margin at a target V."""
import sys, random, math
import numpy as np

def edges(n):
    return [(v, v | (1 << i)) for v in range(1 << n) for i in range(n) if not v >> i & 1]

def huang_sign(n):
    # Huang signing: s(v, v+e_i) = (-1)^{sum_{j<i} v_j}
    return [(-1) ** bin(u & ((1 << ((u ^ w).bit_length() - 1)) - 1)).count('1') for (u, w) in edges(n)]

def matrix(n, E, s):
    M = np.zeros((1 << n, 1 << n))
    for (u, w), x in zip(E, s):
        M[u, w] = M[w, u] = x
    return M

def margin(ev_desc, V):
    k = np.arange(1, V + 1)
    t = 2 * np.cos(k * np.pi / (V + 1))
    a = np.max(t - ev_desc[:V])
    b = np.max(t - (-ev_desc[::-1])[:V])
    return max(a, b)

def excl(ev_desc, N):
    for V in range(2, N + 1):
        if margin(ev_desc, V) > 1e-9:
            return V
    return N + 1

if __name__ == "__main__":
    n = int(sys.argv[1]); V = int(sys.argv[2]); iters = int(sys.argv[3]); start = sys.argv[4]
    rng = random.Random(5); E = edges(n); N = 1 << n
    s = huang_sign(n) if start == 'huang' else ([1] * len(E) if start == 'plus' else [rng.choice((1, -1)) for _ in E])
    M = matrix(n, E, s); ev = np.linalg.eigvalsh(M)[::-1]
    assert start != 'huang' or np.allclose(np.abs(ev), math.sqrt(n))
    cur = margin(ev, V); print('start', start, 'excl', excl(ev, N), 'margin@V', round(cur, 4), flush=True)
    best = cur
    for it in range(iters):
        j = rng.randrange(len(E)); u, w = E[j]
        M[u, w] = M[w, u] = -M[u, w]
        ev2 = np.linalg.eigvalsh(M)[::-1]; m2 = margin(ev2, V)
        if m2 >= cur or rng.random() < 0.002:
            cur = m2; ev = ev2
            if cur > best:
                best = cur
        else:
            M[u, w] = M[w, u] = -M[u, w]
        if it % (iters // 10) == 0:
            print(it, 'margin', round(cur, 4), 'best', round(best, 4), 'excl', excl(ev, N), flush=True)
    print('final excl', excl(ev, N), 'best margin', best)
