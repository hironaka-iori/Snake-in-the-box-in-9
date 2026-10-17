"""Independent exact bound: a path with v vertices has n1 = T, 2*n0 + T = 9214 - 35 v (n0>=0, T == v mod 2).
Alpha sequence a_0..a_{v-1}: a_0,a_{v-1} >= 4 (proved), internal >= 1, forbidden internal windows
(length 2 and 3) as given.  tmin(v) = min sum.  v feasible iff tmin(v) <= 9214-35v (parity adjusted).
Also minimum mean over bi-infinite internal sequences (Karp on the window graph).
Values capped at K; we verify stability by comparing K and K+3."""
import itertools, json, math, sys
from fractions import Fraction

BASE2 = {(1, 1), (1, 2), (2, 1), (1, 3), (3, 1)}

def sym(ps):
    return set(ps) | {tuple(reversed(p)) for p in ps}

def tmin_table(F3, K, vmax, F2=BASE2, endmin=4):
    """returns dict v->min T for v=4..vmax. internal positions 1..v-2"""
    INF = 10 ** 9
    vals = range(1, K + 1)
    res = {}
    # dp over (prev, cur) for internal sequence of length m
    dp = {(None, a): a for a in vals}
    m = 1
    res[3] = endmin * 2 + 1
    while m + 2 <= vmax:
        res[m + 2] = 2 * endmin + min(dp.values())
        nd = {}
        for (p, a), s in dp.items():
            for b in vals:
                if (a, b) in F2:
                    continue
                if p is not None and (p, a, b) in F3:
                    continue
                if s + b < nd.get((a, b), INF):
                    nd[(a, b)] = s + b
        dp = nd
        m += 1
    return res

def edge_bound(F3, K=14, vmax=262, parity=True, F2=BASE2):
    tab = tmin_table(F3, K, vmax, F2)
    best = None
    for v in range(4, vmax + 1):
        cap = 9214 - 35 * v
        t = tab[v]
        if parity and (t - v) % 2:
            t += 1  # T must have parity of v (any larger value is attainable by raising an entry)
        if t <= cap:
            best = v
    return best - 1, tab

def min_mean(F3, K=12, F2=BASE2):
    nodes = [p for p in itertools.product(range(1, K + 1), repeat=2) if p not in F2]
    idx = {p: i for i, p in enumerate(nodes)}
    edges = [(idx[(a, b)], idx[(b, c)], c) for a, b, c in itertools.product(range(1, K + 1), repeat=3)
             if (a, b) not in F2 and (b, c) not in F2 and (a, b, c) not in F3]
    n = len(nodes)
    INF = float('inf')
    D = [[INF] * n for _ in range(n + 1)]
    for i in range(n):
        D[0][i] = 0
    for k in range(1, n + 1):
        Dk, Dp = D[k], D[k - 1]
        for u, w, c in edges:
            if Dp[u] + c < Dk[w]:
                Dk[w] = Dp[u] + c
    best = None
    for i in range(n):
        if D[n][i] == INF:
            continue
        worst = max(Fraction(int(D[n][i] - D[k][i]), n - k) for k in range(n) if D[k][i] < INF)
        if best is None or worst < best:
            best = worst
    return best

def witness_cycle(F3, target, K=12, F2=BASE2, Lmax=8):
    for L in range(1, Lmax + 1):
        for seq in itertools.product(range(1, K + 1), repeat=L):
            if Fraction(sum(seq), L) != target:
                continue
            s = seq * 3
            if all((s[i], s[i + 1]) not in F2 for i in range(2 * L)) and all(tuple(s[i:i + 3]) not in F3 for i in range(L)):
                return seq
    return None

def vbound_from_mean(c):
    return math.floor(Fraction(9214) / (35 + Fraction(c)))

if __name__ == '__main__':
    r3 = json.load(open('/tmp/claude-0/-home-user-Snake-in-the-box-in-9/54df6b79-3551-5be0-97ec-edf141639c5c/scratchpad/ana/patterns_r3_s9.json'))
    st = {}
    for r in r3:
        st.setdefault(tuple(r['alpha']), {})[r['shape']] = r['status']
    excl = sorted(p for p, s in st.items() if all(x == 'INFEASIBLE' for x in s.values()))
    print('radius-3 exclusions in both shapes:', len(excl), excl)
    scen = [('proved (no 11,12,13, no 222)', sym({(2, 2, 2)})),
            ('+223', sym({(2, 2, 2), (2, 2, 3)})),
            ('+all 12 radius-3', sym(excl)),
            ('+all 12 + 233', sym(set(excl) | {(2, 3, 3)})),
            ]
    for name, F in scen:
        for K in (12, 15):
            eb, tab = edge_bound(F, K=K)
            eb0, _ = edge_bound(F, K=K, parity=False)
            print(f'{name:32s} K={K}: edges <= {eb} (no parity: {eb0});  tmin(246)={tab[246]} tmin(245)={tab[245]} tmin(243)={tab[243]} tmin(242)={tab[242]}')
        c = min_mean(F)
        print(f'   asymptotic min mean c={c} ({float(c):.4f}), witness cycle {witness_cycle(F, c)}, v <= {vbound_from_mean(c)}')
