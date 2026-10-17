"""Minimum mean singleton count over bi-infinite internal sequences avoiding
forbidden windows (length <= 3), via Karp's minimum mean cycle on the graph
whose vertices are ordered pairs and edges are allowed triples. Values >= K
are represented by K (a conservative lower bound)."""
import itertools, math
from fractions import Fraction
K = 9
BASE = {(1,1),(1,2),(2,1),(1,3),(3,1)}
def allowed(t, forb3):
    a, b, c = t
    return (a,b) not in BASE and (b,c) not in BASE and t not in forb3
def min_mean(forb3):
    nodes = [p for p in itertools.product(range(1, K+1), repeat=2) if p not in BASE]
    idx = {p: i for i, p in enumerate(nodes)}
    edges = [(idx[(a,b)], idx[(b,c)], c) for a, b, c in itertools.product(range(1, K+1), repeat=3) if allowed((a,b,c), forb3)]
    n = len(nodes); INF = math.inf
    best = INF; arg = None
    # Karp with a virtual source connected to every node
    D = [[INF]*n for _ in range(n+1)]
    for v in range(n): D[0][v] = 0
    for k in range(1, n+1):
        Dk, Dp = D[k], D[k-1]
        for u, v, w in edges:
            if Dp[u] + w < Dk[v]: Dk[v] = Dp[u] + w
    for v in range(n):
        if D[n][v] == INF: continue
        worst = max(Fraction(D[n][v] - D[k][v], n - k) for k in range(n) if D[k][v] < INF)
        if worst < best: best = worst
    return best
def cycle_witness(forb3, target):
    # brute force short cycles achieving target mean
    for L in range(1, 9):
        for seq in itertools.product(range(1, K+1), repeat=L):
            s = seq * 3
            if all(allowed(s[i:i+3], forb3) for i in range(L)) and Fraction(sum(seq), L) == target:
                return seq
def edge_bound(c):
    # E>=0: 2T <= 18428 - 70 v ; T >= c v  (ignoring O(1) endpoint terms)
    return math.floor(Fraction(18428) / (70 + 2*c)) - 1
if __name__ == '__main__':
    sym = lambda ps: set(ps) | {p[::-1] for p in ps}
    scen = [('proved: no (1,1),(1,2),(1,3), no (2,2,2)', sym({(2,2,2)}))]
    scen.append(('+ (2,2,3)', sym({(2,2,2),(2,2,3)})))
    for name, f in scen:
        c = min_mean(f); w = cycle_witness(f, c)
        print(f'{name:55s} min mean={c} ({float(c):.3f}) witness cycle={w} edge bound~{edge_bound(c)}')
    for c in [Fraction(5,2), Fraction(8,3), Fraction(3), Fraction(4), Fraction(5), Fraction(6), Fraction(87,10)]:
        print(f'  if mean alpha >= {str(c):5s}: edges <= ~{edge_bound(c)}')
