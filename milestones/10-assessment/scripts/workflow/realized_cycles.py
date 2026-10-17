"""Min-mean cycle in the order-(k-1) de Bruijn graph whose edges are k-windows of internal alpha values
REALIZED in genuine snakes (and their reversals).  Any valid k-window exclusion keeps these windows, so
this mean is a rigorous ceiling for k-window (DP/potential) arguments.  Karp on the sparse graph."""
import json, math, sys
from fractions import Fraction
from verify_real import order_path, alphas
bank = json.load(open('/home/user/Snake-in-the-box-in-9/work/bank9.json'))
seqs = [e['vertex_sequence'] for e in bank]
for f in sys.argv[1:]:
    for r in json.load(open(f)):
        if r.get('selected'): seqs.append(order_path(r['selected']))
        elif r.get('best'): seqs.append(order_path(r['best']['selected']))
A = [alphas(s)[1:-1] for s in seqs]
def mmc(k):
    W = set()
    for a in A:
        for i in range(len(a) - k + 1):
            w = tuple(a[i:i + k]); W.add(w); W.add(w[::-1])
    nodes = sorted({w[:-1] for w in W} | {w[1:] for w in W}); idx = {u: i for i, u in enumerate(nodes)}
    E = [(idx[w[:-1]], idx[w[1:]], w[-1]) for w in W]
    n = len(nodes); INF = float('inf')
    D = [[INF] * n for _ in range(n + 1)]
    for i in range(n): D[0][i] = 0
    for s in range(1, n + 1):
        Dp, Dk = D[s - 1], D[s]
        for u, v, c in E:
            if Dp[u] + c < Dk[v]: Dk[v] = Dp[u] + c
    best = None
    for v in range(n):
        if D[n][v] == INF: continue
        worst = max(Fraction(int(D[n][v] - D[s][v]), n - s) for s in range(n) if D[s][v] < INF)
        if best is None or worst < best: best = worst
    return best, len(W), n
for k in [3, 4, 5, 6]:
    m, nw, nn = mmc(k)
    if m is None:
        print('k=%d: no cycle among %d realized windows' % (k, nw)); continue
    v = math.floor(Fraction(9214) / (35 + m))
    print('k=%d: realized windows %d, min-mean realized cycle %s = %.3f -> k-window DP arguments cannot prove better than %d edges' % (k, nw, m, float(m), v - 1))
