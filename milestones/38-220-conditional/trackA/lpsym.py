"""Min cycle mean of the K7R34C7W16 product (tab230 = minimal_L8_k7_K7_r3_89_19) under symbol weights.
usage: lpsym.py OUT.jsonl  spec ...   with spec = c0:Delta  (ws(s) = 24 s - Delta [s > c0]),  or 'w:a1,..,a8'"""
import sys, json, time
from fractions import Fraction as Fr
import numpy as np
from lean_automaton import LeanAutomaton, LeanHowardGraph
from lean_minimize import Graph
from fastround import prune_masked
t0 = time.time()
d = json.load(open('../data/minimal_L8_k7_K7_r3_89_19.json'))
keys = {(tuple(e['dirs']), tuple(tuple(x) for x in e['alpha'])) for e in d['exclusions']}
A = LeanAutomaton(8, 7, 7)
G = Graph(A, keys)
print('graph', G.n, G.E, round(time.time() - t0), flush=True)
m = np.ones(G.E, np.uint8)
prune_masked(G.n, G.starts, G.V, m)
print('pruned', int(m.sum()), round(time.time() - t0), flush=True)
sym = G.W.copy()                       # uint8 symbol 1..8
out = sys.argv[1]
for spec in sys.argv[2:]:
    if spec.startswith('w:'):
        ws = [int(x) for x in spec[2:].split(',')]
    else:
        c0, D = map(int, spec.split(':'))
        ws = [24 * s - (D if s > c0 else 0) for s in range(1, 9)]
    tab = np.array([0] + ws, np.uint16)
    W = tab[sym]
    H = LeanHowardGraph(G.n, G.starts, G.V, W, m.copy())
    mu, cyc = H.solve()
    cs = [int(sym[e]) for e in cyc]
    wins = []
    for e in cyc:
        u = int(np.searchsorted(G.starts, e, side='right') - 1); v = int(G.V[e])
        dg = [(u % A.m1) // 8 ** j % 8 + 1 for j in reversed(range(6))] + [v % 8 + 1]
        wins.append([list(A.shapes[v // A.m1]), dg])
    lam = Fr(int(W[cyc].astype(np.int64).sum()), len(cyc))
    r = dict(spec=spec, ws=ws, lam=str(lam), lamf=float(lam), cycle=cs, wins=wins, sec=round(time.time() - t0))
    print(r, flush=True)
    open(out, 'a').write(json.dumps(r) + '\n')
    del H, W
