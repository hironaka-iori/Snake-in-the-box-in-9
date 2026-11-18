"""Min cycle mean of the K7R34C7W16 product under weights 168 * symbol + X(shape of the edge's 7-centre window).
usage: lpshape.py LADDER.jsonl OUT.jsonl [cap ...]   (X(s) = min(cap, proved level of s), default caps: 30 and none)"""
import sys, json, time
from fractions import Fraction as Fr
import numpy as np
from lean_automaton import LeanAutomaton, LeanHowardGraph
from lean_minimize import Graph
from fastround import prune_masked
t0 = time.time()
lad = {}
for l in open(sys.argv[1]):
    r = json.loads(l); lad[tuple(r['dirs'])] = max(30, r['lb'] - 1 if r['lb'] > 31 else 30)   # ladder level T means share >= T
d = json.load(open('../data/minimal_L8_k7_K7_r3_89_19.json'))
keys = {(tuple(e['dirs']), tuple(tuple(x) for x in e['alpha'])) for e in d['exclusions']}
A = LeanAutomaton(8, 7, 7)
G = Graph(A, keys)
m = np.ones(G.E, np.uint8)
prune_masked(G.n, G.starts, G.V, m)
sym = G.W.copy()
shp = (G.V // A.m1).astype(np.int16)
print('graph', G.E, round(time.time() - t0), flush=True)
caps = [int(x) for x in sys.argv[3:]] or [30, 10 ** 6]
for cap in caps:
    X = np.array([min(cap, lad.get(s, 30)) for s in A.shapes], np.uint16)
    W = (168 * sym.astype(np.uint16) + X[shp]).astype(np.uint16)
    H = LeanHowardGraph(G.n, G.starts, G.V, W, m.copy())
    mu, cyc = H.solve()
    lam = Fr(int(W[cyc].astype(np.int64).sum()), len(cyc))
    wins = []
    for e in cyc:
        u = int(np.searchsorted(G.starts, e, side='right') - 1); v = int(G.V[e])
        dg = [(u % A.m1) // 8 ** j % 8 + 1 for j in reversed(range(6))] + [v % 8 + 1]
        wins.append([list(A.shapes[v // A.m1]), dg, int(X[v // A.m1])])
    r = dict(cap=cap, lam=str(lam), per_vertex=float(lam) / 7, cycle=[int(sym[e]) for e in cyc], wins=wins,
             sec=round(time.time() - t0))
    print({k: v for k, v in r.items() if k != 'wins'}, flush=True)
    open(sys.argv[2], 'a').write(json.dumps(r) + '\n')
    del H, W
