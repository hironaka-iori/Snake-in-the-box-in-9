"""Automaton mean with edge weight s + T(window3)/3, T = lower bound on share(x_{i-2})+share(x_{i-1})+share(x_i)
taken from the 3-centre table (keyed by the automaton's own canonical window key) or, when missing,
max(pair(a,b)+single(c), single(a)+pair(b,c)).  usage: automaton3.py lo|hi [out.json]"""
import sys, json
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
import numpy as np
from automaton import load
import os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../10-window-aggregate/scripts'))
from refine import howard

mode = sys.argv[1]
spec = json.load(open(f'spec_pair_{mode}.json'))
single = {int(k): Fr(v) for k, v in spec['single'].items()}
pair = {}
for k, v in spec['pair'].items():
    a, b = map(int, k.split(',')); pair[(a, b)] = pair[(b, a)] = Fr(v)
def pb(a, b): return pair.get((a, b), single[a] + single[b])
tri = {}
for l in open('windows_results.jsonl'):
    r = json.loads(l)
    if len(r['dirs']) != 4 or r['status'] == 'UNSAT_MODEL': continue
    al = tuple((6, 21) if s == '6+' else (int(s), int(s)) for s in r['alpha_req'].split(','))
    M = r['M']
    v = Fr(r['min_lower'], 2 * M) if mode == 'lo' else min(Fr(r['witness_share'], 2 * M), Fr(r['rat_total']))
    if r['witness_share'] > 2 * M * 3 + 1: continue   # stale entries from the buggy first run
    tri[(tuple(r['dirs']), al)] = v
d = load()
D = 2 * 5040 * 11 * 3
W, U = d['W'], d['U']
w = np.zeros(len(W), dtype=np.int64); hits = 0
cache = {}
for e in range(len(W)):
    a = d['inv'][int(U[e])][1]; s = int(W[e]); p2, p1 = a[-2], a[-1]
    k3 = d['WIN'][e][1]
    key = (k3, p2, p1, s)
    if key not in cache:
        fb = max(pb(p2, p1) + single[s], single[p2] + pb(p1, s))
        t = tri.get((tuple(k3[0]), tuple(tuple(x) for x in k3[1])))
        val = fb if t is None else max(t, fb) if mode == 'lo' else t
        cache[key] = (s + val / 3, t is not None)
    v, h = cache[key]; hits += h
    assert (v * D).denominator == 1
    w[e] = int(v * D)
mu, cyc = howard(d['n'], d['U'], d['V'], w)
lam = Fr(int(w[cyc].sum()), len(cyc) * D)
out = {'mode': mode, 'triples_in_table': len(tri), 'edges_using_table': int(hits), 'mean': str(lam), 'meanf': float(lam),
       'v_le': 9214 / (35 + float(lam)), 'cycle_syms': [int(W[e]) for e in cyc],
       'cycle_tri_keys': [[d['WIN'][e][1][0], d['WIN'][e][1][1], tuple(d['WIN'][e][1][0]) in [k[0] for k in tri] and (tuple(d['WIN'][e][1][0]), tuple(tuple(x) for x in d['WIN'][e][1][1])) in tri] for e in cyc]}
print(json.dumps({k: v for k, v in out.items() if k != 'cycle_tri_keys'}))
for k in out['cycle_tri_keys']: print('  ', k)
if len(sys.argv) > 2: json.dump(out, open(sys.argv[2], 'w'), default=list)
