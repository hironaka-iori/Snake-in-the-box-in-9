"""Automaton mean with edge weight  s + single(s)  or  s + pair(prev,s)/2 (+ conservative fill-ins).
usage: automaton2.py spec.json [out.json]
spec: {"single": {"1": "1/6", ...}, "pair": {"2,2": "5/12", ...}, "mode": "pair"|"single"}
pair values are lower bounds on share(x_i)+share(x_{i+1}) (rational, already divided by 2M);
missing pairs fall back to single(a)+single(b)."""
import sys, json, os
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
import numpy as np
from automaton import load
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../10-window-aggregate/scripts'))
from refine import howard

spec = json.load(open(sys.argv[1]))
single = {int(k): Fr(v) for k, v in spec.get('single', {}).items()}
pair = {}
for k, v in spec.get('pair', {}).items():
    a, b = map(int, k.split(',')); pair[(a, b)] = pair[(b, a)] = Fr(v)
def pb(a, b):
    return pair.get((a, b), single.get(a, Fr(0)) + single.get(b, Fr(0)))
d = load()
D = 2 * 5040 * 11
W = d['W']; U = d['U']
prev = np.array([d['inv'][int(u)][1][-1] for u in U])
if spec.get('mode') == 'pair':
    wf = {(p, s): s + pb(p, s) / 2 for p in range(1, 7) for s in range(1, 7)}
else:
    wf = {(p, s): s + single.get(s, Fr(0)) for p in range(1, 7) for s in range(1, 7)}
for v in wf.values():
    assert (v * D).denominator == 1
w = np.array([int(wf[(int(p), int(s))] * D) for p, s in zip(prev, W)])
mu, cyc = howard(d['n'], d['U'], d['V'], w)
lam = Fr(int(w[cyc].sum()), len(cyc) * D)
syms = [int(W[e]) for e in cyc]
out = {'mean': str(lam), 'meanf': float(lam), 'v_le': 9214 / (35 + float(lam)), 'cycle_syms': syms,
       'cycle_windows': [[[list(k[0]), [list(a) for a in k[1]]] for k in d['WIN'][e]] for e in cyc]}
print(json.dumps({k: v for k, v in out.items() if k != 'cycle_windows'}))
if len(sys.argv) > 2:
    json.dump(out, open(sys.argv[2], 'w'), indent=0)
