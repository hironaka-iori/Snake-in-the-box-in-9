"""Rigorous (solver-side) lower side of k6 + w_3 with 5-window charges: minimum cycle mean of the
proved T5 lower bounds (threshold UNSATs, DP floor over sub-windows) on the live k6 automaton, and
the same on the k5 automaton edges (no 6-window exclusions) for comparison.  Writes data/evallo.json."""
import json
from fractions import Fraction as Fr
from k6w3lib import *
from ceil import setup

G, P, O, sub = setup()
lb, ub = arrays5(G, O, sub)
b5, b6 = masks(G, P)
out = {}
for name, keep in (('k6', ~b5[G['K5']] & ~b6[G['K6']]), ('k5_only', ~b5[G['K5']])):
    idx = live(G, keep)
    w = lb[G['K5'][idx]]
    _, cyc = howard(G['n6'], G['U'][idx], G['V'][idx], w)
    lam = Fr(int(w[cyc].sum()), len(cyc))
    out[name] = dict(lam=str(lam), mu=float(lam) / 5, m_approx=mbound(float(lam) / 5), len=len(cyc),
                     untested=sum(1 for e in cyc if G['keys5'][G['K5'][idx[e]]] not in O.st))
print(json.dumps(out, indent=1))
json.dump(out, open(os.path.join(DATA, 'evallo.json'), 'w'), indent=1)
