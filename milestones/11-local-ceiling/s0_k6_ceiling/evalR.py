"""Rigorous ceiling from the data in hand: the minimum cycle of the L7 k6 automaton restricted to edges whose
5-window has a witness (T5 = its share) and whose 6-window was solved SAT (has a witness).  Any such cycle is a
periodic pattern that no k5-share certificates plus k6 plain exclusions can lift.  Also reports the same with
6-window share weights (144 sym + T6 witness)."""
import sys, os, json
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
import numpy as np
from ceilF import build_full, INF
from ceil6 import Oracle6
from refine import howard, prune
G = build_full(); O5 = G['O5']; O6 = Oracle6()
k5, k6 = G['keys5'], G['keys6']
ub5 = np.array([O5.st[k]['ub'] if k in O5.st else INF for k in k5], np.int64)
ex5 = np.array([O5.st[k]['excl'] if k in O5.st else False for k in k5], bool)
ub6 = np.array([O6.st[k]['ub'] if k in O6.st else INF for k in k6], np.int64)
ex6 = np.array([O6.st[k]['excl'] if k in O6.st else False for k in k6], bool)
ki = G['KI'][G['E5']]
print('5-keys with witness', int((ub5 < INF).sum()), 'excluded', int(ex5.sum()), '| 6-keys SAT', int((ub6 < INF).sum()),
      'UNSAT', int(ex6.sum()), 'of', len(k6))
out = {}
for name in ('k5share', 'k6share'):
    keep = (ub5[ki] < INF) & ~ex5[ki] & (ub6[G['K6']] < INF)
    m = prune(G['n6'], G['U6'][keep], G['V6'][keep]); idx = np.nonzero(keep)[0][m]
    if len(idx) == 0:
        print(name, ': no fully witnessed cycle'); out[name] = None; continue
    sym = G['S'][G['E5'][idx]].astype(np.int64)
    w = 120 * sym + ub5[ki[idx]] if name == 'k5share' else 144 * sym + ub6[G['K6'][idx]]
    unit = 120 if name == 'k5share' else 144
    _, cyc = howard(G['n6'], G['U6'][idx], G['V6'][idx], w)
    lam = Fr(int(w[cyc].sum()), len(cyc)); mu = float(lam) / unit
    rec = dict(edges=int(len(idx)), lam=str(lam), mu=round(mu, 5), m_le=round(9171 / (mu + 35), 3),
               syms=[int(x) for x in sym[cyc]], T=[int(x) for x in (w[cyc] - unit * sym[cyc])],
               keys6=[[list(k6[G['K6'][idx[e]]][0]), [a[0] for a in k6[G['K6'][idx[e]]][1]]] for e in cyc])
    print(name, json.dumps(rec)); out[name] = rec
json.dump(out, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'rigorous_ceiling.json'), 'w'), indent=1)
