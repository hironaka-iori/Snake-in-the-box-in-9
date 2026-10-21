"""Rigorous lower side (solver-side): min cycle mean of the L7 k6 automaton with W = 120 sym + T5_lb (proved 5-window
share lower bounds; 0 when none) after removing every 5-window and 6-window proved plain-UNSAT."""
import sys, os, json
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
import numpy as np
from ceilF import build_full, INF
from ceil6 import Oracle6
from refine import howard, prune
G = build_full(); O5 = G['O5']; O6 = Oracle6(); k5, k6 = G['keys5'], G['keys6']
lb5 = np.array([O5.st[k]['lb'] if k in O5.st else 0 for k in k5], np.int64)
ex5 = np.array([O5.st[k]['excl'] if k in O5.st else False for k in k5], bool)
ex6 = np.array([O6.st[k]['excl'] if k in O6.st else False for k in k6], bool)
ki = G['KI'][G['E5']]
for name, use6 in (('k5 exclusions only', False), ('plus k6 exclusions', True)):
    keep = ~ex5[ki] & (~ex6[G['K6']] if use6 else True)
    m = prune(G['n6'], G['U6'][keep], G['V6'][keep]); idx = np.nonzero(keep)[0][m]
    w = 120 * G['S'][G['E5'][idx]].astype(np.int64) + lb5[ki[idx]]
    _, cyc = howard(G['n6'], G['U6'][idx], G['V6'][idx], w)
    lam = Fr(int(w[cyc].sum()), len(cyc)); mu = float(lam) / 120
    print(name, json.dumps(dict(lam=str(lam), mu=round(mu, 5), m_le=round(9171 / (mu + 35), 3), len=len(cyc),
                               syms=[int(G['S'][G['E5'][idx[e]]]) for e in cyc], T5=[int(lb5[ki[idx[e]]]) for e in cyc])))
