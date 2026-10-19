"""Re-weight the radius-4 L7 k5 K5 automaton (exclusions = cached radius-4 UNSAT windows, as refine.py)
with symbol weights w(s) = s + bonus(s) and report the minimum cycle mean and its cycle windows.
usage: automaton.py '<json dict symbol->bonus (Fraction strings)>' [out.json]"""
import sys, json, os, pickle
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../10-window-aggregate/scripts'))
from fractions import Fraction as Fr
import numpy as np
from refine import Automaton, Oracle, prune, howard

HERE = os.path.dirname(os.path.abspath(__file__))
PK = os.path.join(HERE, 'aut_L7k5K5r4.pkl')

def load():
    if os.path.exists(PK):
        return pickle.load(open(PK, 'rb'))
    A = Automaton(7, 5, 5); O = Oracle(4)
    U, V, W, WIN = A.edges(O)
    m = prune(A.n, U, V); idx = np.nonzero(m)[0]
    U, V, W = U[idx], V[idx], W[idx]; WIN = [WIN[i] for i in idx]
    inv = {u: k for k, u in A.sid.items()}
    d = dict(n=A.n, U=U, V=V, W=W, WIN=WIN, inv=inv)
    pickle.dump(d, open(PK, 'wb'))
    return d

def mean_with(d, bonus, D=5040):
    W = d['W']
    w = np.array([int(round((s + bonus.get(int(s), Fr(0))) * D)) for s in W])
    for s in set(W.tolist()):
        assert Fr(int(round((s + bonus.get(s, Fr(0))) * D)), D) == s + bonus.get(s, Fr(0))
    mu, cyc = howard(d['n'], d['U'], d['V'], w)
    lam = Fr(int(w[cyc].sum()), len(cyc) * D)
    return lam, cyc

if __name__ == '__main__':
    bonus = {int(k): Fr(v) for k, v in json.loads(sys.argv[1]).items()} if len(sys.argv) > 1 else {}
    d = load()
    lam, cyc = mean_with(d, bonus)
    syms = [int(d['W'][e]) for e in cyc]
    out = {'bonus': {k: str(v) for k, v in bonus.items()}, 'mean': str(lam), 'meanf': float(lam),
           'bound_v': 9214 / (35 + float(lam)), 'cycle_syms': syms,
           'cycle_states': [[list(d['inv'][int(d['U'][e])][0]), list(d['inv'][int(d['U'][e])][1])] for e in cyc],
           'cycle_windows': [[[list(k[0]), [list(a) for a in k[1]]] for k in d['WIN'][e]] for e in cyc]}
    print(json.dumps({k: v for k, v in out.items() if k not in ('cycle_windows', 'cycle_states')}))
    if len(sys.argv) > 2:
        json.dump(out, open(sys.argv[2], 'w'), indent=0)
