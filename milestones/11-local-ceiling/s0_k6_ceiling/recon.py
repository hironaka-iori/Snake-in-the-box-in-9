"""Reconstruct the optimistic (ceiling) minimum cycle of the share loop: its states, symbols and 5-window keys."""
import sys, os, json, pickle
sys.dont_write_bytecode = True
R = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')
sys.path.insert(0, R + '/11-local-ceiling/s0_share_loop'); sys.path.insert(0, R + '/10-window-aggregate/scripts')
import numpy as np
import refine_share as rs
from refine import Automaton, howard, prune
n, U, V, S, KI, keys = rs.load_compact(rs.DEFAULT_PKL)
O = rs.ShareOracle()
ev = rs.evaluate(n, U, V, S, KI, keys, O)
print(ev['lo']['mu'], ev['hi']['mu'], ev['hi']['cycle_syms'])
A = Automaton(7, 5, 5); inv = {u: k for k, u in A.sid.items()}
# recover the cycle edges
lb = np.array([O.st[k]['lb'] if k in O.st else 0 for k in keys], np.int64)
ub = np.array([O.st[k]['ub'] if k in O.st else rs.INF for k in keys], np.int64)
ex = np.array([O.st[k]['excl'] if k in O.st else False for k in keys], bool)
keep = ~ex[KI]; m = prune(n, U[keep], V[keep]); idx = np.nonzero(keep)[0][m]
w = rs.UNIT * S[idx].astype(np.int64) + np.minimum(ub, rs.INF)[KI[idx]]
_, cyc = howard(n, U[idx], V[idx], w)
for e in cyc:
    E = idx[e]; k = keys[KI[E]]
    print(inv[int(U[E])], '->', inv[int(V[E])], 'sym', S[E], 'key', k, O.st.get(k))

