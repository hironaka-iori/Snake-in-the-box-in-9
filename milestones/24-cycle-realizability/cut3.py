"""Exact cut of the keys_235 critical 3-cycle alone (L_max exact, 16): product size and the
new minimum cycle mean.  Writes data/cut3_keys235.json."""
import json, os, sys
from fractions import Fraction as Fr
import numpy as np
import cutloop as CL
from shapes import unroll, minimal_period

HERE = os.path.dirname(os.path.abspath(__file__))
c = json.load(open(os.path.join(HERE, 'data', 'cycles.json')))['k6_keys235_lambda4']
st = tuple(tuple(s) for s in c['states'])
L = [unroll(list(st), ph)['max_transitions'] for ph in range(len(st))]
shp, u, v, s, nk = CL.base_graph('keys235')
n, U, V, S, nsh, nq = CL.product(shp, u, v, s, [(st, L)])
m = CL.prune(n, U, V); U, V, S = U[m], V[m], S[m]
bf = CL.BF(n, U, V, S)
lam, cyc, pi, it = CL.mcm(bf, Fr(4))
live = np.zeros(n, bool); live[U] = True
cs = [shp[int(nsh[int(bf.U[e]) // CL.NC])] for e in cyc]
res = dict(pattern=[''.join(map(str, x)) for x in st], L_max=L, product_states=n,
           live_states=int(live.sum()), live_transitions=int(len(U)), lam=str(lam),
           pot_range=int(pi[live].max() - pi[live].min()), bound=CL.bound(lam, int(pi[live].max() - pi[live].min()))[0],
           next_cycle_shapes=[''.join(map(str, x)) for x in cs[:minimal_period(cs)]],
           next_cycle_counts=[int(bf.S[e]) for e in cyc])
print(json.dumps(res))
json.dump(res, open(os.path.join(HERE, 'data', 'cut3_keys235.json'), 'w'), indent=1)
