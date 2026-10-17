import json, itertools
from fractions import Fraction
from potential import min_mean, cycle_witness, edge_bound
d = json.load(open('patterns_r3_s9.json'))
st = {}
for r in d: st.setdefault(tuple(r['alpha']), {})[r['shape']] = r['status']
excl = {p for p, s in st.items() if all(v == 'INFEASIBLE' for v in s.values())}
sym = lambda ps: set(ps) | {p[::-1] for p in ps}
F = sym(excl)
c = min_mean(F); print('assume all radius-3 exclusions:', sorted(excl), '\n  min mean =', c, 'cycle', cycle_witness(F, c), 'edges <=~', edge_bound(c))
# which single further exclusion helps most
feas = [p for p, s in st.items() if p not in excl]
for p in sorted(feas, key=sum):
    c2 = min_mean(F | sym({p}))
    print('   + exclude', p, '-> min mean', c2, 'edges<=~', edge_bound(c2))
