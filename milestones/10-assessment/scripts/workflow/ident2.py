import json, math
from math import comb
from delsarte2 import maxT
bank = json.load(open('/home/user/Snake-in-the-box-in-9/work/bank9.json'))
rows = {r['k']: r for r in json.load(open('census.json'))}
bad = 0; gaps = []
for k, e in enumerate(bank):
    S = set(e['vertex_sequence']); v = len(S); r = rows[k]
    s = {u: sum((u ^ 1 << q) in S for q in range(9)) for u in range(512) if u not in S}
    sigma = sum(comb(9 - x, 2) for x in s.values())
    if sigma != 4 * r['n'][0] + r['n'][1]: bad += 1
    if r['T'] + sigma != 18428 - 70 * v: bad += 1
    assert sum(s.values()) == 7 * v + 2
    sbar = (7 * v + 2) / (512 - v)
    J = (512 - v) * (9 - sbar) * (8 - sbar) / 2
    gaps.append((sigma - J) / v)
print('identity 4n0+n1 = sum_{u notin S} C(9-s(u),2) and T+sum = 18428-70v: failures =', bad, 'over', len(bank))
print('Jensen gap (sum f - J)/v on bank: min %.3f max %.3f' % (min(gaps), max(gaps)))
def J(v):
    sbar = (7 * v + 2) / (512 - v); return (512 - v) * (9 - sbar) * (8 - sbar) / 2
print(' v   T cap: square(n0>=0)  Jensen(18428-70v-J)  Delsarte   -> min,  per vertex')
for v in (193, 198, 202, 205, 208, 210, 212, 215, 220, 230, 247):
    a = 9214 - 35 * v; b = 18428 - 70 * v - J(v); c = maxT(v)
    print('%4d  %8.1f %10.1f %10.1f   %8.1f  %6.3f' % (v, a, b, c, min(a, b, c), min(a, b, c) / v))
for c in (8.5,):
    vm = max(v for v in range(150, 260) if c * v <= min(9214 - 35 * v, 18428 - 70 * v - J(v), maxT(v)))
    vm2 = max(v for v in range(150, 260) if c * v <= min(9214 - 35 * v, 18428 - 70 * v - J(v)))
    print('uniform T >= %.1f v: max v = %d with all three caps (%d edges); square+Jensen only: %d' % (c, vm, vm - 1, vm2))
