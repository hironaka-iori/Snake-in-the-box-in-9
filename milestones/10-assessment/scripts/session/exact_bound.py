"""Exact edge bound from E + 2T + 70v = 18428 (E >= 0), minimising T over
count sequences: endpoints >= 4, internal counts >= 1, forbidden internal
adjacent pairs and internal triples."""
import json, itertools
K = 12
BASE = {(1,1),(1,2),(2,1),(1,3),(3,1)}
def tmin(v, F3):
    # DP over internal positions 1..v-2; state = (prev, cur) of internal values
    INF = 10**9
    if v == 2: return 8
    if v == 3: return 4 + 4 + 1
    vals = range(1, K+1)
    dp = {(None, a): a for a in vals}           # position 1
    for _ in range(2, v-1):
        nd = {}
        for (p, a), s in dp.items():
            for b in vals:
                if (a, b) in BASE: continue
                if p is not None and (p, a, b) in F3: continue
                k = (a, b)
                if s + b < nd.get(k, INF): nd[k] = s + b
        dp = nd
    return 8 + min(dp.values())
def bound(F3):
    best = None
    for v in range(150, 260):
        if 2 * tmin(v, F3) <= 18428 - 70 * v: best = v
    return best - 1
sym = lambda ps: set(ps) | {p[::-1] for p in ps}
r3 = json.load(open('patterns_r3_s9.json'))
st = {}
for r in r3: st.setdefault(tuple(r['alpha']), {})[r['shape']] = r['status']
excl12 = {p for p, s in st.items() if all(x == 'INFEASIBLE' for x in s.values())}
print('proved set (no 222):', bound(sym({(2,2,2)})))
print('+ 223           :', bound(sym({(2,2,2),(2,2,3)})))
print('+ all radius-3 exclusions (%d patterns):' % len(excl12), bound(sym(excl12)))
print('+ ... and (2,3,3):', bound(sym(excl12 | {(2,3,3)})))
