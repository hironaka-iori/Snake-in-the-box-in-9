import sys, json
sys.path.insert(0, '/home/user/Snake-in-the-box-in-9/milestones/28-combined-identities')
import comb as C, share7 as S7
Pr = C.fp.Product()
d = json.load(open('data/c_ceiling.json'))
X = S7.Ctx(); seen = set()
for c in d['cycle']:
    ds, t, k5, k6 = C.step_windows(c['g'], Pr)
    c7 = C.canon(ds[1:8])
    if (c7, t) in seen: continue
    seen.add((c7, t))
    T = c['S5ub'] + 1
    r = S7.thr(c7, t, T, 7, tl=90)
    print(c['shape'], t, 'A', c['A'], 'S5ub', c['S5ub'], 'ctx7 T', T, r['result'], r['seconds'], r['witness5'], flush=True)
