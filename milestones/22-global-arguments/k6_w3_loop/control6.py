"""Control for sweep6.py: re-solve known-status 6-keys (plain statuses from earlier runs) with the
per-shape incremental encoding and check agreement.  usage: control6.py N   -> data/control6.json"""
import sys, os, json, time, random
ME = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, ME)
import k6w3loop as L
from k6w3loop import *
from sweep_w3 import AlphaInc
G, P, O, sub = setup()
n = int(sys.argv[1]); random.seed(1)
known = [k for k in G['keys6'] if P.st.get(k) in ('SAT', 'UNSAT') and P.src.get(k) != 'w3excl']
ds0 = max(set(k[0] for k in known), key=lambda d: sum(1 for k in known if k[0] == d))
ks = [k for k in known if k[0] == ds0]; random.shuffle(ks); ks = ks[:n]
w = w3enc.window_from_dirs(list(ds0)); enc = AlphaInc(w, None, 4, None, sym=False)
agree = dis = 0; t = time.time()
with survey.Cadical153(bootstrap_with=enc.clauses) as sv:
    for k in ks:
        ass = []
        for i, (lo, hi) in enumerate(k[1]):
            if lo >= 1: ass.append(enc.atot[i][lo])
            if hi < 21: ass.append(-enc.atot[i][hi + 1])
        st, sel, cuts, sec = survey.solve_assume(sv, enc, ass, 30)
        if st == P.st[k]: agree += 1
        elif st != 'TIMEOUT': dis += 1; print('DISAGREE', k, st, P.st[k])
out = dict(shape=ds0, n=len(ks), agree=agree, disagree=dis, seconds=round(time.time() - t, 1),
           sat=sum(1 for k in ks if P.st[k] == 'SAT'))
print(out); json.dump(out, open(os.path.join(L.DATA, 'control6.json'), 'w'))
