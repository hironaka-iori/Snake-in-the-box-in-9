import sys, json, collections
sys.path.insert(0, '/home/user/Snake-in-the-box-in-9/milestones/28-combined-identities')
import numpy as np
import comb as C, share7 as S7
from fractions import Fraction as Fr
G = C.build('all', with_share=True, with_w3=False)
C.fp.K6.OPLAIN = C.os.path.join(C.MS, '11-local-ceiling', 'k6_loop', 'oracle_plain.jsonl')
S = C.fp.Status()
for k in C.own_plain_unsat(): S.st[k] = 'UNSAT'
import glob, gzip
for l in (x for f in sorted(glob.glob(C.os.path.join(C.HERE, 'data', 'oracle_plain_r232*.jsonl*'))) for x in (gzip.open(f, 'rt') if f.endswith('.gz') else open(f))):
    r = json.loads(l)
    if r['result'] != 'UNSAT' and len(r['alpha']) in (5, 6) and all(a[0]==a[1] or a==[6,21] for a in r['alpha']):
        t = tuple(C.GA.sym_of(tuple(a)) for a in r['alpha'])
        S.st.setdefault(C.fp.lkey(tuple(r['dirs']), t), r['result'])
O = C.share_records(); X = S7.Ctx()
d = json.load(open('data/b_231try_final.json'))
Pr = C.fp.Product()
cnt = collections.Counter(); rows = []
for c in d['cycle']:
    ds, t, k5, k6 = C.step_windows(c['g'], Pr)
    s = O.st.get(C.rkey_of(k5), dict(lb=0, ub=10**6, fail=10**6))
    x7 = X.get((7, C.canon(ds[1:8]), t)); x8 = X.get((8, C.canon(ds[0:8]), t))
    p6 = S.st.get(k6)
    w5 = s['ub'] < 10**6; w7 = x7['ub'] < 10**6
    open5 = s['lb'] < s['ub'] and s['fail'] >= 10**6
    cls = ('p6:' + str(p6), 'S5wit' if w5 else 'S5nowit', 'ctx7wit' if w7 else 'ctx7nowit',
           'timeout' if min(s['fail'], x7['fail'], x8['fail']) < 10**6 else 'no-timeout')
    cnt[cls] += 1
    rows.append(dict(A=c['A'], S5=c['S5'], p6=p6, s5=[s['lb'], s['ub'], s['fail']], c7=[x7['lb'], x7['ub'], x7['fail']], c8=[x8['lb'], x8['ub'], x8['fail']]))
for k, v in sorted(cnt.items(), key=str): print(k, v)
A = np.array([r['A'] for r in rows]); print('A mean', A.mean(), 'S5 mean', np.mean([r['S5'] for r in rows]))
# ctx-7 witnessed ceiling: transitions with a plain-SAT 6-window and a ctx-7 witness
ub = np.full(len(G['U']), 10**6, np.int64)
I = S7.ctx_index(Pr, C.canon)
for (ctx, c, t), s in X.st.items():
    if ctx == 7 and s['ub'] < 10**6:
        p = S7.positions(G, I, 7, c, t, C.GA.cnt_idx, C.NT, np)
        ub[p] = np.minimum(ub[p], s['ub'])
keep = np.nonzero(ub < 10**6)[0]
m = C.prune(int(G['n']), G['U'][keep].astype(np.int64), G['V'][keep].astype(np.int64))
print('ctx7-witnessed transitions', len(keep), 'live', int(m.sum()))
if m.sum():
    kk = keep[m]; w = 120*G['A'][kk].astype(np.int64) + ub[kk]
    mu, cyc = C.howard(int(G['n']), G['U'][kk], G['V'][kk], w)
    lam = Fr(int(w[cyc].sum()), len(cyc)); print('ctx7 witnessed ceiling', lam, float(lam)/120, C.bound_real(float(lam),1,0,0))
json.dump(dict(classes={'|'.join(k): v for k, v in cnt.items()}, rows=rows), open('data/stall_final_cycle.json', 'w'))
