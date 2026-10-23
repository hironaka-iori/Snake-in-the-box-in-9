"""Statuses of every suffix window on the minimum-mean cycle of the share-weighted product
with all known plain UNSAT keys (refine_share.status()).  usage: python obstruction.py B"""
import sys, json
import numpy as np
import refine_share as RS
B = int(sys.argv[1]) if len(sys.argv) > 1 else 6
S = RS.status(); Pr = RS.FP.Product(); RS.FP.load_all(S, Pr); patE = RS.pat_flags(Pr)
g = np.flatnonzero((Pr.CNT == 0).ravel())
u, v, s, w = RS.weights(Pr, patE, g, 0, B)
u = u.astype(np.int64); v = v.astype(np.int64)
keep = np.flatnonzero(RS.live_prune(Pr.n, u, v))
mu, cyc = RS.howard(Pr.n, u[keep], v[keep], w[keep], iters=400)
cyc = [int(g[keep[e]]) for e in cyc]
out = []
for e in cyc:
    ws = Pr.windows(e)
    out.append(dict(dirs8=list(Pr.ext[e // RS.NT][3]), windows=[[list(k[0]), list(k[1]), S.st.get(k)] for k in ws]))
stats = {}
for o in out:
    for k in o['windows']:
        stats[k[2]] = stats.get(k[2], 0) + 1
res = dict(B=B, mean=float(w[[np.searchsorted(g, e) for e in cyc]].sum()) / len(cyc), length=len(cyc),
           window_statuses=stats, edges=out)
print(json.dumps(dict(B=B, mean_alpha=res['mean'] / 24, length=len(cyc), window_statuses=stats)))
json.dump(res, open(sys.argv[2], 'w'), indent=1) if len(sys.argv) > 2 else None
