"""Exact finite bound with forbidden internal windows of length 2,3,5 (5-window exclusions read from the
cutting-plane log).  Internal values 1..K (K = '>=K'), endpoints >= 4.  tmin(v) = 8 + min internal sum
over sequences of length v-2 all of whose windows are allowed.  v feasible iff tmin(v) <= 9214-35v (parity)."""
import json, sys, itertools
import numpy as np
from mincycle import allowed_mask, sym, BASE2, min_mean_cycle

def load_forb(path5):
    r3 = json.load(open('/tmp/claude-0/-home-user-Snake-in-the-box-in-9/54df6b79-3551-5be0-97ec-edf141639c5c/scratchpad/ana/patterns_r3_s9.json'))
    st = {}
    for r in r3:
        st.setdefault(tuple(r['alpha']), {})[r['shape']] = r['status']
    excl3 = {p for p, s in st.items() if all(x == 'INFEASIBLE' for x in s.values())}
    forb = sym(BASE2) | sym(excl3)
    n5 = 0
    if path5:
        log = json.load(open(path5))
        for w, s in log['tested'].items():
            if s == 'INFEASIBLE':
                forb |= sym({tuple(json.loads(w))}); n5 += 1
    return forb, n5

def tmin_all(forb, K=8, vmax=250):
    k = 5
    ok = allowed_mask(k, K, forb)                      # (a,b,c,d,e)
    INF = 10 ** 8
    pen = np.where(ok, 0, INF).astype(np.int64)
    vals = np.arange(1, K + 1, dtype=np.int64)
    # sequences of internal length m>=4: state = last 4 values; init with all allowed 4-tuples (sub-windows checked)
    ok4 = allowed_mask(4, K, forb)
    g = np.indices((K,) * 4).sum(axis=0) + 4          # sum of 4 values (indices+1 each)
    D = np.where(ok4, g, INF).astype(np.int64)
    res = {}
    # short sequences (internal length 1..3) handled by brute force
    for m in (1, 2, 3):
        best = min(sum(t) for t in itertools.product(range(1, K + 1), repeat=m)
                   if all(t[i:i + L] not in forb for L in range(2, m + 1) for i in range(m - L + 1)))
        res[m + 2] = 8 + best
    m = 4
    while m + 2 <= vmax:
        res[m + 2] = 8 + int(D.min())
        cand = D[..., None] + pen
        D = cand.min(axis=0) + vals.reshape(1, 1, 1, K)
        D = np.minimum(D, INF)
        m += 1
    return res

def edge_bound(res):
    best = None
    for v, t in sorted(res.items()):
        if (t - v) % 2:
            t += 1
        if t <= 9214 - 35 * v:
            best = v
    return best - 1

if __name__ == '__main__':
    path = sys.argv[1] if len(sys.argv) > 1 else None
    forb, n5 = load_forb(path)
    res = tmin_all(forb)
    lam, cyc = min_mean_cycle(5, 8, forb)
    print('5-window exclusions used:', n5, ' asymptotic min mean', lam, '=%.4f' % float(lam), ' exact edge bound:', edge_bound(res),
          ' tmin(240..243)=', [res[v] for v in range(240, 244)], ' caps', [9214 - 35 * v for v in range(240, 244)])
