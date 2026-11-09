"""What a share-weighted k6 chain at lambda_t would need (dual reading of one potential).

Optimistic weights wF = 120 A + S5F, S5F = proved lb where the window was threshold-tested, else
max(lb, min(ub, F)) (comb/ceiling.py what-if).  Bellman-Ford from 0 for Q wF - P on every allowed
transition gives a potential pi (or proves lambda_t infeasible even optimistically).  With pi fixed,
a transition e: u -> v is satisfied by its proved weight iff
    Q (120 A + S5lb) - P + pi(u) - pi(v) >= 0;
otherwise its 5-window needs a share certificate with T >= ceil((P - Q 120 A - pi(u) + pi(v)) / Q)
(or a plain exclusion of a window ending there).  Grouped by 5-window key: the certificate list
for this potential.  Keys already proved high enough cost nothing new.
usage: need.py P/Q F [--keys all|cert]
"""
import sys, os, json, time, itertools
from fractions import Fraction as Fr
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import comb as C
import ceiling as CE

INF = 10 ** 6


def main():
    lam = Fr(sys.argv[1]); F = int(sys.argv[2])
    keys = sys.argv[sys.argv.index('--keys') + 1] if '--keys' in sys.argv else 'all'
    P, Q = lam.numerator, lam.denominator
    G = C.build(keys, with_share=True, with_w3=False)
    n = int(G['n'])
    if keys == 'all':
        z = np.load(os.path.join(C.SCR, 'ceiling_arrays.npz')); ub, tst = z['ub'], z['tst']
    else:
        ub, tst, _ = CE.arrays(G)
    A = G['A'].astype(np.int64); lb = G['S5'].astype(np.int64)
    s5F = np.where(tst, lb, np.maximum(lb, np.minimum(ub, F)))
    U = G['U'].astype(np.int64); V = G['V'].astype(np.int64)
    t0 = time.time()
    pi, it = C.bellman_ford(n, U, V, Q * (120 * A + s5F) - P, 30000)
    if pi is None:
        print(json.dumps(dict(lam=str(lam), F=F, feasible=False, rounds=it)))
        return
    R = int(pi.max() - pi.min())
    red = Q * (120 * A + lb) - P + pi[U] - pi[V]
    bad = np.nonzero(red < 0)[0]
    if '--used' in sys.argv:              # certificates the proved weights already rely on
        bad = np.nonzero(Q * 120 * A - P + pi[U] - pi[V] < 0)[0]
    need = -(-(P - Q * 120 * A[bad] - pi[U[bad]] + pi[V[bad]]) // Q)       # required S5 (ceil)
    req = {}
    for e, T in zip(bad, need):
        ds, t, k5, k6 = C.step_windows(int(G['G'][e]))
        req[k5] = max(req.get(k5, 0), int(T))
    O = C.share_records()
    hist = {}
    tested_low = 0; witnessed_below = 0
    rows = []
    for k, T in req.items():
        s = O.st.get(C.rkey_of(k))
        st = 'untested' if s is None or not s.get('tested') else 'tested'
        if s is not None and s['ub'] < T:
            witnessed_below += 1
        if st == 'tested':
            tested_low += 1
        b = min(T // 24 * 24, 240)
        hist[b] = hist.get(b, 0) + 1
        rows.append(dict(key=[list(k[0]), list(k[1])], T=T, status=st, lb=s['lb'] if s else 0,
                         ub=s['ub'] if s else None, fail=s['fail'] if s else None))
    out = dict(lam=str(lam), lam_float=float(lam), F=F, keys=keys, feasible=True, R=R, R_units=R / Q / 120,
               rounds=it, bf_s=round(time.time() - t0), m_real_lo=C.bound_real(float(lam), 1, 0, 0, R / Q),
               bound=int(C.bound_m(P, Q, R, 1, 0, 0)), deficient_transitions=int(len(bad)),
               keys_needing_share=len(req), of_which_tested=tested_low,
               of_which_witness_below_need=witnessed_below,
               T_histogram={str(k): v for k, v in sorted(hist.items())})
    print(json.dumps(out), flush=True)
    out['rows'] = sorted(rows, key=lambda r: -r['T'])
    json.dump(out, open(os.path.join(HERE, 'data', f'need_{P}_{Q}_F{F}_{keys}.json'), 'w'), indent=0)


if __name__ == '__main__':
    main()
