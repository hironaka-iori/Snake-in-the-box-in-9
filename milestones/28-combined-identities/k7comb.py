"""Stage B on the k7 product of milestone 25 (keys_best234): alpha + share (+ w_3) combinations.

State (e, a2..a7): 8-direction shape e, 6 counts; step X = shape ++ [d] (9 directions), new count
s = a8.  The transitions are those of k7.K7.mask (closed-set rule: both states live, no F8/H9 key).
Per transition: A = s; S5 = share lb of the trailing 5-window (dirs X[3:9], counts a4..a8);
W6 = w_3 lb of the 6-window (dirs X[2:9], counts a3..a8), as comb.W3Tables.

Arithmetic (k7 analogue of comb.py (*); steps j = 8 .. m-1, a1..a7 >= 1, endpoints >= 4,
42 multiplicity deficits of 6-windows among internal vertices):
  (P + 4200 a Q) m <= Q (1099680 a + b (387072 - 42 c1)) + 8 P + R.
a = 1, b = 0, S5 = 0 is the k7 alpha chain (P + 35Q) m + 7Q <= 9171 Q + 8P + R times 120.
usage: k7comb.py SHARE W3      SHARE = none | cert | all
"""
import sys, os, json, time, gzip
from fractions import Fraction as Fr
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import comb as C
sys.path.insert(0, os.path.join(C.MS, '25-k7-234'))
import k7
NC, NT = k7.NC, k7.NT
KEYS = os.path.join(C.MS, '25-k7-234', 'data', 'keys_best234.json.gz')


class Dummy:
    pass


def load_k7(which='best'):
    if which == 'pool':                   # every known UNSAT k6/F8/H9 key (milestone 25 pool)
        import prune234
        S, O, keys6, newk = prune234.pool()
        keys6 = sorted(set(keys6) | set(k for k in C.own_plain_unsat() if 2 <= len(k[1]) <= 6))
        K = k7.K7(Dummy(), keys6)
        for k in newk:
            K.add_new(k)
        return K, dict(pool=True, k6=len(keys6), new=len(newk))
    d = json.load(gzip.open(KEYS, 'rt'))
    k6, new = [], []
    for k in d['keys']:
        if k[0] == 'k6':
            k6.append((tuple(k[1]), tuple(k[2])))
        else:
            new.append((k[0], tuple(k[1]), tuple(k[2])))
    K = k7.K7(Dummy(), k6)
    for k in new:
        K.add_new(k)
    return K, d['summary']


def edges(K, share, w3):
    SD = C.share_dense(share == 'cert') if share != 'none' else {}
    W3 = C.W3Tables() if w3 else None
    z5 = np.zeros(6 ** 5, np.int64)
    i5 = ((np.arange(NC) % 1296)[:, None] * 6 + np.arange(6)[None, :])          # (NC, 6)
    Us, Vs, As, Ss, Ws = [], [], [], [], []
    CX = {}                                             # context share records (share7.py)
    if share == 'all' and os.environ.get('NOCTX') != '1':
        import share7
        for (ctx, c, t), st in share7.Ctx().st.items():
            if st['lb'] > 0:
                CX.setdefault((ctx, tuple(c)), []).append((C.GA.cnt_idx(tuple(t)), st['lb']))
    for i in range(K.nX):
        e, e2 = K.XE[i]
        X = K.X[i]
        m = K.mask(i)                                   # (6, NC, 6) over (a2, a3..a7, a8)
        t0, mid, s = np.nonzero(m)
        Us.append((e * NT + t0 * NC + mid).astype(np.int32))
        Vs.append((e2 * NT + mid * 6 + s).astype(np.int32))
        As.append((s + 1).astype(np.int8))
        Ss.append(SD.get(C.canon(X[3:9]), z5)[i5[mid, s]].astype(np.int32))
        for ctx, lo in ((7, 2), (8, 1)):
            for x, lb in CX.get((ctx, C.canon(X[lo:9])), ()):
                hit = (mid * 6 + s) == x
                Ss[-1][hit] = np.maximum(Ss[-1][hit], lb)
        if W3 is not None:
            Ws.append(W3.dense(C.canon(X[2:9]))[mid * 6 + s].astype(np.int32))
        else:
            Ws.append(np.zeros(len(s), np.int32))
    G = dict(U=np.concatenate(Us), V=np.concatenate(Vs), A=np.concatenate(As), S5=np.concatenate(Ss),
             W6=np.concatenate(Ws), n=np.array(K.nE * NT), c1=np.array(min(W3.single.values()) if W3 else 0))
    return G


def bound_real(lam, a, b, c1, RQ=0.0):
    return (1099680 * a + b * (387072 - 42 * c1) + 8 * lam + RQ) / (lam + 4200 * a)


def bound_m(P, Q, R, a, b, c1):
    return (Q * (1099680 * a + b * (387072 - 42 * c1)) + 8 * P + R) // (P + 4200 * a * Q)


def main():
    which = 'best'
    if sys.argv[1] in ('best', 'pool'):
        which = sys.argv.pop(1)
    share, w3 = sys.argv[1], int(sys.argv[2])
    betas = [float(x) for x in sys.argv[3:] if not x.startswith('--')] or [0.0]
    t0 = time.time()
    K, summ = load_k7(which)
    G = edges(K, share, w3)
    del K
    n = int(G['n']); c1 = int(G['c1'])
    C.log(f'k7: {len(G["U"])} transitions, rss {C.rss_mb():.0f} MB, {time.time()-t0:.0f}s; summary {summ}')
    L = C.live(G)
    C.log(f'live {len(L)}, rss {C.rss_mb():.0f}')
    out = []
    for beta in betas:
        a, b = 1000, int(round(beta * 1000))
        w = C.weights(G, a, b, L)
        mu, cyc = C.howard(n, G['U'][L], G['V'][L], w)
        lam = Fr(int(w[cyc].sum()), len(cyc))
        cyc = [int(L[e]) for e in cyc]
        r = dict(share=share, w3=w3, a=a, b=b, lam=str(lam), mu_alpha=float(lam) / 120 / a,
                 m_real=bound_real(float(lam), a, b, c1),
                 cycle=[dict(A=int(G['A'][e]), S5=int(G['S5'][e]), W6=int(G['W6'][e]),
                             u=int(G['U'][e]), v=int(G['V'][e])) for e in cyc])
        C.log(json.dumps({k: v for k, v in r.items() if k != 'cycle'}), f'cycle len {len(cyc)}')
        print('   A', [c['A'] for c in r['cycle']], 'S5', [c['S5'] for c in r['cycle']], 'W6', [c['W6'] for c in r['cycle']], flush=True)
        if '--exact' in sys.argv or beta == betas[0]:
            P, Q = lam.numerator, lam.denominator
            ww = C.weights(G, a, b)
            pi, it = C.bellman_ford(n, G['U'], G['V'], Q * ww - P, 20000)
            if pi is not None:
                R = int(pi.max() - pi.min())
                r['exact'] = dict(P=P, Q=Q, R=R, R_alpha=R / Q / 120 / a, rounds=it, bound=int(bound_m(P, Q, R, a, b, c1)))
            else:
                r['exact'] = dict(P=P, Q=Q, converged=False)
            C.log('exact', r['exact'])
        out.append(r)
        json.dump(out, open(os.path.join(HERE, 'data', f'k7_{which}_{share}_{w3}.json'), 'w'), indent=1)


if __name__ == '__main__':
    main()
