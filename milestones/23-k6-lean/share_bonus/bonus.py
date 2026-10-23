"""Share-weighted minimum cycle mean of the k6 full product (keys_235).

Edge weight  w = 24 * s + bonus(edge),  s = new lumped count (1..6),
bonus = B when the 7-direction window of the step (the hw6 window, directions
d(n+1)..d(n+7), r = n+1) has canonical shape 0123415, i.e. directions (a,b,c,d,e,b,f)
with six distinct coordinates -- the hypothesis of `pattern_share_in_snake`.

usage: nice -n 19 python bonus.py mcm B [B ...]     minimum cycle mean for each bonus B
       nice -n 19 python bonus.py bf P Q B          exact Bellman-Ford test of lambda = P/Q
"""
import sys, os, json, time
sys.dont_write_bytecode = True
for v in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[v] = '1'
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
MS = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(MS, '23-k6-lean', 'full_product'))
sys.path.insert(0, os.path.join(MS, '10-window-aggregate', 'scripts'))
import fp as FP
import gen_lean_automaton6 as GA
from refine import prune, howard, canon

PAT = (0, 1, 2, 3, 4, 1, 5)
NC, NT = GA.NC, GA.NT


def load_keys(path):
    d = json.load(open(path))
    return [(tuple(k[0]), tuple(GA.sym_of(tuple(a)) for a in k[1])) for k in d['keys']]


def build(keys):
    Pr = FP.Product()
    for k in keys:
        Pr.apply(k)
    patE = np.array([canon(ds[1:]) == PAT for (_, _, _, ds) in Pr.ext])
    g = np.flatnonzero((Pr.CNT == 0).ravel())
    u, v, s = Pr.uvw(g)
    flag = patE[g // NT]
    return Pr, g, u.astype(np.int64), v.astype(np.int64), s.astype(np.int64), flag


def bf(n, u, v, w, maxit=5000):
    """Integer Bellman-Ford from pi = 0; returns (pi or None, rounds)."""
    o = np.argsort(v, kind='stable')
    us, vs, ws = u[o], v[o], w[o]
    uv, starts = np.unique(vs, return_index=True)
    pi = np.zeros(n, np.int64)
    for it in range(maxit):
        mins = np.minimum.reduceat(pi[us] + ws, starts)
        upd = mins < pi[uv]
        if not upd.any():
            return pi, it
        pi[uv[upd]] = mins[upd]
    return None, maxit


def mcm(Pr, u, v, s, flag, B):
    w = 24 * s + B * flag
    keep = np.flatnonzero(prune(Pr.n, u, v))
    mu, cyc = howard(Pr.n, u[keep], v[keep], w[keep], iters=400)
    cyc = [keep[e] for e in cyc]
    from fractions import Fraction as Fr
    lam = Fr(int(w[cyc].sum()), len(cyc))
    info = dict(B=B, mean=str(lam), mean_float=float(lam), alpha_units=float(lam) / 24,
                length=len(cyc), counts=[int(s[e]) for e in cyc], pattern_edges=int(flag[cyc].sum()),
                shapes=[GA.lst(Pr.shp[int(u[e]) // NC]) for e in cyc])
    return lam, info


def main():
    t0 = time.time()
    keys = load_keys(os.path.join(MS, '23-k6-lean', 'full_product', 'keys_235.json'))
    Pr, g, u, v, s, flag = build(keys)
    print(f'{len(keys)} keys, {Pr.n} states, {len(g)} transitions, {int(flag.sum())} pattern '
          f'transitions, {time.time() - t0:.0f}s, rss {FP.rss_mb():.0f} MB', flush=True)
    if sys.argv[1] == 'mcm':
        for B in map(int, sys.argv[2:]):
            lam, info = mcm(Pr, u, v, s, flag, B)
            P, Q = lam.numerator, lam.denominator
            pi, it = bf(Pr.n, u, v, Q * (24 * s + B * flag) - P)
            info['bf_converged'] = pi is not None
            if pi is not None:
                info['range'] = int(pi.max() - pi.min()); info['bf_rounds'] = it
            print(json.dumps(info), flush=True)
    elif sys.argv[1] == 'bf':
        P, Q, B = map(int, sys.argv[2:5])
        pi, it = bf(Pr.n, u, v, Q * (24 * s + B * flag) - P)
        print(json.dumps(dict(P=P, Q=Q, B=B, converged=pi is not None, rounds=it,
                              range=None if pi is None else int(pi.max() - pi.min()))), flush=True)
    print(f'done {time.time() - t0:.0f}s rss {FP.rss_mb():.0f} MB', flush=True)


if __name__ == '__main__':
    main()
