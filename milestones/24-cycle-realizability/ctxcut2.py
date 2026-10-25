"""Second stage of ctxcut.py: 9-direction windows (7 counted centres) on the line graph.

Stage 1 (ctxcut.py) removes the k6 transitions whose own 8-direction window is UNSAT and
stalls when the critical cycle is made of SAT 8-direction windows.  Stage 2 remembers one more
transition: the nodes are the live stage-1 transitions, the edges are consecutive pairs (a, b)
(this is the k7 automaton restricted to live k6 transitions), the weight is the count of b.
The window of (a, b) is ext[a] followed by the label of b: 9 directions d0..d8 with lumped
counts on w2..w8.  When b's label is the fresh symbol of its 7-shape, it may concretely be d0
or a brand-new coordinate; the pair is removed only when every concrete version is UNSAT.

  nice -n 19 python ctxcut2.py allknown [R] [hours]
"""
import sys, os, json, time
from fractions import Fraction as Fr
for _v in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '1'
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
import cutloop as CL  # noqa: E402
import ctxcut as C1  # noqa: E402

NC = CL.NC


def stage1(shp, ext, u, v, s, E, R=0):
    """Re-run the stage-1 loop silently; returns the alive mask and lam_prev."""
    n = len(shp) * NC
    alive = np.ones(len(u), bool)
    cache = {}
    lam_prev = Fr(4)
    while True:
        idx = np.flatnonzero(alive)
        m = CL.prune(n, u[idx], v[idx]); idx = idx[m]
        bf = CL.BF(n, u[idx], v[idx], s[idx])
        lam, cyc, pi, it = CL.mcm(bf, lam_prev); lam_prev = lam
        P, Q = lam.numerator, lam.denominator
        rc = Q * s[idx] - P + pi[u[idx]] - pi[v[idx]]
        cz = idx[rc <= R]
        mz = CL.prune(n, u[cz], v[cz]); cz = cz[mz]
        k = 0
        for i in cz:
            ds, syms = C1.window_of(ext, E, u, s, i)
            key = (tuple(ds), tuple(syms))
            if key not in cache:
                cache[key] = C1.decide(ds, syms)
            if cache[key] == 'UNSAT':
                alive[i] = False; k += 1
        print(f'stage1 lam {lam}, removed {k}', flush=True)
        if k == 0:
            return idx, lam


def concrete9(ext, E, a, b):
    """Concrete 9-direction windows of the pair (a, b) (1 or 2 of them)."""
    da = list(ext[int(E[a])])
    db = list(ext[int(E[b])])            # canonical: shape of da[1:] + label
    tail = da[1:]
    # canonical symbol -> concrete label of da[1:]
    mp = {}
    for x in tail:
        if x not in mp:
            mp[x] = None
    order = list(mp)                      # concrete labels in order of first appearance
    lab = db[-1]
    if lab < len(order):
        return [da + [order[lab]]]
    outs = []
    if da[0] not in tail:
        outs.append(da + [da[0]])
    fresh = min(x for x in range(9) if x not in da)
    outs.append(da + [fresh])
    return outs


def main():
    which = sys.argv[1]
    R = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    hours = float(sys.argv[3]) if len(sys.argv) > 3 else 1.0
    t0 = time.time()
    shp, ext, u, v, s, E = C1.product(which)
    live, lam1 = stage1(shp, ext, u, v, s, E)
    n = len(shp) * NC
    # line graph on the live transitions
    m = len(live)
    lu, lv, ls, lE = u[live], v[live], s[live], E[live]
    o = np.argsort(lu, kind='stable')
    first = np.searchsorted(lu[o], np.arange(n)); last = np.searchsorted(lu[o], np.arange(n), side='right')
    cnt = last[lv] - first[lv]
    E2 = int(cnt.sum())
    print(f'stage 2: {m} nodes, {E2} pair edges, rss {CL.rss_mb():.0f} MB, {time.time() - t0:.0f}s', flush=True)
    if E2 > 15_000_000:
        print('line graph too large for the 1.5 GB budget: stop', flush=True); return
    A = np.repeat(np.arange(m, dtype=np.int32), cnt)
    offs = np.arange(E2, dtype=np.int64) - np.repeat(np.cumsum(cnt) - cnt, cnt)
    B = o[np.repeat(first[lv], cnt) + offs].astype(np.int32)
    del offs
    S2 = ls[B].astype(np.int8)
    alive = np.ones(E2, bool)
    print(f'line graph built, rss {CL.rss_mb():.0f} MB', flush=True)
    cache, log, removed = {}, [], []
    lam_prev = lam1
    out = os.path.join(HERE, 'data', f'ctxcut2_{which}_R{R}.json')
    while True:
        idx = np.flatnonzero(alive)
        mk = CL.prune(m, A[idx].astype(np.int64), B[idx].astype(np.int64)); idx = idx[mk]
        bf = CL.BF(m, A[idx].astype(np.int64), B[idx].astype(np.int64), S2[idx].astype(np.int64))
        lam, cyc, pi, it = CL.mcm(bf, lam_prev); lam_prev = lam
        P, Q = lam.numerator, lam.denominator
        livem = np.zeros(m, bool); livem[A[idx]] = True
        rng = int(pi[livem].max() - pi[livem].min())
        b, bits = CL.bound(lam, rng)
        rc = Q * S2[idx].astype(np.int64) - P + pi[A[idx]] - pi[B[idx]]
        cz = idx[rc <= R]
        mz = CL.prune(m, A[cz].astype(np.int64), B[cz].astype(np.int64)); cz = cz[mz]
        tested = unsat = 0
        for j in cz:
            a, bb = int(A[j]), int(B[j])
            _, syms = C1.window_of(ext, lE, lu, ls, a)
            syms = syms + [int(ls[bb])]
            sts = []
            for ds in concrete9(ext, lE, a, bb):
                key = (tuple(ds), tuple(syms))
                if key not in cache:
                    cache[key] = C1.decide(ds, syms); tested += 1
                sts.append(cache[key])
            if all(x == 'UNSAT' for x in sts):
                alive[j] = False; unsat += 1
                if len(removed) < 20:
                    removed.append(dict(dirs=concrete9(ext, lE, a, bb), alpha=syms))
        rec = dict(round=len(log), lam=str(lam), lam_float=float(lam), pot_range=rng, bound=b,
                   live_pairs=int(len(idx)), critical=int(len(cz)), tested=tested, removed=unsat,
                   windows_decided=len(cache), windows_unsat=sum(1 for x in cache.values() if x == 'UNSAT'),
                   seconds=round(time.time() - t0), rss_mb=round(CL.rss_mb()))
        print(json.dumps(rec), flush=True)
        log.append(rec)
        json.dump(dict(which=which, R=R, stage1_lam=str(lam1), nodes=m, pair_edges=E2, rounds=log,
                       removed_sample=removed), open(out, 'w'))
        if unsat == 0 or time.time() - t0 > hours * 3600 or CL.rss_mb() > 1400:
            break
    cu = [int(bf.U[e]) for e in cyc]
    crit = dict(length=len(cyc), counts=[int(bf.S[e]) for e in cyc],
                shapes=[''.join(map(str, shp[int(lu[x]) // NC])) for x in cu])
    json.dump(dict(which=which, R=R, stage1_lam=str(lam1), nodes=m, pair_edges=E2, rounds=log,
                   removed_sample=removed, final_cycle=crit), open(out, 'w'))
    print('final cycle', crit, flush=True)


if __name__ == '__main__':
    main()
