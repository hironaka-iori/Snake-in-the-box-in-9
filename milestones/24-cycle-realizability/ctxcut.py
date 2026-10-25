"""Lazy long-window refinement of the k6 full product: 8-direction context keys.

A k6 transition e = (7-shape d0..d6, label d7, counts of w2..w6, new count of w7) already knows
an 8-direction window d0..d7 with 6 counted centres w2..w7 (w1 is uncounted).  The automaton
tests only the windows of at most 7 directions (fp.py: 3..7 directions, 2..6 counts).  Here the
whole 8-direction window is decided in the radius-4 local model (wincert.Encoding, exact lumped
counts, cycle cuts) and the transition is removed when it is UNSAT.  No new automaton state is
needed: the Lean change would be one more window length in `check6At` and one more LRAT per key.

Loop: exact minimum cycle mean lam (cutloop.mcm) with an optimal potential pi; decide every
untested transition of the critical subgraph {rc <= R} (cyclic part), rc = Q s - P + pi(u) - pi(v);
remove the UNSAT ones; repeat.  Stops when no candidate is UNSAT (the critical cycles are made
of realizable 8-direction windows), at lam >= target, or at the time cap.

  nice -n 19 python ctxcut.py allknown|keys235 [R] [hours] [target]
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
import wincert as W  # noqa: E402
from shapes import canon  # noqa: E402

NC = CL.NC
NT = 6 ** 6
LUMP = {i: (i, i) for i in range(1, 6)}; LUMP[6] = (6, 21)


def product(which):
    """Like cutloop.base_graph, but also returns the 8-direction window of every transition."""
    import bonus as BO
    import fp as FP
    if which == 'keys235':
        keys = BO.load_keys(os.path.join(CL.MS, '23-k6-lean', 'full_product', 'keys_235.json'))
        Pr = FP.Product()
        for k in keys:
            Pr.apply(k)
    else:
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            'refine_share_k6', os.path.join(CL.MS, '23-k6-lean', 'share_bonus', 'refine_share.py'))
        RS = importlib.util.module_from_spec(spec); spec.loader.exec_module(RS)
        S = RS.status(); Pr = FP.Product(); FP.load_all(S, Pr)
    g = np.flatnonzero((Pr.CNT == 0).ravel())
    u, v, s = Pr.uvw(g)
    ext = [x[3] for x in Pr.ext]
    shp = [tuple(c) for c in Pr.shp]
    E = (g // NT).astype(np.int64)
    del Pr
    return shp, ext, u.astype(np.int64), v.astype(np.int64), s.astype(np.int64), E


def window_of(ext, E, u, s, i):
    ds = list(ext[int(E[i])])
    c = int(u[i]) % NC
    syms = [(c // 6 ** k) % 6 + 1 for k in range(4, -1, -1)] + [int(s[i])]
    return ds, syms


def decide(ds, syms, radius=4):
    vs = [0]
    for d in ds:
        vs.append(vs[-1] ^ 1 << d)
    al = [None] + [LUMP[x] for x in syms]
    enc = W.Encoding(vs, al, radius)
    st, _, _ = W.decide(enc, certify=False)
    return st


def main():
    which = sys.argv[1]
    R = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    hours = float(sys.argv[3]) if len(sys.argv) > 3 else 1.0
    target = Fr(sys.argv[4]) if len(sys.argv) > 4 else Fr(83, 20)
    t0 = time.time()
    shp, ext, u, v, s, E = product(which)
    n = len(shp) * NC
    alive = np.ones(len(u), bool)
    cache = {}
    removed = []
    log = []
    out = os.path.join(HERE, 'data', f'ctxcut_{which}_R{R}.json')
    rem = os.path.join(os.environ.get('SCRATCH', '/tmp'), f'ctxcut_{which}_R{R}_removed.json')
    print(f'{which}: {len(u)} transitions, {time.time() - t0:.0f}s, rss {CL.rss_mb():.0f} MB', flush=True)
    lam_prev = Fr(4)
    while True:
        idx = np.flatnonzero(alive)
        m = CL.prune(n, u[idx], v[idx]); idx = idx[m]
        bf = CL.BF(n, u[idx], v[idx], s[idx])
        lam, cyc, pi, it = CL.mcm(bf, lam_prev)
        lam_prev = lam
        live = np.zeros(n, bool); live[u[idx]] = True
        rng = int(pi[live].max() - pi[live].min())
        b, bits = CL.bound(lam, rng)
        P, Q = lam.numerator, lam.denominator
        rc = Q * s[idx] - P + pi[u[idx]] - pi[v[idx]]
        cz = idx[rc <= R]
        mz = CL.prune(n, u[cz], v[cz]); cz = cz[mz]
        tested = unsat = 0
        for i in cz:
            ds, syms = window_of(ext, E, u, s, i)
            k = (tuple(ds), tuple(syms))
            if k not in cache:
                cache[k] = decide(ds, syms); tested += 1
            if cache[k] == 'UNSAT':
                alive[i] = False; unsat += 1
                removed.append(dict(dirs=ds, alpha=syms))
        rec = dict(round=len(log), lam=str(lam), lam_float=float(lam), pot_range=rng, bound=b,
                   live_transitions=int(len(idx)), critical=int(len(cz)), tested=tested, removed=unsat,
                   total_removed=len(removed), windows_decided=len(cache),
                   seconds=round(time.time() - t0), rss_mb=round(CL.rss_mb()))
        print(json.dumps(rec), flush=True)
        log.append(rec)
        json.dump(dict(which=which, R=R, rounds=log), open(out, 'w'))
        json.dump(removed, open(rem, 'w'))
        if unsat == 0 or lam >= target or time.time() - t0 > hours * 3600:
            break
    # the final critical cycle: its 8-direction windows (all SAT when the loop stalled)
    cu = [int(bf.U[e]) for e in cyc]
    crit = dict(length=len(cyc), counts=[int(bf.S[e]) for e in cyc],
                shapes=[''.join(map(str, shp[x // NC])) for x in cu])
    json.dump(dict(which=which, R=R, rounds=log, removed_sample=removed[:20], final_cycle=crit,
                   windows_sat=sum(1 for x in cache.values() if x == 'SAT'),
                   windows_unsat=sum(1 for x in cache.values() if x == 'UNSAT')), open(out, 'w'))
    print('final cycle', crit, flush=True)


if __name__ == '__main__':
    main()
