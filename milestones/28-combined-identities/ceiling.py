"""Stage C: ceiling and what-if values of the share (+ w_3) combination on the k6 full product.

  ceiling   minimum cycle mean of 120 A + S5ub over transitions whose trailing 5-window has a share
            witness (S5ub = least witnessed share, an upper bound on what any 5-window share
            certificate can prove) and whose 6-window is known plain-SAT (so no plain key of <= 7
            directions ending there can remove it).  No set of 5-window share certificates and
            k <= 6 plain exclusions lifts such a cycle.
  whatif F  S5 = max(lb, min(ub, F)) where the window was never threshold-tested (lb only if tested),
            i.e. "every untested 5-window forces F" (the share loops' heuristic), plain-untested
            transitions kept.
usage: ceiling.py ceiling | whatif F [F ...]
"""
import sys, os, json, itertools
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import comb as C
from fractions import Fraction as Fr
INF = 10 ** 6


def tables():
    O = C.share_records()
    ub = {}; tested = {}
    for (ds, al), s in O.st.items():
        if len(al) != 5:
            continue
        for t in itertools.product(*[C.lumped_choices(a) for a in al]):
            for cc, tt in ((C.canon(tuple(ds)), tuple(t)), (C.canon(tuple(reversed(ds))), tuple(reversed(t)))):
                x = C.GA.cnt_idx(tt)
                if s['ub'] < INF:
                    arr = ub.setdefault(cc, np.full(6 ** 5, INF, np.int64))
                    arr[x] = min(arr[x], s['ub'])
                if s.get('tested'):
                    arr = tested.setdefault(cc, np.zeros(6 ** 5, bool))
                    arr[x] = True
    return O, ub, tested


def arrays(G):
    O, UB, TST = tables()
    S = C.fp.Status()
    Pr = C.fp.Product()
    ub = np.full(len(G['U']), INF, np.int64); tst = np.zeros(len(G['U']), bool)
    sat6 = np.zeros(len(G['U']), bool)
    e_of = G['G'] // C.NT; x_of = G['G'] % C.NT
    for e, (i, d, j, ds) in enumerate(Pr.ext):
        sel = np.nonzero(e_of == e)[0]
        if not len(sel):
            continue
        xs = x_of[sel]
        c5 = C.canon(ds[2:8])
        if c5 in UB:
            ub[sel] = UB[c5][xs % 7776]
        if c5 in TST:
            tst[sel] = TST[c5][xs % 7776]
        c6 = C.canon(ds[1:8])
        for q, x in zip(sel, xs):
            if ub[q] >= INF:
                continue
            t = tuple(int(x) // 6 ** k % 6 + 1 for k in range(5, -1, -1))
            if S.st.get(C.fp.lkey(ds[1:8], t)) == 'SAT':
                sat6[q] = True
    return ub, tst, sat6


def main():
    mode = sys.argv[1]
    G = C.build('all', with_share=True, with_w3=True)
    n = int(G['n'])
    npz = os.path.join(C.SCR, 'ceiling_arrays.npz')
    if os.path.exists(npz):
        z = np.load(npz); ub, tst, sat6 = z['ub'], z['tst'], z['sat6']
    else:
        ub, tst, sat6 = arrays(G); np.savez(npz, ub=ub, tst=tst, sat6=sat6)
    C.log(f'{(ub < INF).sum()} transitions with a share witness, {sat6.sum()} with a plain-SAT 6-window')
    out = {}
    if mode == 'ceiling':
        keep = np.nonzero((ub < INF) & sat6)[0]
        m = C.prune(n, G['U'][keep].astype(np.int64), G['V'][keep].astype(np.int64))
        keep = keep[m]
        C.log(f'witnessed live transitions: {len(keep)}')
        if len(keep):
            w = 120 * G['A'][keep].astype(np.int64) + ub[keep]
            mu, cyc = C.howard(n, G['U'][keep], G['V'][keep], w)
            cyc = [int(keep[e]) for e in cyc]
            lam = Fr(int((120 * G['A'][cyc].astype(np.int64) + ub[cyc]).sum()), len(cyc))
            out = dict(mode='ceiling', lam=str(lam), mu_alpha=float(lam) / 120,
                       m_real=C.bound_real(float(lam), 1, 0, 0), witnessed_live=int(len(keep)),
                       cycle=[dict(C.cycle_info(G, None, [e])[0], S5ub=int(ub[e])) for e in cyc])
            C.log(json.dumps({k: v for k, v in out.items() if k != 'cycle'}))
            for r in out['cycle']:
                print('   ', r, flush=True)
    else:
        res = []
        L = C.live(G)
        for F in map(int, sys.argv[2:]):
            s5 = np.where(tst[L], G['S5'][L], np.maximum(G['S5'][L], np.minimum(ub[L], F)))
            w = 120 * G['A'][L].astype(np.int64) + s5
            mu, cyc = C.howard(n, G['U'][L], G['V'][L], w)
            lam = Fr(int(w[cyc].sum()), len(cyc))
            r = dict(F=F, lam=str(lam), mu_alpha=float(lam) / 120, m_real=C.bound_real(float(lam), 1, 0, 0),
                     cycle=[dict(C.cycle_info(G, None, [int(L[e])])[0], S5used=int(s5[e])) for e in cyc])
            C.log(json.dumps({k: v for k, v in r.items() if k != 'cycle'}))
            res.append(r)
        out = dict(mode='whatif', runs=res)
    json.dump(out, open(os.path.join(HERE, 'data', f'c_{mode}.json'), 'w'), indent=1)


if __name__ == '__main__':
    main()
