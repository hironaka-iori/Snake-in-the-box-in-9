"""Cost-aware certificate count for a target bound (dual pruning, as ../../11-local-ceiling/k6_loop/minimal.py).

For a target m*, the needed per-vertex mean is mu* = 63148/(m* - 6) (+ epsilon), i.e. lambda* = p/q
just above 6 mu*.  An integer potential pi with  q W6(e) - p + pi[u] - pi[v] >= 0  on every live edge
is found by Bellman-Ford (exact_check), with W6 the reached weights.  Holding pi fixed, each live edge
needs only  W'(e) >= d(e) = ceil((p + pi[v] - pi[u]) / q).  Per 6-key the demand is the max over its
edges; it is met by one of
    (a) the cert-free floor  max(floor5(L) + sL, sF + floor5(R))  (sub-window / single-centre DP floors,
        which are w3_survey certificates: counted separately),
    (b) a 5-window threshold certificate on L at T >= D - sL, or on R at T >= D - sF,
    (c) a 6-window threshold certificate at T >= D,
choosing per key the smallest proved threshold that suffices.  Greedy: keys whose demand an
already-chosen 5-window certificate meets take it; otherwise the cheaper of (b)/(c) by estimated hints.
Hint estimates: sampled LRAT hints per solve-second of the class (data/proof_samples.jsonl matched to
the oracle line), floored at the class median.  Also counts the run's 6-window plain exclusions whose
edge (both ends live) would have negative slack under pi.
usage: prune.py M1 [M2 ...]     writes data/prune.json
"""
import sys, os, json, math
ME = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, ME)
from fractions import Fraction as Fr
import numpy as np
import k6w3loop as L
from k6w3loop import *

RATE = 0.42e-3 / 3600        # kernel-hours per hint (237 rate)


def certs(O, path):
    """All UNSAT threshold records per key: list of (T, seconds), from every merged oracle file."""
    out = {}
    for f in path:
        for l in open(f):
            r = json.loads(l)
            if r['result'] == 'UNSAT' and r.get('T') is not None:
                k = survey.key(tuple(r['dirs']), r['alpha'])
                out.setdefault(k, []).append((r['T'], r.get('seconds', 0) or 0))
    for k in out:
        out[k].sort()
    return out


def main():
    G, P, O, sub = setup()
    Tb = Tables(G, sub)
    files = [L.OW, os.path.join(L.K6W3, 'w3_k6_oracle.jsonl'), os.path.join(L.W3S, 'w3_alpha_oracle.jsonl')]
    C = certs(O, files)
    samp = [json.loads(l) for l in open(L.PROOFS)] if os.path.exists(L.PROOFS) else []
    med = {}
    for nc in (5, 6):
        h = sorted(s['lrat_hints'] for s in samp if s.get('centres') == nc and s.get('lrat_hints'))
        med[nc] = h[len(h) // 2] if h else 1e6
        med[f'mean{nc}'] = sum(h) / len(h) if h else 1e6
        med[f'n{nc}'] = len(h)
    hint = lambda k: med[f'mean{len(k[1])}']
    b5, b6 = masks(G, P)
    keep = ~b5[G['K5']] & ~b6[G['K6']]
    idx = live(G, keep)
    W6, lb5, ub6 = Tb.weights(G, O)
    fl6 = np.maximum(Tb.floor5[Tb.L] + Tb.sL, Tb.sF + Tb.floor5[Tb.R])
    U, V, K6 = G['U'][idx], G['V'][idx], G['K6'][idx]
    w = W6[K6]
    _, cyc = howard(G['n6'], U, V, w)
    lam = Fr(int(w[cyc].sum()), len(cyc))
    res = dict(reached_lam6=str(lam), reached_mu=float(lam) / 6, reached_m=mbound(float(lam) / 6),
               hints_per_cert=med, targets={})
    for mt in map(int, sys.argv[1:]):
        mu = Fr(63148, mt - 6) + Fr(1, 1000)
        lt = Fr(math.floor(6 * mu * 100) + 1, 100)       # lambda* = 6 mu*, rounded up to 1/100
        if lt > lam:
            res['targets'][mt] = dict(reachable=False, need_mu=float(mu)); continue
        p, q = lt.numerator, lt.denominator
        pi = exact_check(G['n6'], U, V, w, p, q)
        d = -((-(p + pi[V] - pi[U])) // q)               # ceil
        D = np.zeros(len(G['keys6']), np.int64)
        np.maximum.at(D, K6, d)
        need = np.nonzero(D > fl6)[0]
        need = need[np.argsort(-(D[need] - fl6[need]))]
        chosen5 = {}       # 5-key -> T
        chosen6 = {}
        miss = 0
        def pick(lst, T):
            for t, s in lst:
                if t >= T:
                    return t
            return None
        for j in need:
            Dj = int(D[j])
            opts = []
            for i5, s in ((Tb.L[j], Tb.sL[j]), (Tb.R[j], Tb.sF[j])):
                k5 = Tb.k5[i5]; T = Dj - int(s)
                if Tb.floor5[i5] >= T:
                    opts = [(0, 'free', None, None)]; break
                if k5 in chosen5 and chosen5[k5] >= T:
                    opts = [(0, 'have', None, None)]; break
                t = pick(C.get(k5, []), T)
                if t is not None:
                    opts.append((hint(k5) * (0.3 if k5 in chosen5 else 1), '5', k5, t))
            if opts and opts[0][1] in ('free', 'have'):
                continue
            k6 = G['keys6'][j]
            t = pick(C.get(k6, []), Dj)
            if t is not None:
                opts.append((hint(k6), '6', k6, t))
            if not opts:
                miss += 1; continue
            _, kind, k, t = min(opts, key=lambda x: x[0])
            if kind == '5':
                chosen5[k] = max(chosen5.get(k, 0), t)
            else:
                chosen6[k] = t
        # plain 6-window exclusions of this run that are needed
        here = set()
        import gzip
        for l in (open(L.OPL) if os.path.exists(L.OPL) else gzip.open(L.OPL + '.gz', 'rt')):
            r = json.loads(l)
            if r['result'] == 'UNSAT':
                here.add(k6loop.rkey(tuple(r['dirs']), tuple(tuple(a) for a in r['alpha'])))
        livemask = np.zeros(G['n6'], bool); livemask[U] = True; livemask[V] = True
        k6id = {k: j for j, k in enumerate(G['keys6'])}
        exc = ~b5[G['K5']] & b6[G['K6']]
        ex = np.nonzero(exc & livemask[G['U']] & livemask[G['V']])[0]
        neg = q * W6[G['K6'][ex]] - p + pi[G['U'][ex]] - pi[G['V'][ex]] < 0
        plain_needed = {G['keys6'][G['K6'][e]] for e in ex[neg]}
        h5 = sum(hint(k) for k in chosen5); h6 = sum(hint(k) for k in chosen6)
        res['targets'][mt] = dict(reachable=True, lam_star=str(lt), mu_star=float(lt) / 6, demanded_keys=int(len(need)),
                                  certs5=len(chosen5), certs6=len(chosen6), uncovered=miss,
                                  plain6_needed=len(plain_needed), plain6_needed_new=len(plain_needed & here),
                                  est_hints=h5 + h6, est_kernel_h=round((h5 + h6) * RATE, 1),
                                  thresholds5=sorted(chosen5.values())[::max(1, len(chosen5) // 10)],
                                  thresholds6=sorted(chosen6.values())[::max(1, len(chosen6) // 10 or 1)])
        print(mt, json.dumps(res['targets'][mt]), flush=True)
    json.dump(res, open(os.path.join(L.DATA, 'prune.json'), 'w'), indent=1, default=str)


if __name__ == '__main__':
    main()
