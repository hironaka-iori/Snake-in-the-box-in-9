"""Exact drops (milestone 23 prune.py step 2, on the k7 full product): try to remove each
expensive key of a set, most expensive first; the removal stands when a Bellman-Ford warm
started from the current potential (a valid upper bound, since removing a key only adds
transitions; revived states start at 0) still converges with min >= -(2^B - 1).
Stronger than the dual cover test of prune7, since the potential may move.

  nice -n 10 python exact234.py TAG NEWTAG [--min COST] [--hours H] [--ovh 1]
"""
import sys, os, json, time, gzip, argparse
sys.dont_write_bytecode = True
import numpy as np
import k7
import prune234 as P4
from k7 import NC, NT


def bf_warm(K, masks, pi, dirty, P, Q, L, maxit=4000):
    w = (Q * np.arange(1, 7) - P).astype(np.int32)
    BIG = np.int32(2 ** 30)
    for it in range(maxit):
        nd = np.zeros(K.nE, bool)
        for i in range(K.nX):
            e, e2 = K.XE[i]
            if not dirty[e]:
                continue
            cand = np.where(masks[i], pi[e].reshape(6, NC, 1) + w, BIG).min(0)
            tgt = pi[e2].reshape(NC, 6)
            upd = cand < tgt
            if upd.any():
                tgt[upd] = cand[upd]
                nd[e2] = True
        dirty = nd
        if not nd.any():
            return True, it
        if pi.min() < -L:
            return False, it
    return False, maxit


def apply6(Pr, k, delta):
    w = len(k[1])
    for e, pat in Pr.hits(k):
        A = Pr.CNT[e].reshape((6,) * 6)
        ix = (slice(None),) * (6 - w) + tuple(p - 1 for p in pat)
        if delta > 0:
            A[ix] += 1
        else:
            A[ix] -= 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('tag'); ap.add_argument('newtag')
    ap.add_argument('--min', type=float, default=1e6); ap.add_argument('--hours', type=float, default=2)
    ap.add_argument('--ovh', type=float, default=1.0)
    a = ap.parse_args()
    t0 = time.time()
    d = json.load(gzip.open(os.path.join(P4.D, f'keys_{a.tag}.json.gz'), 'rt'))
    s = d['summary']; P, Q, B = s['P'], s['Q'], s['B']; L = 2 ** B - 1
    S = k7.status(); O = P4.Oracle(); C = P4.Costs(a.ovh)
    keys, rows = [], []
    for k in d['keys']:
        if k[0] == 'k6':
            key = (tuple(k[1]), tuple(k[2])); keys.append(('k6', key)); rows.append(C.k6(key))
        else:
            key = (k[0], tuple(k[1]), tuple(k[2])); keys.append(('new', key)); rows.append(C.new(key, O.sec.get(key, 0.05)))
    hints = np.array([r[0] for r in rows]); core = np.array([r[1] for r in rows]); basis = [r[2] for r in rows]
    cost = np.array([C.eff(*r) for r in rows])
    kept = np.ones(len(keys), bool)
    K = P4.build(S, keys, kept)
    conv, pi, pred, it = K.bf(P, Q, L)
    assert conv and pi.min() >= -L
    del pred
    masks = [K.mask(i) for i in range(K.nX)]
    bysrc = [[] for _ in range(K.nE)]; bytgt = [[] for _ in range(K.nE)]
    for i, (e, e2) in enumerate(K.XE):
        bysrc[e].append(i); bytgt[e2].append(i)
    order = [j for j in np.argsort(-cost, kind='stable') if cost[j] >= a.min]
    print(f'{len(order)} keys >= {a.min:.0f} ({cost[order].sum() / 1e9:.2f} G eff); start range {int(-pi.min())}', flush=True)
    dropped = saved = 0
    log = []
    for n, j in enumerate(order):
        if time.time() - t0 > a.hours * 3600:
            break
        t, k = keys[j]
        tt = time.time()
        if t == 'k6':
            E = sorted({e for e, _ in K.Pr.hits(k)})
            old_alive = K.alive[E].copy()
            apply6(K.Pr, k, -1)
            K.alive[E] = K.Pr.CNT[E] == 0
            aff = sorted({i for e in E for i in bysrc[e] + bytgt[e]})
            revived = [(e, np.flatnonzero(K.alive[e] & ~oa)) for e, oa in zip(E, old_alive)]
        else:
            hs = K.hits_new(k)
            for i, c in hs:
                K.newcnt[i, k7.cidx(c)] -= 1
            aff = sorted({i for i, _ in hs}); E = []; revived = []
        old_masks = {i: masks[i] for i in aff}
        for i in aff:
            masks[i] = K.mask(i)
        pi2 = pi.copy()
        dirty = np.zeros(K.nE, bool)
        for e, idx in revived:
            pi2[e, idx] = 0
            dirty[e] = True
        for i in aff:
            dirty[K.XE[i][0]] = True
        ok, its = bf_warm(K, masks, pi2, dirty, P, Q, L)
        if ok:
            pi = pi2; kept[j] = False; dropped += 1; saved += cost[j]
            if t == 'new':
                K.newkeys.discard(k)
        else:
            if t == 'k6':
                apply6(K.Pr, k, 1); K.alive[E] = K.Pr.CNT[E] == 0
            else:
                for i, c in hs:
                    K.newcnt[i, k7.cidx(c)] += 1
            for i in aff:
                masks[i] = old_masks[i]
        log.append(dict(key=[t, [list(x) for x in k]], cost=round(float(cost[j])), dropped=bool(ok), its=its,
                        s=round(time.time() - tt, 1)))
        if n < 30 or n % 50 == 0:
            print(f'{n}: {log[-1]} | dropped {dropped}, saved {saved / 1e9:.3f} G, {time.time() - t0:.0f}s', flush=True)
    # final check from scratch
    K2 = P4.build(S, keys, kept)
    conv, pi, pred, it = K2.bf(P, Q, L)
    assert conv and pi.min() >= -L, 'final check failed'
    P4.save(a.newtag, P, Q, B, int(-pi.min()), keys, kept, hints, core, basis, cost,
            [dict(exact_from=a.tag, tried=len(log), dropped=dropped, saved=round(float(saved)))], a.ovh)
    json.dump(log, open(os.path.join(P4.D, f'exact234_{a.newtag}.json'), 'w'))


if __name__ == '__main__':
    main()
