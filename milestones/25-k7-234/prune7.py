"""Cost-aware pruning of the k7 key set on the full product (k7.py), for the bound 234.

Keys: every known k6 lumped plain-UNSAT key (windows of 3..7 directions, fully counted) and
every UNSAT F8/H9 key of data/oracle_k7.jsonl.gz.  Costs (LRAT hints):
  * k6 keys of the replayed 236/237 sets and of keys_235.json (being certified by the 235
    build): 0;  other k6 keys: full_product/prune.py load_costs (measured / est_r4 / fit);
  * F8/H9 keys: A * seconds^0.843 with A from costs.json (1.49e6), times the calibration
    factor of data/lrat_samples.jsonl (measured / predicted on the samples).
Method (dual reverse-delete, as full_product/prune.py step 1): with the Bellman-Ford
potential pi of the current set (lambda = P/Q, range <= 2^B - 1), a transition of the full
product is critical when Q s - P + pi(u) - pi(v) < 0.  A key may go when every critical
transition it excludes is excluded by another kept key.  The transitions a k6 key excludes
in the k7 product are those whose target state (windows ending at the new vertex) or source
state (the closed-set test of the source's own windows) it hits.  Keys are visited most
expensive first.  pi stays a valid potential for the reduced set, so the bound still holds;
pi is then recomputed and the pass repeated until nothing more goes.

  nice -n 19 python prune7.py LAM TAG [--passes N]
"""
import sys, os, json, time, gzip
sys.dont_write_bytecode = True
import numpy as np
import k7
from k7 import NC, NT, N7, cidx

HERE = k7.HERE
FPD = os.path.join(k7.MS, '23-k6-lean', 'full_product')
A_FIT, B_FIT = 1.49e6, 0.843


BINS = [(0.03, 1.9e3), (0.04, 1.38e4), (0.06, 1.99e4), (0.10, 1.07e5)]   # data/lrat_samples.jsonl


def new_cost(sec):
    """Hints of an F8/H9 key from its own solve time: the mean of the measured samples per
    solve-time bin below 0.1 s (the power fit overestimates trivial proofs 10-100x), the
    k6 fit 1.49e6 t^0.843 above (it matches the 7 samples >= 0.1 s within 0.6-1.3x)."""
    for hi, c in BINS:
        if sec < hi:
            return c
    return A_FIT * sec ** B_FIT


def k6_costs(keys):
    sys.path.insert(0, FPD)
    import prune as PR
    cost, how, cert = PR.load_costs(keys, True)
    free = cert | {PR.lumped_of(d, a) for d, a in json.load(open(os.path.join(FPD, 'keys_235.json')))['keys']}
    for i, k in enumerate(keys):
        if k in free:
            cost[i] = 0; how[i] = 'reuse'
    return cost, how


class Cover:
    """Coverage counts of every transition of the full k7 product by the kept keys."""
    def __init__(self, K):
        self.K = K
        self.cov = np.zeros((K.nX, N7), np.uint16)
        self.src = [[] for _ in range(K.nE)]
        self.tgt = [[] for _ in range(K.nE)]
        for i, (e, e2) in enumerate(K.XE):
            self.src[e].append(i); self.tgt[e2].append(i)
            C = K.Pr.CNT
            v = self.cov[i].reshape(6, NC, 6)
            v += C[e].reshape(6, NC, 1)
            v += C[e2].reshape(1, NC, 6)
            v += K.newcnt[i].reshape(6, NC, 6)

    def slabs6(self, k):
        """Index arrays (X, flat 7-count index) of the transitions a k6 key excludes."""
        out = []
        w = len(k[1])
        base = np.arange(6 ** (6 - w), dtype=np.int64) * 6 ** w
        for e, pat in self.K.Pr.hits(k):
            xs = base + k7.GA.cnt_idx(pat)                  # k6 index = k7 state (a2..a7)
            for i in self.tgt[e]:                           # target state: (a3..a8) = xs
                f = (np.arange(6, dtype=np.int64)[:, None] * NT + xs[None, :]).ravel()
                out.append((i, f))
            for i in self.src[e]:                           # source state: (a2..a7) = xs
                f = (xs[:, None] * 6 + np.arange(6, dtype=np.int64)[None, :]).ravel()
                out.append((i, f))
        return out

    def slabs_new(self, k):
        return [(i, np.array([cidx(c)], np.int64)) for i, c in self.K.hits_new(k)]

    @staticmethod
    def merge(sl):
        """Per X: distinct flat indices and how often this key covers each."""
        by = {}
        for i, f in sl:
            by.setdefault(i, []).append(f)
        out = []
        for i, fs in by.items():
            u, c = np.unique(np.concatenate(fs), return_counts=True)
            out.append((i, u, c.astype(np.uint16)))
        return out


def dead_potential(K, pi, P, Q, L):
    """Dead states (own k6 windows excluded) have no transitions, so their potential is free.
    Give each the value it would get if revived: min over its in-transitions from live states
    (ignoring every test at the target) of pi(u) + Q s - P, clipped to [-L, 0]."""
    w = (Q * np.arange(1, 7) - P).astype(np.int64)
    dm = np.zeros((K.nE, NT), np.int64)
    for i, (e, e2) in enumerate(K.XE):
        c = np.where(K.alive[e].reshape(6, NC, 1), pi[e].reshape(6, NC, 1) + w, 0).min(0).ravel()
        np.minimum(dm[e2], c, out=dm[e2])
    dead = ~K.alive
    pi[dead] = np.clip(dm[dead], -L, 0)


def critical(K, pi, P, Q):
    crit = np.zeros((K.nX, N7), bool)
    w = (Q * np.arange(1, 7) - P)
    for i, (e, e2) in enumerate(K.XE):
        rc = w[None, None, :] + pi[e].reshape(6, NC, 1).astype(np.int64) - pi[e2].reshape(1, NC, 6)
        crit[i] = (rc < 0).ravel()
    return crit


def run(lam, tag, passes=4, start=None):
    P, Q, B = k7.best_pq(lam)
    L = 2 ** B - 1
    S = k7.status()
    keys6 = sorted(S.unsat())
    O = k7.Oracle()
    newk = sorted(k for k, s in O.st.items() if s == 'UNSAT')
    c6, how6 = k6_costs(keys6)
    cf = 'binned'
    cn = np.array([new_cost(O.sec[k]) for k in newk])
    keys = [('k6', k) for k in keys6] + [('new', k) for k in newk]
    cost = np.concatenate([c6, cn])
    kept = np.ones(len(keys), bool)
    if start:                       # start from a pruned set (+ every F8/H9 key)
        d = json.load(gzip.open(os.path.join(HERE, 'data', f'keys_{start}.json.gz'), 'rt'))
        s6 = {(tuple(k[1]), tuple(k[2])) for k in d['keys'] if k[0] == 'k6'}
        kept = np.array([t == 'new' or k in s6 for t, k in keys])
    print(f'lambda {P}/{Q}, B {B}: {len(keys6)} k6 keys ({sum(c6 == 0)} free, {c6.sum() / 1e6:.0f} M), '
          f'{len(newk)} F8/H9 keys ({cn.sum() / 1e6:.0f} M hints, cost model {cf})', flush=True)
    hist = []
    for ps in range(passes):
        K = k7.K7(S, [k for (t, k), m in zip(keys, kept) if m and t == 'k6'])
        for (t, k), m in zip(keys, kept):
            if m and t == 'new':
                K.add_new(k)
        conv, pi, pred, it = K.bf(P, Q, L)
        assert conv and pi.min() >= -L, ('set does not satisfy the target', conv, int(pi.min()))
        dead_potential(K, pi, P, Q, L)
        crit = critical(K, pi, P, Q)
        cv = Cover(K)
        dropped = 0
        t0 = time.time()
        for j in np.argsort(-cost, kind='stable'):
            if not kept[j] or cost[j] == 0:           # free keys stay (no LRAT cost)
                continue
            t, k = keys[j]
            sl = cv.merge(cv.slabs6(k) if t == 'k6' else cv.slabs_new(k))
            if any((crit[i, f] & (cv.cov[i, f] <= c)).any() for i, f, c in sl):
                continue
            for i, f, c in sl:
                cv.cov[i, f] -= c
            kept[j] = False; dropped += 1
        rec = dict(passes=ps, bf_rounds=int(it), range=int(-pi.min()), critical=int(crit.sum()), dropped=dropped,
                   kept=int(kept.sum()), kept_cost=round(float(cost[kept].sum())), seconds=round(time.time() - t0))
        print(json.dumps(rec), flush=True); hist.append(rec)
        del crit, cv, K
        if dropped == 0:
            break
    # final check of the kept set
    K = k7.K7(S, [k for (t, k), m in zip(keys, kept) if m and t == 'k6'])
    for (t, k), m in zip(keys, kept):
        if m and t == 'new':
            K.add_new(k)
    conv, pi, pred, it = K.bf(P, Q, L)
    assert conv and pi.min() >= -L
    ks = [(t, k) for (t, k), m in zip(keys, kept) if m]
    cs = cost[kept]
    summ = dict(tag=tag, P=P, Q=Q, B=B, slack=L / Q, bound=k7.bound(P, Q, B), range=int(-pi.min()),
                keys=len(ks), k6_keys=sum(t == 'k6' for t, _ in ks),
                k6_free=int(sum(1 for (t, _), c in zip(ks, cs) if t == 'k6' and c == 0)),
                k6_new=int(sum(1 for (t, _), c in zip(ks, cs) if t == 'k6' and c > 0)),
                F8=sum(t == 'new' and k[0] == 'F' for t, k in ks), H9=sum(t == 'new' and k[0] == 'H' for t, k in ks),
                hints_k6=round(float(sum(c for (t, _), c in zip(ks, cs) if t == 'k6'))),
                hints_new=round(float(sum(c for (t, _), c in zip(ks, cs) if t == 'new'))),
                calibration=cf, passes=hist)
    summ['hints'] = summ['hints_k6'] + summ['hints_new']
    summ['kernel_hours'] = round(summ['hints'] * 0.42e-3 / 3600, 1)
    print(json.dumps(summ), flush=True)
    out = dict(summary=summ, keys=[[k[0], list(k[1]), list(k[2])] if t == 'new' else ['k6', list(k[0]), list(k[1])]
                                   for t, k in ks],
               cost=[round(float(c)) for c in cs])
    with gzip.open(os.path.join(HERE, 'data', f'keys_{tag}.json.gz'), 'wt') as f:
        json.dump(out, f)
    json.dump(summ, open(os.path.join(HERE, 'data', f'prune_{tag}.json'), 'w'), indent=1)
    return summ


if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('lam', type=float)
    ap.add_argument('tag')
    ap.add_argument('--passes', type=int, default=4)
    ap.add_argument('--start', default=None, help='TAG of a pruned set to start from')
    a = ap.parse_args()
    run(a.lam, a.tag, a.passes, a.start)
