"""Cost-aware pruning of the k7 key set for 234 with MEASURED replay costs (cost234/measure234).

Pool: every known k6 lumped plain-UNSAT key (k7.status) + the k6 keys decided here
(data/decide234.jsonl: one-step extensions of expensive keys), every UNSAT F8/H9 key of
data/oracle_k7.jsonl.gz + those decided here (data/oracle234.jsonl.gz).

Cost of a key = replay hints + per-key overhead (Cnf + Sat module and process: OVH_CL hint
equivalents per core clause + OVH_KEY per key; --ovh 0 for the pure hint objective).
  * replay hints/core: data/replay234.jsonl (measured, cost234.replay_cost) when present;
  * otherwise the model of model234.json (fits on the measured records, see fit());
  * k6 keys of the replayed 236/237/235 sets: 0.
Method: prune7's dual reverse-delete on the full product, repeated; then a final BF check.

  nice -n 10 python prune234.py fit
  nice -n 10 python prune234.py prune LAM TAG [--start TAG0] [--ovh 1] [--passes 4]
"""
import sys, os, json, time, gzip
sys.dont_write_bytecode = True
import numpy as np
import k7
import prune7 as PR7

HERE = k7.HERE
D = os.path.join(HERE, 'data')
REPLAY = os.path.join(D, 'replay234.jsonl')
DECIDE = os.path.join(D, 'decide234.jsonl')
ORACLE234 = os.path.join(D, 'oracle234.jsonl.gz')
MODEL = os.path.join(D, 'model234.json')
OVH_CL, OVH_KEY = 40.0, 5000.0
SBINS = [0.03, 0.05, 0.1, 0.2, 0.5, 1, 2, 5, 1e9]


def kk(r):
    return (r['kind'], tuple(r['dirs']), tuple(r['syms']))


def measured():
    out = {}
    if os.path.exists(REPLAY):
        for l in open(REPLAY):
            r = json.loads(l)
            if r.get('hints') is not None:
                out[kk(r)] = r
    return out


class Oracle(k7.Oracle):
    """oracle_k7 (read) + oracle234 (read/write)."""
    def __init__(self):
        super().__init__()
        for f in (ORACLE234,):
            if os.path.exists(f):
                for l in gzip.open(f, 'rt'):
                    r = json.loads(l)
                    k = kk(r); self.st[k] = r['result']; self.sec[k] = r['seconds']
        if os.path.exists(DECIDE):
            for l in open(DECIDE):
                r = json.loads(l)
                if r['kind'] == 'H':
                    k = kk(r); self.st[k] = r['result']; self.sec[k] = r['seconds']

    def flush(self):
        if self.buf:
            with gzip.open(ORACLE234, 'at') as f:
                for r in self.buf:
                    f.write(json.dumps(r) + '\n')
            self.buf = []


def extra_k6():
    """UNSAT k6 keys decided here, with their own solve times."""
    out = {}
    if os.path.exists(DECIDE):
        for l in open(DECIDE):
            r = json.loads(l)
            if r['kind'] == 'k6' and r['result'] == 'UNSAT':
                out[(tuple(r['dirs']), tuple(r['syms']))] = r['seconds']
    return out


def sbin(t):
    for i, hi in enumerate(SBINS):
        if t < hi:
            return i


def fit():
    """Model of unmeasured keys from the measured ones: per kind and own-solve-time bin, the
    mean replay hints and mean core size; plus the mean of k6 keys without an own solve time
    (class 'median') and the ratio measured / est_r4."""
    M = measured()
    sys.path.insert(0, PR7.FPD)
    import prune as PR
    sec = PR.seconds_map(); sec.update(extra_k6())
    O = Oracle()
    est = {}
    for l in open(os.path.join(PR.D10, 'est_hints_r4.jsonl')):
        r = json.loads(l); k = PR.lumped_of(r['dirs'], r['alpha'])
        if k:
            est[k] = r['proof_lines']
    acc = {}
    r4 = []
    for k, r in M.items():
        if k[0] == 'k6':
            kk6 = (k[1], k[2])
            t = sec.get(kk6)
            cl = f'k6_{len(k[2])}_' + ('none' if t is None else str(sbin(t)))
            if kk6 in est:
                r4.append((r['hints'], est[kk6]))
        else:
            t = O.sec.get(k)
            cl = 'H_' + ('none' if t is None else str(sbin(t)))
        a = acc.setdefault(cl, [0, 0.0, 0.0])
        a[0] += 1; a[1] += r['hints']; a[2] += r['core']
    model = {cl: dict(n=a[0], hints=a[1] / a[0], core=a[2] / a[0]) for cl, a in sorted(acc.items())}
    out = dict(classes=model, r4_ratio=(sum(a for a, _ in r4) / sum(b for _, b in r4)) if r4 else 1.0, r4_n=len(r4))
    json.dump(out, open(MODEL, 'w'), indent=1)
    for cl, v in model.items():
        print(cl, v)
    print('r4 ratio', out['r4_ratio'], len(r4))
    return out


class Costs:
    def __init__(self, ovh=1.0):
        self.M = measured()
        self.model = json.load(open(MODEL)) if os.path.exists(MODEL) else dict(classes={}, r4_ratio=1.0)
        sys.path.insert(0, PR7.FPD)
        import prune as PR
        self.PR = PR
        self.sec6 = PR.seconds_map(); self.sec6.update(extra_k6())
        self.ovh = ovh
        self.est = {}
        for l in open(os.path.join(PR.D10, 'est_hints_r4.jsonl')):
            r = json.loads(l); k = PR.lumped_of(r['dirs'], r['alpha'])
            if k:
                self.est[k] = r['proof_lines']
        self.free = set(k7.free_keys())

    def cls(self, cl, fallback):
        c = self.model['classes'].get(cl)
        if c is None or c['n'] < 5:
            return fallback
        return c['hints'], c['core'], 'model'

    def k6(self, k):
        """(hints, core, basis) of a k6 lumped key."""
        if k in self.free:
            return 0.0, 0.0, 'reuse'
        r = self.M.get(('k6',) + k)
        if r is not None:
            return float(r['hints']), float(r['core']), 'measured'
        n = len(k[1]); t = self.sec6.get(k)
        if k in self.est and t is None:
            return self.est[k] * self.model.get('r4_ratio', 1.0), 3000.0, 'est_r4'
        if t is None:
            h, c, b = self.cls(f'k6_{n}_none', (1.13e6, 2000.0, 'prior'))
            return h, c, 'median_' + b
        fb = (1.49e6 * max(t, 0.01) ** 0.843, 2000.0, 'fit')
        h, c, b = self.cls(f'k6_{n}_{sbin(t)}', fb)
        if b == 'model' and k in self.est:     # an est_r4 key with an own time: keep the larger
            h = max(h, 0.0)
        return h, c, 'seconds_' + b

    def new(self, k, sec):
        r = self.M.get(k)
        if r is not None:
            return float(r['hints']), float(r['core']), 'measured'
        h, c, b = self.cls(f'H_{sbin(sec)}', (PR7.new_cost(sec), 600.0, 'binned'))
        return h, c, 'model' if b == 'model' else b

    def eff(self, h, c, basis):
        if basis == 'reuse':
            return 0.0
        return h + self.ovh * (OVH_CL * c + OVH_KEY)


def pool(S=None, O=None):
    S = S or k7.status()
    O = O or Oracle()
    keys6 = sorted(set(S.unsat()) | set(extra_k6()))
    newk = sorted(k for k, s in O.st.items() if s == 'UNSAT')
    return S, O, keys6, newk


def build(S, keys, kept):
    K = k7.K7(S, [k for (t, k), m in zip(keys, kept) if m and t == 'k6'])
    for (t, k), m in zip(keys, kept):
        if m and t == 'new':
            K.add_new(k)
    return K


def run(lam, tag, passes=4, start=None, ovh=1.0, pq=None):
    P, Q, B = pq if pq else k7.best_pq(lam)
    L = 2 ** B - 1
    S, O, keys6, newk = pool()
    C = Costs(ovh)
    rows = [C.k6(k) for k in keys6] + [C.new(k, O.sec[k]) for k in newk]
    keys = [('k6', k) for k in keys6] + [('new', k) for k in newk]
    hints = np.array([r[0] for r in rows]); core = np.array([r[1] for r in rows])
    basis = [r[2] for r in rows]
    cost = np.array([C.eff(*r) for r in rows])
    kept = np.ones(len(keys), bool)
    if start:
        d = json.load(gzip.open(os.path.join(D, f'keys_{start}.json.gz'), 'rt'))
        s6 = {(tuple(k[1]), tuple(k[2])) for k in d['keys'] if k[0] == 'k6'}
        kept = np.array([t == 'new' or k in s6 for t, k in keys])
        if '--start-strict' in sys.argv:
            sn = {kk(dict(kind=k[0], dirs=k[1], syms=k[2])) for k in d['keys'] if k[0] != 'k6'}
            kept = np.array([(k in sn) if t == 'new' else (k in s6) for t, k in keys])
    print(f'lambda {P}/{Q} = {P / Q:.5f}, B {B}: pool {len(keys6)} k6 + {len(newk)} F8/H9; ovh {ovh}', flush=True)
    hist = []
    for ps in range(passes):
        K = build(S, keys, kept)
        conv, pi, pred, it = K.bf(P, Q, L)
        assert conv and pi.min() >= -L, ('set does not satisfy the target', conv, int(pi.min()))
        PR7.dead_potential(K, pi, P, Q, L)
        crit = PR7.critical(K, pi, P, Q)
        cv = PR7.Cover(K)
        dropped = 0
        t0 = time.time()
        for j in np.argsort(-cost, kind='stable'):
            if not kept[j] or cost[j] == 0:
                continue
            t, k = keys[j]
            sl = cv.merge(cv.slabs6(k) if t == 'k6' else cv.slabs_new(k))
            if any((crit[i, f] & (cv.cov[i, f] <= c)).any() for i, f, c in sl):
                continue
            for i, f, c in sl:
                cv.cov[i, f] -= c
            kept[j] = False; dropped += 1
        rec = dict(passes=ps, bf_rounds=int(it), range=int(-pi.min()), dropped=dropped, kept=int(kept.sum()),
                   kept_cost=round(float(cost[kept].sum())), seconds=round(time.time() - t0))
        print(json.dumps(rec), flush=True); hist.append(rec)
        del crit, cv, K
        if dropped == 0:
            break
    K = build(S, keys, kept)
    conv, pi, pred, it = K.bf(P, Q, L)
    assert conv and pi.min() >= -L
    return save(tag, P, Q, B, int(-pi.min()), keys, kept, hints, core, basis, cost, hist, ovh)


def save(tag, P, Q, B, rng, keys, kept, hints, core, basis, cost, hist, ovh):
    idx = np.flatnonzero(kept)
    by = {}
    for j in idx:
        b = basis[j].split('_')[0] if basis[j] != 'reuse' else 'reuse'
        t = keys[j][0] if keys[j][0] == 'k6' else 'H9'
        a = by.setdefault(f'{t}:{b}', [0, 0.0, 0.0])
        a[0] += 1; a[1] += hints[j]; a[2] += core[j] if basis[j] != 'reuse' else 0
    paid = [j for j in idx if basis[j] != 'reuse']
    H = float(hints[paid].sum()); CL = float(core[paid].sum())
    summ = dict(tag=tag, P=P, Q=Q, B=B, lam=P / Q, slack=(2 ** B - 1) / Q, bound=k7.bound(P, Q, B), range=rng,
                keys=len(idx), k6=sum(keys[j][0] == 'k6' for j in idx), H9=sum(keys[j][0] == 'new' for j in idx),
                paid_keys=len(paid), hints=round(H), core_clauses=round(CL),
                hints_measured=round(float(sum(hints[j] for j in paid if basis[j] == 'measured'))),
                kernel_hours_hints=round(H * 0.42e-3 / 3600, 1),
                olean_GB_hints=round(H * 10 / 1e9, 1),
                overhead_hint_eq=round(OVH_CL * CL + OVH_KEY * len(paid)),
                objective=round(float(cost[idx].sum())), ovh=ovh,
                by_basis={b: dict(keys=a[0], hints=round(a[1]), core=round(a[2])) for b, a in sorted(by.items())},
                passes=hist)
    print(json.dumps(summ), flush=True)
    out = dict(summary=summ,
               keys=[['k6', list(keys[j][1][0]), list(keys[j][1][1])] if keys[j][0] == 'k6'
                     else [keys[j][1][0], list(keys[j][1][1]), list(keys[j][1][2])] for j in idx],
               hints=[round(float(hints[j])) for j in idx], core=[round(float(core[j])) for j in idx],
               basis=[basis[j] for j in idx])
    with gzip.open(os.path.join(D, f'keys_{tag}.json.gz'), 'wt') as f:
        json.dump(out, f)
    json.dump(summ, open(os.path.join(D, f'prune_{tag}.json'), 'w'), indent=1)
    return summ


def recost(tag, ovh=1.0):
    """Re-cost an existing key set with the current measurements/model (no pruning)."""
    d = json.load(gzip.open(os.path.join(D, f'keys_{tag}.json.gz'), 'rt'))
    C = Costs(ovh); O = Oracle()
    keys, rows = [], []
    for k in d['keys']:
        if k[0] == 'k6':
            key = (tuple(k[1]), tuple(k[2])); keys.append(('k6', key)); rows.append(C.k6(key))
        else:
            key = (k[0], tuple(k[1]), tuple(k[2])); keys.append(('new', key)); rows.append(C.new(key, O.sec.get(key, 0.05)))
    s = d['summary']
    hints = np.array([r[0] for r in rows]); core = np.array([r[1] for r in rows]); basis = [r[2] for r in rows]
    cost = np.array([C.eff(*r) for r in rows])
    return save(tag + '_recost', s['P'], s['Q'], s['B'], s['range'], keys, np.ones(len(keys), bool), hints, core, basis,
                cost, [], ovh)


if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('cmd'); ap.add_argument('lam', nargs='?', type=float); ap.add_argument('tag', nargs='?')
    ap.add_argument('--passes', type=int, default=4)
    ap.add_argument('--start', default=None)
    ap.add_argument('--start-strict', action='store_true')
    ap.add_argument('--ovh', type=float, default=1.0)
    ap.add_argument('--pq', default=None, help='P/Q/B explicitly')
    a = ap.parse_args()
    if a.cmd == 'fit':
        fit()
    elif a.cmd == 'recost':
        recost(a.tag, a.ovh)
    else:
        run(a.lam, a.tag, a.passes, a.start, a.ovh, tuple(map(int, a.pq.split('/'))) if a.pq else None)
