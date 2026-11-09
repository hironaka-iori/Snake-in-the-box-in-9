"""Pool keys that might replace an expensive seed through their widened core.

For a seed K (data/seeds.json.gz, full cover) and a known-UNSAT pool key K' (prune234.pool, not in
the key set), E(K') can imply K only if K's window contains K''s window (equal or a sub-window, in
some orientation) and K, K' disagree only at centres that E(K') might widen.  Candidates: pool
keys K' cheaper than K (modelled replay hints) whose window is a sub-window of K's or equal, with
at most `--ham` disagreeing centres.  Their cores are extracted with cores.one, and the seeds whose
E(K') then contains them are reported with the saving.  Output data/poolcand.json, the pool cores
in data/pool_cores.jsonl.

  nice -n 15 python poolcand.py [--ham 2] [--top 300] [--budget 3600]
"""
import sys, os, json, gzip, time, argparse, collections
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import cores as CO       # noqa: E402
import families as FA    # noqa: E402
import prune234 as P234  # noqa: E402
from refine import canon  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--ham', type=int, default=2)
    ap.add_argument('--top', type=int, default=300)
    ap.add_argument('--budget', type=float, default=3600)
    a = ap.parse_args()
    d = json.load(gzip.open(os.path.join(CO.M25, 'data', 'keys_best234.json.gz'), 'rt'))
    inset = {(k[0], tuple(k[1]), tuple(k[2])) for k in d['keys']}
    hints = {(k[0], tuple(k[1]), tuple(k[2])): h for k, h in zip(d['keys'], d['hints'])}
    seeds = [(x[0], tuple(x[1]), tuple(x[2])) for x in
             json.load(gzip.open(os.path.join(HERE, 'data', 'seeds.json.gz'), 'rt'))['full']]
    seeds.sort(key=lambda k: -hints[k])
    S, O, keys6, newk = P234.pool()
    C = P234.Costs(ovh=0.0)
    pool = {}
    for k in keys6:
        kk = ('F' if len(k[0]) == 8 else 'k6', k[0], k[1])
        if kk not in inset:
            pool[kk] = C.k6(k)[0]
    for k in newk:
        if k not in inset:
            pool[k] = C.new(k, O.sec.get(k, 0.05))[0]
    byds = collections.defaultdict(list)
    for k, h in pool.items():
        cs = FA.cons(k[0], k[2])
        byds[k[1]].append((k, cs, h))
    cand = collections.defaultdict(list)     # pool key -> seeds it might replace
    for K in seeds[:a.top]:
        kind, ds, syms = K
        cs = FA.cons(kind, syms)
        n = len(ds)
        for o in (0, 1):
            d2 = ds if o == 0 else tuple(reversed(ds))
            c2 = cs if o == 0 else list(reversed(cs))
            for L in range(3, n + 1):
                for i in range(0, n - L + 1):
                    c = canon(d2[i:i + L])
                    for k2, cs2, h in byds.get(c, ()):
                        if h >= hints[K] or len(cs2) != L - 1:
                            continue
                        diff = sum(1 for x, y in zip(cs2, c2[i:i + L - 1]) if x != y)
                        if diff <= a.ham:
                            cand[k2].append(K)
    print('pool candidates', len(cand), 'seeds touched', len({K for v in cand.values() for K in v}),
          'model hints of candidates', round(sum(pool[k] for k in cand) / 1e6, 1), flush=True)
    out = os.path.join(HERE, 'data', 'pool_cores.jsonl')
    done = {}
    prev = ([json.loads(l) for l in open(out)] if os.path.exists(out) else
            [json.loads(l) for l in gzip.open(out + '.gz', 'rt')] if os.path.exists(out + '.gz') else [])
    for r in prev:
        done[(r['kind'], tuple(r['dirs']), tuple(r['syms']))] = r
    wd = os.path.join(CO.SCR, 'work'); os.makedirs(wd, exist_ok=True)
    order = sorted(cand, key=lambda k: -sum(hints[K] for K in cand[k]) / (pool[k] + 1e3))
    t0 = time.time()
    with open(out, 'a') as f:
        for k in order:
            if k in done:
                continue
            if time.time() - t0 > a.budget or CO.disk_mb() < 300:
                break
            try:
                r = CO.one(k, wd)
            except Exception as e:     # noqa: BLE001
                r = dict(kind=k[0], dirs=list(k[1]), syms=list(k[2]), result='ERROR', err=str(e)[:200])
            r['model_hints'] = pool[k]
            f.write(json.dumps(r, separators=(',', ':')) + '\n'); f.flush()
            done[k] = r
    # which seeds does each pool E replace
    rep = {}
    for k, r in done.items():
        if r.get('result') != 'UNSAT':
            continue
        ds, rng, ab = FA.widened(r)
        Eo = FA.orient(ds, rng)
        for K in cand.get(k, ()):
            kind, kds, syms = K
            cs = FA.cons(kind, syms); n = len(kds)
            ok = False
            for L in range(2, n + 1):
                for i in range(0, n - L + 1):
                    c = canon(kds[i:i + L])
                    for ed, er in Eo:
                        if ed == c and FA.contains(er, cs[i:i + L - 1]):
                            ok = True
            if ok and (K not in rep or pool[k] < rep[K][1]):
                rep[K] = (k, pool[k])
    saved = sum(hints[K] - c for K, (k, c) in rep.items())
    # pool seeds shared by several replaced keys are paid once
    shared = collections.defaultdict(list)
    for K, (k, c) in rep.items():
        shared[k].append(K)
    saved_net = sum(sum(hints[K] for K in Ks) - pool[k] for k, Ks in shared.items())
    res = dict(candidates=len(cand), cores=len(done), replaced_seeds=len(rep), pool_seeds=len(shared),
               hints_replaced=sum(hints[K] for K in rep), hints_saved_net=saved_net, saved_gross=saved,
               examples=[[list(K[1]), list(K[2]), hints[K], [k[0], list(k[1]), list(k[2])], c]
                         for K, (k, c) in sorted(rep.items(), key=lambda x: -hints[x[0]])[:20]])
    json.dump(res, open(os.path.join(HERE, 'data', 'poolcand.json'), 'w'), indent=1)
    print({k: v for k, v in res.items() if k != 'examples'})


if __name__ == '__main__':
    main()
