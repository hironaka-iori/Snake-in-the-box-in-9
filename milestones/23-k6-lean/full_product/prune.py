"""Cost-aware pruning of the plain exclusion keys on the FULL k6 product (fp.py).

Goal: a cheap key set K such that the Lean k6 step check holds with lambda = 4 and a
potential of range <= LIM (= 7, 3 bits), i.e. Bellman-Ford with weights s - 4 on the
transitions of the full product that no key of K excludes converges with min >= -LIM.

Costs (estimated LRAT hints of a key's certificate):
  * keys of the replayed 236/237 sets (direction_certificates_r4b/r4c.json) cost 0 with
    --reuse (their LRAT modules already exist), else their table value;
  * radius-4 cache keys: data/est_hints_r4.jsonl of milestone 10 (measured or fitted);
  * other keys: hints = A * seconds^B per centre class (fit in costs.json, from the LRAT
    samples of k6_loop and of this directory), seconds = the key's own plain solve time
    (k6loop record format; samples.jsonl / verify.jsonl of this directory first);
  * keys without an own solve (members of a range certificate, 'derived'): the class median.

Method:
  1. dual pruning: with a potential pi, an excluded transition with s - 4 + pi[u] - pi[v] < 0
     is critical; K must hit every critical transition.  Weighted greedy hitting set (lazy
     cost/coverage), reverse delete; recompute pi (Bellman-Ford) and repeat until stable;
  2. exact drops: keys of K in decreasing cost order, each removed when a warm-started
     Bellman-Ford on the enlarged graph still converges with min >= -LIM.
Writes keys_<tag>.json ({"keys": [[dirs, alpha]]}, the generator's format) and prune_<tag>.json.

usage: nice -n 19 python prune.py TAG [--reuse] [--drop-budget SECONDS] [--from KEYS.json]
"""
import sys, os, json, time, heapq, argparse, glob, gzip
sys.dont_write_bytecode = True
import numpy as np
import fp
from fp import NT, LIM, LUMP, lkey

HERE = fp.HERE; MS = fp.MS
D10 = os.path.join(MS, '10-window-aggregate', 'data')


def lumped_of(dirs, alpha):
    ch = [fp.lumped_choices(tuple(a)) for a in alpha]
    if all(len(c) == 1 and LUMP[c[0]] == tuple(a) for c, a in zip(ch, alpha)):
        return lkey(tuple(dirs), tuple(c[0] for c in ch))
    return None


def certified():
    out = set()
    for f in ('direction_certificates_r4b.json', 'direction_certificates_r4c.json'):
        for c in json.load(open(os.path.join(D10, f)))['cases']:
            if c['drat_trim_verified'] and c['radius'] == 4:
                k = lumped_of(c['dirs'], c['alpha'])
                if k:
                    out.add(k)
    return out


def seconds_map():
    """Own plain solve time of every lumped key (latest record wins; our verify/samples last)."""
    sec = {}
    files = [os.path.join(MS, '11-local-ceiling', 's0_share_loop', 'share_oracle.jsonl'),
             os.path.join(MS, '11-local-ceiling', 's0_k6_ceiling', 'oracle5_extra.jsonl'),
             os.path.join(MS, '11-local-ceiling', 's0_k6_ceiling', 'oracle6.jsonl'),
             os.path.join(MS, '11-local-ceiling', 'k6_loop', 'oracle_plain.jsonl'),
             os.path.join(MS, '22-global-arguments', 'k6_w3', 'data', 'plain_k6w3.jsonl'),
             os.path.join(MS, '22-global-arguments', 'k6_w3_loop', 'data', 'plain_loop.jsonl.gz'),
             fp.ORACLE, os.path.join(HERE, 'verify.jsonl')]
    for f in files:
        if not os.path.exists(f):
            continue
        for l in (gzip.open(f, 'rt') if f.endswith('.gz') else open(f)):
            r = json.loads(l)
            if r.get('kind') != 'plain' or r.get('result') != 'UNSAT' or r.get('src') == 'range' \
                    or r.get('seconds') is None or r.get('T') is not None:
                continue
            k = lumped_of(r['dirs'], r['alpha'])
            if k:
                sec[k] = float(r['seconds'])
    return sec


def load_costs(keys, reuse):
    cfit = json.load(open(os.path.join(HERE, 'costs.json')))
    cert = certified()
    est = {}
    for l in open(os.path.join(D10, 'est_hints_r4.jsonl')):
        r = json.loads(l)
        k = lumped_of(r['dirs'], r['alpha'])
        if k:
            est[k] = r['proof_lines']
    sec = seconds_map()
    meas = {}
    if os.path.exists(os.path.join(HERE, 'samples.jsonl')):
        for l in open(os.path.join(HERE, 'samples.jsonl')):
            r = json.loads(l)
            if r.get('hints') is not None:
                meas[lumped_of(r['dirs'], r['alpha'])] = r['hints']
    cost = np.zeros(len(keys)); how = []
    for i, k in enumerate(keys):
        c = str(len(k[1]))
        f = cfit.get(c, cfit['6'])
        if reuse and k in cert:
            cost[i] = 0; how.append('reuse')
        elif k in meas:
            cost[i] = meas[k]; how.append('measured')
        elif k in est:
            cost[i] = est[k]; how.append('est_r4')
        elif k in sec:
            cost[i] = f['A'] * max(sec[k], 0.01) ** f['B'] + f['C']; how.append('seconds')
        else:
            cost[i] = f['median']; how.append('median')
    return cost, how, cert


class Net:
    """All transitions of the full product, sorted by target, with exclusion counts."""
    def __init__(self, Pr):
        self.Pr = Pr
        g = np.arange(Pr.nE * NT, dtype=np.int64)
        u, v, s = Pr.uvw(g)
        o = np.argsort(v, kind='stable')
        self.g = g[o]; self.u = u[o].astype(np.int32); self.v = v[o].astype(np.int32)
        self.w = (s[o] - 4).astype(np.int32)
        self.pos = np.empty_like(o); self.pos[o] = np.arange(len(o))
        self.uv, self.starts = np.unique(self.v, return_index=True)
        self.cnt = np.zeros(len(o), np.int32)
        self.BIG = np.int32(1 << 20)

    def bf(self, pi=None, maxit=3000):
        """Warm-startable Bellman-Ford on cnt == 0.  Returns (ok, pi)."""
        n = self.Pr.n
        pi = np.zeros(n, np.int32) if pi is None else pi.copy()
        w = np.where(self.cnt == 0, self.w, self.BIG)
        for it in range(maxit):
            cand = pi[self.u] + w
            mins = np.minimum.reduceat(cand, self.starts)
            upd = mins < pi[self.uv]
            if not upd.any():
                return pi.min() >= -LIM, pi
            pi[self.uv[upd]] = mins[upd]
            if pi.min() < -LIM:
                return False, pi
        return False, pi


def greedy(elems_of, cost, cand, nel):
    """Weighted greedy hitting set of nel elements by the candidate keys; then reverse delete."""
    covered = np.zeros(nel, bool)
    heap = []
    for i in cand:
        e = elems_of[i]
        if len(e):
            heapq.heappush(heap, (cost[i] / len(e), i))
    chosen = []
    while heap and not covered.all():
        r, i = heapq.heappop(heap)
        e = elems_of[i]; new = int((~covered[e]).sum())
        if new == 0:
            continue
        rr = cost[i] / new
        if heap and rr > heap[0][0] + 1e-12:
            heapq.heappush(heap, (rr, i)); continue
        chosen.append(i); covered[e] = True
    assert covered.all(), 'cannot cover the critical transitions'
    mult = np.zeros(nel, np.int32)
    for i in chosen:
        mult[elems_of[i]] += 1
    keep = []
    for i in sorted(chosen, key=lambda i: -cost[i]):
        e = elems_of[i]
        if len(e) and (mult[e] >= 2).all():
            mult[e] -= 1
        else:
            keep.append(i)
    return keep


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('tag'); ap.add_argument('--reuse', action='store_true')
    ap.add_argument('--drop-budget', type=float, default=3600)
    ap.add_argument('--from', dest='frm')
    a = ap.parse_args()
    t0 = time.time()
    S = fp.Status(); Pr = fp.Product()
    keys = sorted(S.unsat(), key=lambda k: (len(k[0]), k))
    cost, how, cert = load_costs(keys, a.reuse)
    N = Net(Pr)
    ek = [N.pos[Pr.edges_of(k)] for k in keys]           # positions in the sorted transition list
    kept = np.ones(len(keys), bool)
    if a.frm:
        want = {lumped_of(d, al) for d, al in json.load(open(a.frm))['keys']}
        kept = np.array([k in want for k in keys])
    for i in np.flatnonzero(kept):
        np.add.at(N.cnt, ek[i], 1)
    ok, pi = N.bf()
    print(f'{len(keys)} keys, {kept.sum()} start, cost {cost[kept].sum()/1e6:.0f} M hints; start feasible {ok} '
          f'range {-pi.min()}  [{time.time()-t0:.0f}s, rss {fp.rss_mb():.0f} MB]', flush=True)
    assert ok
    # ---------------- 1. dual pruning
    for sweep in range(20):
        exc = N.cnt > 0
        sl = N.w + pi[N.u] - pi[N.v]
        crit = np.flatnonzero(exc & (sl < 0))
        emap = np.full(len(N.cnt), -1, np.int64); emap[crit] = np.arange(len(crit))
        cand = np.flatnonzero(kept)
        elems = {}
        for i in cand:
            e = emap[ek[i]]; elems[i] = e[e >= 0]
        keep = greedy(elems, cost, cand, len(crit))
        newk = np.zeros(len(keys), bool); newk[keep] = True
        for i in np.flatnonzero(kept & ~newk):
            np.subtract.at(N.cnt, ek[i], 1)
        changed = (newk != kept).any()
        kept = newk
        ok, pi2 = N.bf(pi)            # pi stays feasible: warm start from it
        assert ok, 'dual pruning broke feasibility'
        ok, pi = N.bf()               # least-range potential of the new graph
        print(f' sweep {sweep}: critical {len(crit)}, kept {kept.sum()}, cost {cost[kept].sum()/1e6:.0f} M, '
              f'range {-pi.min()}  [{time.time()-t0:.0f}s]', flush=True)
        if not changed:
            break
    # ---------------- 2. exact drops, most expensive first
    t1 = time.time(); tried = dropped = 0
    order = sorted(np.flatnonzero(kept), key=lambda i: -cost[i])
    for i in order:
        if time.time() - t1 > a.drop_budget:
            break
        if cost[i] <= 0:
            continue
        tried += 1
        np.subtract.at(N.cnt, ek[i], 1)
        ok, pi2 = N.bf(pi)
        if ok:
            kept[i] = False; pi = pi2; dropped += 1
        else:
            np.add.at(N.cnt, ek[i], 1)
        if tried % 100 == 0:
            print(f'  drops: tried {tried}, dropped {dropped}, kept {kept.sum()}, cost {cost[kept].sum()/1e6:.0f} M '
                  f'[{time.time()-t0:.0f}s]', flush=True)
    # free keys (cost 0) last: fewer keys means smaller tables and cover module
    t2 = time.time(); fdrop = 0
    for i in [i for i in np.flatnonzero(kept) if cost[i] <= 0]:
        if time.time() - t2 > a.drop_budget:
            break
        np.subtract.at(N.cnt, ek[i], 1)
        ok, pi2 = N.bf(pi)
        if ok:
            kept[i] = False; pi = pi2; fdrop += 1
        else:
            np.add.at(N.cnt, ek[i], 1)
    print(f'  free keys dropped: {fdrop}', flush=True)
    ok, pi = N.bf()
    assert ok
    ks = [keys[i] for i in np.flatnonzero(kept)]
    byc = {}; byhow = {}; srcs = {}
    for i in np.flatnonzero(kept):
        c = len(keys[i][1]); byc[c] = byc.get(c, 0) + 1
        byhow[how[i]] = byhow.get(how[i], 0) + 1
        srcs[S.src[keys[i]]] = srcs.get(S.src[keys[i]], 0) + 1
    out = dict(tag=a.tag, reuse=a.reuse, kept=len(ks), by_centres=byc, cost_basis=byhow, by_source=srcs,
               reused_certified=int(sum(1 for k in ks if k in cert)),
               hints_total=float(cost[kept].sum()), potential_range=int(-pi.min()), lam='4', lim=LIM,
               exact_tried=tried, exact_dropped=dropped, free_dropped=fdrop,
               hints_without_reuse=float(load_costs([keys[i] for i in np.flatnonzero(kept)], False)[0].sum()), seconds=round(time.time() - t0))
    print(json.dumps(out), flush=True)
    json.dump(out, open(os.path.join(HERE, f'prune_{a.tag}.json'), 'w'), indent=1)
    json.dump(dict(keys=[[list(d), [list(LUMP[x]) for x in t]] for d, t in ks]),
              open(os.path.join(HERE, f'keys_{a.tag}.json'), 'w'))


if __name__ == '__main__':
    main()
