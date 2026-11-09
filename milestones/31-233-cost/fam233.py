"""Families L1/L2 (milestone 30, work/final_lean/LocalWindowFamilies.lean) on a 233 set's paid plain keys.

Cores: milestone 30's data/cores.jsonl.gz (the 234 set's keys) plus this milestone's
data/cores233.jsonl.gz, computed here with milestone 30's cores.one (CaDiCaL --unsat --lrat through a
FIFO into lrattrim; no proof on disk), for the members of L1 sibling groups (same window, the
largest groups by hints first) within a time budget.  Then milestone 30's construction: widened key
E(K) from K's core, implication of K2 by E(K) (L1: same window and orientation; L2: any slice, either
orientation), weighted greedy set cover with cost = hints (+5 k per seed).
Share thresholds are not widened (no share analogue of refuted_narrow exists yet).

usage: fam233.py TAG [BUDGET_S]      -> data/fam_TAG.json
"""
import sys, os, json, gzip, time, collections
import lib233 as L
M30 = os.path.join(L.MS, '30-certificate-families')
os.environ.setdefault('FAM_SCR', L.SCR)
sys.path.insert(0, M30)
import cores as CR        # noqa: E402
import families as FA     # noqa: E402
CR.TRIM = os.path.join(L.SCR, 'bin', 'lrattrim')
OUT = os.path.join(L.D, 'cores233.jsonl')


def load_cores():
    recs = {}
    for r in CR.records():
        recs[(r['kind'], tuple(r['dirs']), tuple(r['syms']))] = r
    for f in (OUT + '.gz', OUT):
        if os.path.exists(f):
            for l in (gzip.open(f, 'rt') if f.endswith('.gz') else open(f)):
                r = json.loads(l); recs[(r['kind'], tuple(r['dirs']), tuple(r['syms']))] = r
    return recs


def main():
    tag = sys.argv[1]; budget = float(sys.argv[2]) if len(sys.argv) > 2 else 0
    d = json.load(gzip.open(os.path.join(L.D, f'set_{tag}.json.gz'), 'rt'))
    hints = {('k6', tuple(ds), tuple(sy)): h for ds, sy, b, h in d['plain'] if b != 'reuse'}
    recs = load_cores()
    keys = sorted(hints)
    groups = collections.defaultdict(list)
    for k in keys:
        groups[k[1]].append(k)
    order = sorted((g for g in groups.values() if len(g) > 1), key=lambda g: -sum(hints[k] for k in g))
    todo = [k for g in order for k in sorted(g, key=lambda k: hints[k]) if k not in recs]
    t0 = time.time(); n = 0
    wd = os.path.join(L.SCR, 'famwork'); os.makedirs(wd, exist_ok=True)
    with open(OUT, 'a') as f:
        for k in todo:
            if time.time() - t0 > budget or L.disk_mb() < 320:
                break
            try:
                r = CR.one(k, wd)
            except Exception as e:      # noqa: BLE001
                r = dict(kind=k[0], dirs=list(k[1]), syms=list(k[2]), result='ERROR', err=str(e)[:200])
            r['model_hints'] = hints[k]
            f.write(json.dumps(r, separators=(',', ':')) + '\n'); f.flush()
            recs[k] = r; n += 1
    L.log(f'{n} cores computed in {time.time() - t0:.0f}s; {len(todo) - n} sibling-group keys left without a core')
    E = {}; byds = collections.defaultdict(list)
    for k in keys:
        r = recs.get(k)
        if r is None or r.get('result') != 'UNSAT':
            continue
        ds, rng, ab = FA.widened(r)
        E[k] = (ds, rng, ab)
        n_ = len(k[1])
        for j, o in enumerate(FA.orient(ds, rng)):
            byds[o[0]].append((o[1], k, j == 0 and ab == (0, n_)))
    cover = collections.defaultdict(set); cover1 = collections.defaultdict(set)
    for k in keys:
        cover[k].add(k); cover1[k].add(k)
        kind, ds, syms = k
        cs = FA.cons(kind, syms); n_ = len(ds)
        for Ln in range(2, n_ + 1):
            for i in range(0, n_ - Ln + 1):
                c = FA.canon(ds[i:i + Ln])
                if c not in byds:
                    continue
                kr = cs[i:i + Ln - 1]
                for er, src, fw in byds[c]:
                    if src != k and FA.contains(er, kr):
                        cover[src].add(k)
                        if fw and Ln == n_ and c == ds:
                            cover1[src].add(k)

    def greedy(cover):
        unc = set(keys); chosen = []
        cov = {s: set(v) for s, v in cover.items()}
        while unc:
            best = None
            for s, cv in cov.items():
                live = cv & unc
                if not live:
                    continue
                g = sum(hints[x] for x in live) + 5e3 * len(live)
                rr = (hints[s] + 5e3) / g
                if best is None or rr < best[0]:
                    best = (rr, s)
            s = best[1]; live = cov[s] & unc
            chosen.append((s, sorted(live))); unc -= live
            for t in [t for t, cv in cov.items() if not (cv & unc)]:
                del cov[t]
        return chosen
    tot = sum(hints.values())
    c1 = greedy(cover1); c2 = greedy(cover)
    h1 = sum(hints[s] for s, _ in c1); h2 = sum(hints[s] for s, _ in c2)
    out = dict(tag=tag, paid=len(keys), paid_hints=tot, with_core=len(E), cores_new=n,
               cores_missing_in_groups=len(todo) - n,
               L1=dict(seeds=len(c1), removed_keys=len(keys) - len(c1), removed_hints=tot - h1),
               L1L2=dict(seeds=len(c2), removed_keys=len(keys) - len(c2), removed_hints=tot - h2),
               removed_keys=len(keys) - len(c2), removed_hints=tot - h2,
               top=[dict(seed=[s[0], list(s[1]), list(s[2])], E=[list(E[s][0]), E[s][1]] if s in E else None,
                         keys=len(v), removed=sum(hints[y] for y in v if y != s))
                    for s, v in sorted(c2, key=lambda x: -sum(hints[y] for y in x[1] if y != x[0]))[:12]])
    json.dump(out, open(os.path.join(L.D, f'fam_{tag}.json'), 'w'), indent=1)
    with gzip.open(os.path.join(L.D, f'seeds_{tag}.json.gz'), 'wt') as f:
        json.dump([[list(s[1]), list(s[2]), [[list(y[1]), list(y[2])] for y in v]] for s, v in c2], f)
    print(json.dumps({k: v for k, v in out.items() if k != 'top'}, indent=1))


if __name__ == '__main__':
    main()
