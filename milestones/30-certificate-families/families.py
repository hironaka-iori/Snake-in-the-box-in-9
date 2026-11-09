"""Core-derived families: which keys are implied by the widened core of another key.

From data/cores.jsonl (cores.py).  For a key K with core C, the WIDENED key E(K) keeps
  * at a centre p: both bounds of K's symbol if C uses both counters of p; [lo, 21] if C uses
    only the alpha>=lo counter; [0, hi] if only alpha<=hi; nothing (uncounted, (0, 21)) if
    neither;
  * the window trimmed to the positions C needs: the vertices whose 'window' unit is in C and
    the two path neighbours of every centre still counted (they fix its directions).
Every clause of C is sound for Axioms(winOf E.ds, centresOf E.bounds), so K's own proof (the
same core and LRAT) proves Refuted (winOf E.ds) E.bounds, at no extra cost.
E implies a key K2 when E.ds is, up to relabelling and in one orientation of K2, the slice of
K2's directions at some offset, and every counted range of E contains K2's symbol range there
(an uncounted centre of K2, H9's last one, must be uncounted in E).
Seed set: weighted greedy set cover of the paid keys by the E(K) (cost = K's hints in
keys_best234).  Output data/families.json.

  nice -n 15 python families.py
"""
import sys, os, json, gzip, collections
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
M25 = os.path.join(HERE, '..', '25-k7-234')
sys.path.insert(0, M25)
sys.path.insert(0, os.path.join(M25, '..', '10-window-aggregate', 'scripts'))
from refine import canon  # noqa: E402

LUMP = {i: (i, i) for i in range(1, 6)}; LUMP[6] = (6, 21)
FULL = (0, 21)


def cons(kind, syms):
    return [LUMP[s] for s in syms] + ([None] if kind == 'H' else [])


def widened(r):
    """(ds, ranges) of E(K); ranges[j] is None (uncounted) or (lo, hi)."""
    ds = r['dirs']; n = len(ds)
    cs = cons(r['kind'], r['syms'])
    lo, hi = set(r['lo']), set(r['hi'])
    rng = []
    for p in range(1, n):
        s = cs[p - 1]
        if s is None or (p not in lo and p not in hi):
            rng.append(None); continue
        rng.append((s[0] if p in lo else 0, s[1] if p in hi else 21))
    used = set(r['win'])
    for p in range(1, n):
        if rng[p - 1] is not None:
            used |= {p - 1, p, p + 1}
    a, b = min(used), max(used)
    return tuple(ds[a:b]), tuple(rng[a:b - 1]), (a, b)


def orient(ds, rng):
    return [(canon(ds), tuple(rng)), (canon(tuple(reversed(ds))), tuple(reversed(rng)))]


def contains(er, kr):
    for e, k in zip(er, kr):
        if e is None:
            continue
        if k is None or not (e[0] <= k[0] and k[1] <= e[1]):
            return False
    return True


# unit costs of 25-k7-234/certify/README.md ("Budget of the certificates")
BPH = {'k6': 2.8, 'F': 2.9, 'H': 3.6}


def budget(sel, hints, corecl):
    """CPU hours and GB of .olean of the replay + Cnf/Sat modules of the keys sel."""
    cpu = sum(1 + 0.22e-3 * hints[k] + 6 + 1.2e-3 * 3.6 * corecl[k] for k in sel) / 3600
    gb = sum(37e3 + BPH[k[0]] * hints[k] + 41e3 + 3.5 * 3.6 * corecl[k] for k in sel) / 1e9
    return dict(keys=len(sel), hints=sum(hints[k] for k in sel), cpu_h=round(cpu, 1), olean_GB=round(gb, 2))


def main():
    d = json.load(gzip.open(os.path.join(M25, 'data', 'keys_best234.json.gz'), 'rt'))
    hints = {(k[0], tuple(k[1]), tuple(k[2])): h for k, h, b in zip(d['keys'], d['hints'], d['basis'])
             if b != 'reuse'}
    corecl = {(k[0], tuple(k[1]), tuple(k[2])): c for k, c, b in zip(d['keys'], d['core'], d['basis'])
              if b != 'reuse'}
    recs = {}
    sys.path.insert(0, HERE)
    import cores as CO
    for r in CO.records():
        if r['result'] == 'UNSAT':
            recs[(r['kind'], tuple(r['dirs']), tuple(r['syms']))] = r
    keys = sorted(hints)
    # E(K) indexed by canonical directions (both orientations)
    E = {}
    byds = collections.defaultdict(list)
    stats = collections.Counter()
    for k in keys:
        r = recs.get(k)
        if r is None:
            continue
        ds, rng, ab = widened(r)
        E[k] = (ds, rng, ab)
        n = len(k[1])
        stats['trimmed'] += (ab != (0, n))
        stats['widened'] += any(x is None or (x[0], x[1]) not in LUMP.values() for x in rng) or ab != (0, n)
        stats['uncounted_centre'] += sum(x is None for x in rng)
        stats['one_sided'] += sum(x is not None and x not in LUMP.values() for x in rng)
        for j, o in enumerate(orient(ds, rng)):
            # forward orientation of an untrimmed E: refuted_narrow alone (same window)
            byds[o[0]].append((o[1], k, j == 0 and ab == (0, n)))
    # which keys does each E cover (cover1: by refuted_narrow alone)
    cover = collections.defaultdict(set)
    cover1 = collections.defaultdict(set)
    for k in keys:
        cover[k].add(k); cover1[k].add(k)
        kind, ds, syms = k
        cs = cons(kind, syms)
        n = len(ds)
        for L in range(2, n + 1):
            for i in range(0, n - L + 1):
                c = canon(ds[i:i + L])
                if c not in byds:
                    continue
                kr = cs[i:i + L - 1]
                for er, src, fw in byds[c]:
                    if src != k and contains(er, kr):
                        cover[src].add(k)
                        if fw and L == n and c == ds:
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
    chosen1 = greedy(cover1)
    chosen = greedy(cover)
    tot = sum(hints.values())
    # families by the number of centres E still counts, and the top-N families
    byc = collections.defaultdict(lambda: [0, 0, 0.0])
    rem = []
    for s_, live in chosen:
        if s_ not in E:
            continue
        nc = sum(x is not None for x in E[s_][1])
        rh = sum(hints[y] for y in live if y != s_)
        byc[nc][0] += 1; byc[nc][1] += len(live) - 1; byc[nc][2] += rh
        rem.append(rh)
    rem.sort(reverse=True)
    topn = {N: sum(rem[:N]) for N in (10, 50, 100, 500, 1000)}
    ecount = collections.Counter(sum(x is not None for x in v[1]) for v in E.values())
    seed_h = sum(hints[s] for s, _ in chosen)
    fam = sorted(chosen, key=lambda x: -sum(hints[y] for y in x[1] if y != x[0]))
    top = []
    for s, live in fam[:25]:
        ds, rng, ab = E[s] if s in E else (s[1], None, None)
        top.append(dict(seed=[s[0], list(s[1]), list(s[2])], E_dirs=list(ds), E_ranges=rng, trim=ab,
                        keys=len(live), seed_hints=hints[s],
                        hints_removed=sum(hints[y] for y in live if y != s)))
    seed1_h = sum(hints[s] for s, _ in chosen1)
    out = dict(paid=len(keys), with_core=len(E), paid_hints=tot, stats=stats,
               narrow_only=dict(seeds=len(chosen1), seed_hints=seed1_h, removed_hints=tot - seed1_h,
                                removed_keys=len(keys) - len(chosen1)),
               budget_all=budget(keys, hints, corecl),
               budget_narrow=budget([s for s, _ in chosen1], hints, corecl),
               budget_full=budget([s for s, _ in chosen], hints, corecl),
               keys_implied_by_another=len({k for s, v in cover.items() for k in v if k != s}),
               seeds=len(chosen), seed_hints=seed_h, removed_hints=tot - seed_h,
               removed_keys=len(keys) - len(chosen),
               by_kind_removed=collections.Counter(k[0] for s, v in chosen for k in v if k != s),
               E_counted_centres=dict(sorted(ecount.items())),
               families_by_counted=dict(sorted(byc.items())), removed_by_top_families=topn,
               top_families=top)
    with gzip.open(os.path.join(HERE, 'data', 'seeds.json.gz'), 'wt') as f:
        json.dump(dict(narrow=[[s[0], list(s[1]), list(s[2]), [[y[0], list(y[1]), list(y[2])] for y in v]]
                               for s, v in chosen1],
                       full=[[s[0], list(s[1]), list(s[2]), [[y[0], list(y[1]), list(y[2])] for y in v]]
                             for s, v in chosen],
                       E={json.dumps([k[0], list(k[1]), list(k[2])]): [list(v[0]), v[1], list(v[2])]
                          for k, v in E.items()}), f)
    print(json.dumps(out, indent=1, default=str)[:6000])
    json.dump(out, open(os.path.join(HERE, 'data', 'families.json'), 'w'), indent=1, default=str)


if __name__ == '__main__':
    main()
