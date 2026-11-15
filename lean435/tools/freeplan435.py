#!/usr/bin/env python3
"""The plan's FREE keys as a job list for prod435.py (`--free` mode): everything the 4.35 chain needs
that was Lean-checked only in 4.19 (233-era and 235-237 certificates), so that no 4.35 module depends on
a 4.19 .olean.

    freeplan435.py --plan P [--out-dir lean435/data]
      -> freeplan_<tag>.json.gz   a certplan-format file whose rows are the certificates to (re)build,
                                  all `free: false` (so cert231.items / prod435.py take them)
         freeseeds_<tag>.json.gz  the seed plan (cert231 format) of its plain rows, with the 233 widened
                                  bounds where the seed is a 233 seed
         freederive_<tag>.json.gz key -> how the chain gets it (glue table for the assembly)
    then: prod435.py run --plan freeplan_<tag>.json.gz --seeds freeseeds_<tag>.json.gz --index I --workers W

What is certified (each as one merged 4.35 module, like the paid certificates):
  plain reuse233 / derive233_L1 / derive233_L2  ->  the 233 SEEDS they come from (milestone 33,
      seeds6SB233.json.gz), each with its widened bounds: `Refuted (winOf ds) wide`. A plain key is then
      glue: the seed itself, `Families.refuted_key_of_wide` (L1) or `Families.refuted_key_sub` (L2),
      exactly as cert233.proof_term writes them (LocalWindowFamilies is in the ported core).
      A key no 233 seed derives (checked with families_k7.derivable, the generators' mirror) is
      certified itself.
  plain reuse (235-237 replay keys)              ->  each key itself (`Refuted (winOf ds) (boundsOf syms)`).
  H8 keys of the chain (the 233 chain's 262 cuts) -> each key itself (plain path, kind H).
  share free233 above the floor level            ->  the 233 share key with its 233 cap T233 - 1.
  share lean_floor                                ->  nothing here: the floors (lean435/floors).
"""
import argparse, collections, gzip, json, os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(ROOT, 'milestones', '35-231-lean', 'scripts'))
sys.path.insert(0, os.path.join(ROOT, 'milestones', '35-231-lean', 'certify'))
sys.path.insert(0, os.path.join(ROOT, 'milestones', '33-233-lean', 'certify'))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--plan', required=True)
    ap.add_argument('--out-dir', default=os.path.join(ROOT, 'lean435', 'data'))
    a = ap.parse_args()
    t0 = time.time()
    import gen_lean_automaton6sc as GEN      # read-only use of the chain generator's plan reader
    import cert233 as C
    FK = C.FK
    tag = os.path.basename(a.plan).replace('.json.gz', '')
    P = GEN.load_plan(a.plan)
    rows = {(tuple(r['key'][0]), tuple(r['key'][1])): r for r in P['plain_rows']}
    pl233 = C.load_plan(C.PLAN)                   # key -> ('self', wide) | (seed, L1|L2, v, s)
    seeds233 = {k: v[1] for k, v in pl233.items() if v[0] == 'self'}
    byds = collections.defaultdict(list)
    for k in seeds233:
        byds[FK.canon(k[0])].append(k)
        byds[FK.canon(k[0][::-1])].append(k)

    def hints233(k):
        m = C.load_meta(C.CORE, C.pname(k))
        return (m or {}).get('lrat', {}).get('hints', 0)

    derive = {}               # key -> [how, seed, method, v, s]
    need_seed, need_self = set(), set()
    nder = collections.Counter()
    for k, r in rows.items():
        b = r['basis']
        if not r['free']:
            continue
        if b == 'reuse':
            need_self.add(k); derive[k] = ['self'] ; nder['reuse: self'] += 1
            continue
        assert b in ('reuse233', 'derive233_L1', 'derive233_L2'), r
        if k in pl233:
            e = pl233[k]
            if e[0] == 'self':
                need_seed.add(k); derive[k] = ['seed', list(map(list, k))]; nder[b + ': 233 seed'] += 1
            else:
                need_seed.add(e[0]); derive[k] = ['glue', list(map(list, e[0])), e[1], e[2], e[3]]
                nder[b + ': 233 ' + e[1]] += 1
            continue
        # a key outside the 233 plan: find a 233 seed that implies it (L1 / L2)
        best = None
        ds2 = k[0]
        for L in range(2, len(ds2) + 1):
            for i in range(0, len(ds2) - L + 1):
                for src in byds.get(FK.canon(ds2[i:i + L]), ()):
                    dv = FK.derivable((None, list(src[0]), list(src[1])), [tuple(x) for x in seeds233[src]],
                                      (None, list(k[0]), list(k[1])))
                    if dv:
                        h = hints233(src)
                        o = (0 if dv[0] == 'L1' else 1, h, src)
                        if best is None or o < best[0]:
                            best = (o, src, dv)
        if best:
            src, dv = best[1], best[2]
            need_seed.add(src); derive[k] = ['glue', list(map(list, src)), dv[0], dv[1], dv[2]]
            nder[b + ': ' + dv[0]] += 1
        else:
            need_self.add(k); derive[k] = ['self']; nder[b + ': self (no 233 seed implies it)'] += 1
    for c, t in P['h8']:
        need_self.add((c, t)); nder['h8: self'] += 1
    # plain rows of the free plan: 233 seeds (widened) + selves
    plain_rows, keys, seeds_out = [], [], []
    for k in sorted(need_seed | need_self, key=lambda k: (len(k[0]), k)):
        wide = seeds233.get(k) if k in need_seed else None
        if wide is None:
            wide = [list(x) for x in C.GC.dir_bounds(tuple(k[1]))]
        est = hints233(k) if k in need_seed else 0
        plain_rows.append({'kind': 'plain', 'key': [list(k[0]), list(k[1])], 'basis': 'free435',
                           'free': False, 'est_hints': est or 50000})
        seeds_out.append([len(keys), [list(x) for x in wide]])
        keys.append(['k6', list(k[0]), list(k[1])])
    share_rows = []
    s233 = {}
    k233 = json.load(gzip.open(GEN.KEYS233, 'rt'))
    for ds, sy, T, lb, b, h in k233['share']:
        if b != 'lean_floor':
            s233[(tuple(ds), tuple(sy))] = (int(T), h)
    for (c, t), (L, b) in P['share'].items():
        if b == 'free233' and L > GEN.G6.floor_level(c, t):
            T, h = s233[(c, t)]
            share_rows.append({'kind': '5', 'key': [list(c), list(t)], 'level': T, 'basis': 'free233',
                               'free': False, 'est_hints': h or 50000})
    plan_out = dict(summary=dict(source=os.path.relpath(a.plan, ROOT), note='freeplan435: certificates to '
                                 'rebuild in 4.35 for the free keys', plain=len(plain_rows), share=len(share_rows),
                                 seeds233=len(need_seed), selves=len(need_self), derivation=dict(nder),
                                 est_hints=sum(r['est_hints'] for r in plain_rows + share_rows)),
                    plain=plain_rows, share=share_rows, format='certplan231 rows (freeplan435)')
    seeds = dict(summary=dict(keys=len(keys), seeds=len(keys), derived=0, note='freeplan435'),
                 keys=keys, seeds=seeds_out, derive=[[i, 'self', None, None] for i in range(len(keys))])
    os.makedirs(a.out_dir, exist_ok=True)
    for name, obj in ((f'freeplan_{tag}.json.gz', plan_out), (f'freeseeds_{tag}.json.gz', seeds),
                      (f'freederive_{tag}.json.gz', {' '.join(map(str, k[0])) + '|' + ' '.join(map(str, k[1])): v
                                                     for k, v in derive.items()})):
        with gzip.GzipFile(os.path.join(a.out_dir, name), 'wb', mtime=0) as g:
            g.write(json.dumps(obj, separators=(',', ':')).encode())
    print(json.dumps(plan_out['summary'], indent=1))
    print(f'{time.time() - t0:.0f} s; wrote freeplan_/freeseeds_/freederive_{tag}.json.gz to {a.out_dir}')


if __name__ == '__main__':
    main()
