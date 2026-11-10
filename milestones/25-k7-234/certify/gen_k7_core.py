"""UNSAT cores, packed clause-soundness modules and chunk aggregates of the new certificates
of the seven-centre (k7) bound 234.

The key set of a k7 chain (`data/keys_<tag>.json.gz`) has three kinds of keys: k6 windows
(3 to 7 directions, one count per interior vertex), F8 windows (8 directions, 7 counts) and
H9 windows (9 directions, 7 counts, stored reversed so that the uncounted interior vertex is
the last one).  The certificate of every key `(ds, syms)` is `Refuted (winOf ds) (boundsOf
syms)`: `centresOf` takes `syms.length` centres, so an H9 key has 7 centres on its 8 interior
vertices and the eighth carries no constraint.  The new keys (those in none of `dirKeysR4b`,
`dirKeysR4`, `dirKeysK6`) are the chunks `dirKeysK7_<c>` of `lean/scripts/gen_lean_glue7.py
keys` (sorted, 400 keys a chunk).  This script certifies them, set name `k7`, Lean module
prefix `K7`:

  1. the CNF: `wincert.Encoding(winOf ds, alpha, radius 4)` with alpha = the bounds of `syms`
     and, for an H9 key, `None` for the uncounted eighth interior vertex (the encoding of
     `../k7.py`), plus the lazy cycle cuts that `wincert.decide` adds until the solver
     answers UNSAT.  The cuts are recorded (vertex lists) in the core JSON, so the CNF is
     regenerated exactly from it (`regen_cnf`, checked by SHA256).  No CNF is committed.
  2. the UNSAT core: `gen_lean_core.full_core_ids` (the toolchain CaDiCaL with `--lrat`,
     configurations `FULL_PORTFOLIO`, each proof trimmed to the cone of the empty clause; the
     input clauses its hints use are the core).  The hint count of that proof is recorded as
     the estimate.  The replayed LRAT is made later from the core alone (`replay_k7.py`).
  3. one packed module `LocalWindowCnf/K7<ds>A<syms>.lean` (`gen_lean_cnfsat_packed.emit`:
     `window`, `bounds`, `raw`, `cnf`, `meaning`, `ctrs`, `tags`, `check`, `sat`), whose
     tagging re-derives every clause from the encoding (`Tags.checkAll`; H9 cores have
     counters on the centres 0..6 only).  With `--part-lits N` (default 4000) `check` is
     proved in several declarations (`work/final_lean/LocalWindowTagsSplit.lean`): the
     counters by `ctrOKL` (linear check of the endpoint order; `ctrOK` compares all pairs of
     the about 350 endpoint flags of an H9 ball, 14 s and 1.2 GB), and the clauses in parts
     of at most N literals.  This keeps every H9 module at 1.2-1.6 GB instead of 2.4 GB and
     more; `--part-lits 0` writes the single `check` of the default layout.
  4. `milestones/10-window-aggregate/data/lean_core_direction_k7/NAME.json` per key.

`final` writes, once the replays `LocalWindowUnsat.K7*` exist (`replay_k7.py gen`):

  * `LocalWindowDirUnsatK7_<c>.lean` per chunk: `K7<…>.refuted : Refuted (winOf ds)
    (boundsOf syms)` for every key of the chunk (`Tags.refuted_of_sat sat unsat`) and
    `allRefutedK7_<c> : AllRefutedList dirKeysK7_<c>`;
  * `LocalWindowDirUnsatK7.lean`: `allRefutedK7 : AllRefutedK7`, the premise that
    `LocalWindowDirGlue7<T>` and `UpperBound234` (`gen_lean_glue7.py`) take.

Seeds and families (`--plan data/seeds234.json.gz`, written by `families_k7.py`): `run --plan`
certifies only the seed keys of the plan, each with its widened Lean bounds (`bounds := [...]`
in the Cnf module, `lean_bounds` in the core JSON).  The core is taken from the first
configuration of `FULL_PORTFOLIO` whose used counters allow the planned bounds (`--unsat` first,
the configuration of the plan); if none does, the bounds are narrowed to what the core allows.
After the seeds, every key whose seed no longer implies it (checked with the mirror of the Lean
checks, `families_k7.derivable`) is certified on its own (an *orphan*).  `final --plan` proves
every key of a chunk from its own certificate if it has one, else from its seed: by L1
`refuted_key_of_wide` (same window, `widerB`) or L2 `refuted_key_sub` (sub-window, reversal,
relabelling, `subOK`) of `work/final_lean/LocalWindowFamilies.lean`, each side condition one
kernel `decide`.  The statements `K7….refuted : Refuted (winOf ds) (boundsOf syms)`, the chunk
theorems and `allRefutedK7 : AllRefutedK7` are exactly those of the plain run.

Solver runs are sequential; every CaDiCaL call goes through a wrapper with `nice -n 19` and
a file-size cap on the raw proof.  Resumable: a key whose JSON and Cnf module exist is
skipped.

  nice -n 19 python3 gen_k7_core.py run --keys KEYS.json.gz --work DIR [--out ROOT] [--kinds H,F,k6]
                                        [--only DS:SYMS ...] [--limit N] [--max-est HINTS] [--plan PLAN]
  python3 gen_k7_core.py cnfsat --work DIR [--out ROOT] NAME ...   # rewrite Cnf modules from core JSONs
  python3 gen_k7_core.py final --keys KEYS.json.gz [--out ROOT] [--chunks 0,1,...] [--plan PLAN]
  python3 gen_k7_core.py regen --out CERTDIR NAME ...      # CNFs (.cnf.gz) from the core JSONs

See `README.md` (this directory) for the five-key validation and the commands of a full run.
"""
import argparse, gzip, hashlib, json, os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
S10 = os.path.join(ROOT, 'milestones', '10-window-aggregate', 'scripts')
GLUE7 = os.path.join(ROOT, 'milestones', '25-k7-234', 'lean', 'scripts')
sys.path.insert(0, S10)
sys.path.insert(0, GLUE7)
import wincert                         # noqa: E402
import gen_lean_core as GC             # noqa: E402
import gen_lean_sat as GS              # noqa: E402
import gen_lean_cnfsat_packed as CP    # noqa: E402
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import families_k7 as FK               # noqa: E402

LEAN = os.path.join(ROOT, 'work', 'final_lean')
CORE = os.path.join(ROOT, 'milestones', '10-window-aggregate', 'data', 'lean_core_direction_k7')
TOOLCHAIN_CADICAL = '/home/user/lean-deps/toolchain/lean-4.19.0-linux/bin/cadical'
RADIUS = 4
PREFIX = 'K7'
PART_LITS = 4000     # literals per clause-check declaration of the packed core module
ME = 'milestones/25-k7-234/certify/gen_k7_core.py'


# ------------------------------------------------------------------ keys ---

def load_glue7():
    import gen_lean_glue7 as G7      # imports gen_lean_automaton7 (numpy)
    return G7


def new_chunks(keys, chunk=400):
    """The chunks `dirKeysK7_<c>` of `gen_lean_glue7.py keys --keys KEYS --chunk CHUNK`."""
    G7 = load_glue7()
    _, _, _, chunks = G7.split(argparse.Namespace(keys=keys, chunk=chunk))
    return chunks


def key_parts(chunks, keys_per_module=4000):
    """Part module `LocalWindowDirKeysK7_P<p>` of each chunk (as `gen_lean_glue7.keys`)."""
    parts, cur, n = [], [], 0
    for ci, ch in enumerate(chunks):
        if cur and n + len(ch) > keys_per_module:
            parts.append(cur)
            cur, n = [], 0
        cur.append(ci)
        n += len(ch)
    parts.append(cur)
    return {ci: pi for pi, part in enumerate(parts) for ci in part}


def key_estimates(paths):
    """Per-key hint estimate of the key files (`hints`, else `cost`), if they have one."""
    est = {}
    for p in paths:
        d = json.load((gzip.open if p.endswith('.gz') else open)(p, 'rt'))
        vals = d.get('hints') if isinstance(d.get('hints'), list) else d.get('cost')
        if isinstance(vals, list) and len(vals) == len(d['keys']):
            for (_, ds, syms), h in zip(d['keys'], vals):
                est[(tuple(ds), tuple(syms))] = h
    return est


def parse_only(spec):
    ds, syms = spec.split(':')
    return tuple(map(int, ds)), tuple(map(int, syms))


# -------------------------------------------------------------- encoding ---

def kind_of(dirs, syms):
    return 'H' if len(dirs) == len(syms) + 2 else 'F' if len(dirs) == 8 else 'k6'


def case_name(dirs, syms):
    return 'd' + ''.join(map(str, dirs)) + '_a' + '_'.join(
        f'{lo}' if lo == hi else f'{lo}-{hi}' for lo, hi in GC.dir_bounds(syms))


def module_name(dirs, syms):
    return GC.dir_module(list(dirs), list(syms), PREFIX)


def encoding(dirs, syms):
    """The radius-4 CNF of `../k7.py encoding`: one bound per lumped count, then `None` for
    the uncounted last interior vertex of an H9 key."""
    window = wincert.window_from_dirs(list(dirs))
    bounds = GC.dir_bounds(syms)
    alpha = [lo if lo == hi else (lo, hi) for lo, hi in bounds]
    alpha += [None] * GS.uncounted_centres(window, bounds)
    return wincert.Encoding(window, alpha, RADIUS)


def write_gz_cnf(enc, path):
    """Plain DIMACS text, gzipped with mtime 0; returns the SHA256 of the text."""
    data = (f'p cnf {enc.nv} {len(enc.clauses)}\n' +
            ''.join(' '.join(map(str, c)) + ' 0\n' for c in enc.clauses)).encode()
    with gzip.GzipFile(path, 'wb', mtime=0) as g:
        g.write(data)
    return hashlib.sha256(data).hexdigest()


def regen_cnf(meta, path):
    """The CNF of a core JSON: the encoding plus its recorded cycle cuts (checked by SHA256)."""
    enc = encoding(meta['dirs'], meta['syms'])
    assert len(enc.clauses) == meta['base_clauses'], meta['name']
    for cyc in meta['cycle_cuts']:
        enc.add_cycle_cut(cyc)
    sha = write_gz_cnf(enc, path)
    assert sha == meta['cnf_sha256'] and len(enc.clauses) == meta['cnf_clauses'], meta['name']
    return path


def cadical_wrapper(work, fsize_mb):
    p = os.path.join(work, 'cadical_nice.sh')
    open(p, 'w').write(f'#!/bin/bash\nulimit -f {fsize_mb * 1024}\nexec nice -n 19 {TOOLCHAIN_CADICAL} "$@"\n')
    os.chmod(p, 0o755)
    return p


def disk_free_mb():
    st = os.statvfs('/')
    return st.f_bavail * st.f_frsize // (1 << 20)


# ------------------------------------------------------------------- run ---

def used_counters(dirs, syms, ids, npre):
    """(lo, hi): the 0-based centres whose `alpha >= lo` / `alpha <= hi` counter has a clause
    in the core `ids` (clause ids of the CNF; ids above `npre` are cycle cuts)."""
    window = wincert.window_from_dirs(list(dirs))
    bounds = GC.dir_bounds(syms)
    alpha = [lo if lo == hi else (lo, hi) for lo, hi in bounds]
    alpha += [None] * GS.uncounted_centres(window, bounds)
    enc = GS.TaggedEncoding(window, alpha, radius=RADIUS)
    used = {enc.tags[i - 1][1] for i in ids if i <= npre and enc.tags[i - 1][0] in
            ('first', 'zero', 'mono', 'step', 'over')}
    kinds = [enc.ctrs[c][2] for c in used]
    return {k[1] for k in kinds if k[0] == 'lo'}, {k[1] for k in kinds if k[0] == 'hi'}


def allowed(plan, syms, lo_used, hi_used):
    """The bounds `plan` (widened bounds of the key) narrowed to what a core with these counters
    allows: a used counter keeps the key's own bound on its side."""
    out = []
    for i, s in enumerate(syms):
        lo, hi = FK.bound_of(s)
        plo, phi = plan[i] if i < len(plan) else FK.TRIV
        out.append((lo if i in lo_used else plo, hi if i in hi_used else phi))
    while out and out[-1] == FK.TRIV:
        out.pop()
    return out


def seed_core(name, work, cadical, certs, dirs, syms, npre, plan):
    """Core of a seed: the first configuration of `FULL_PORTFOLIO` whose core allows the planned
    bounds, else the one that keeps the most widened sides.  Returns (ids, info, lean bounds)."""
    cnf = GC.extract_cnf(name, work, certs)
    best = None
    for cfg in GC.FULL_PORTFOLIO:
        nl, nh, desc, ids = GC.best_cadical_proof(cnf, os.path.join(work, name + '.full'), cadical, [1],
                                                  portfolio=[cfg], rounds=1)
        os.remove(os.path.join(work, name + '.full.lrat'))
        lb = allowed(plan, syms, *used_counters(dirs, syms, ids, npre))
        score = sum((x[1] - x[0]) for x in lb) + 22 * (len(syms) - len(lb))
        cand = (lb == [tuple(x) for x in plan], score, -nh, ids, {'full_lemmas': nl, 'full_hints': nh,
                                                                   'full_seed': desc}, lb)
        if best is None or cand[:3] > best[:3]:
            best = cand
        if cand[0]:
            break
    return best[3], best[4], best[5]


def one(dirs, syms, work, certs, cadical, out, core, log, part_lits, plan=None, sat_v2=False):
    """Certify one key; with `plan` (its widened bounds) as a seed with those bounds, or as many
    of them as its core allows."""
    name, module = case_name(dirs, syms), module_name(dirs, syms)
    mp = os.path.join(core, name + '.json')
    if os.path.exists(mp) and os.path.exists(os.path.join(out, 'LocalWindowCnf', module + '.lean')) and \
            (plan is None or 'lean_bounds' in json.load(open(mp))):
        return None
    t0 = time.time()
    enc = encoding(dirs, syms)
    npre = len(enc.clauses)
    st, _, ncuts = wincert.decide(enc, certify=False)
    assert st == 'UNSAT', (name, st)
    inv = {i: v for v, i in enc.var.items()}
    # vertex lists in literal order, so that add_cycle_cut rebuilds the same clauses
    cuts = [[inv[-l] for l in c] for c in enc.clauses[npre:]]
    gz = os.path.join(certs, name + '.cnf.gz')
    sha = write_gz_cnf(enc, gz)
    t1 = time.time()
    if plan is None:
        ids, finfo = GC.full_core_ids(name, work, cadical, [1], certs)
        lean_bounds = None
    else:
        ids, finfo, lean_bounds = seed_core(name, work, cadical, certs, dirs, syms, npre, plan)
    t2 = time.time()
    bounds = GC.dir_bounds(syms)
    meta = {'name': name, 'module': 'LocalWindowCnf.' + module, 'kind': kind_of(dirs, syms),
            'dirs': list(dirs), 'syms': list(syms), 'window': wincert.window_from_dirs(list(dirs)),
            'bounds': bounds, 'radius': RADIUS, 'variables': enc.nv, 'cnf_clauses': len(enc.clauses),
            'base_clauses': npre, 'cnf_sha256': sha, 'cycle_cuts': cuts,
            'cnf_source': 'regenerated: wincert.Encoding(winOf dirs, boundsOf syms (+ None for an uncounted '
                          'last interior vertex), radius 4) plus cycle_cuts (in order); SHA256 cnf_sha256 '
                          '(gen_k7_core.regen_cnf)',
            'hash_source': 'gen_k7_core.py',
            'core_producer': f"cadical --lrat {finfo['full_seed']} on the CNF, trimmed "
                             f"({finfo['full_lemmas']} lemmas, {finfo['full_hints']} hints)",
            'lrat_producer': 'core_lrat (cadical on the core; regenerated by replay_k7.py, not committed)',
            'lrat': {'lemmas': finfo['full_lemmas'], 'hints': finfo['full_hints'], 'estimated_from_full_proof': True},
            'core_ids': ids}
    if plan is not None:
        meta['plan_bounds'] = [list(x) for x in plan]
        meta['lean_bounds'] = [list(x) for x in lean_bounds]
    json.dump(meta, open(mp, 'w'))
    r = CP.emit(name, certs, core, out, part_lits=part_lits, sat_v2=sat_v2)
    t3 = time.time()
    for p in (gz, os.path.join(work, name + '.cnf')):
        if os.path.exists(p):
            os.remove(p)
    rec = {'name': name, 'module': module, 'kind': meta['kind'], 'variables': enc.nv,
           'clauses': len(enc.clauses), 'cuts': ncuts, 'core': len(ids), 'core_lits': r['lits'],
           'full_hints': finfo['full_hints'], 'cnfsat_src_bytes': r['lean_bytes'], 'check_parts': r['check_parts'],
           'enc_s': round(t1 - t0, 2), 'core_s': round(t2 - t1, 2), 'emit_s': round(t3 - t2, 2)}
    if plan is not None:
        rec.update(seed=True, plan_bounds=meta['plan_bounds'], lean_bounds=meta['lean_bounds'],
                   as_planned=meta['lean_bounds'] == meta['plan_bounds'], core_config=finfo['full_seed'])
    with open(log, 'a') as f:
        f.write(json.dumps(rec) + '\n')
    return rec


def run(a):
    os.makedirs(a.core, exist_ok=True)
    os.makedirs(a.work, exist_ok=True)
    certs = os.path.join(a.work, 'certs')
    os.makedirs(certs, exist_ok=True)
    cadical = cadical_wrapper(a.work, a.fsize_mb)
    keys = [k for ch in new_chunks(a.keys, a.chunk) for k in ch]
    if a.only:
        want = set(map(parse_only, a.only))
        missing = want - set(keys)
        assert not missing, 'not new keys of the key set: %s' % sorted(missing)
        keys = [k for k in keys if k in want]
    kinds = set(a.kinds.split(','))
    keys = [k for k in keys if kind_of(*k) in kinds]
    est = key_estimates(a.keys)
    plan = load_plan(a.plan) if a.plan else None
    if plan:
        seeds = plan['seed_bounds']
        nk = len(keys)
        keys = [k for k in keys if k in seeds]
        print(json.dumps({'plan_seeds': len(seeds), 'seeds_here': len(keys), 'keys_here': nk}), flush=True)
    keys.sort(key=lambda k: (est.get(k, 1e12), k))       # smallest estimate first
    n = 0
    stopped = False
    for k in keys:
        if a.max_est and est.get(k, 0) > a.max_est:
            continue
        if disk_free_mb() < a.min_disk_mb:
            print('stop: disk below %d MB' % a.min_disk_mb, flush=True)
            stopped = True
            break
        rec = one(k[0], k[1], a.work, certs, cadical, a.out, a.core, a.log, a.part_lits,
                  plan['seed_bounds'][k] if plan else None, sat_v2=a.sat_v2)
        if rec:
            n += 1
            print(json.dumps(rec), flush=True)
            if a.limit and n >= a.limit:
                stopped = True
                break
    if plan and not stopped:
        # keys whose seed (as certified) no longer implies them: certify them on their own
        allk = set(k for ch in new_chunks(a.keys, a.chunk) for k in ch)
        orph = [k for k in plan['derived'] if k in allk and (not a.only or k in want)
                and kind_of(*k) in kinds and derivation(plan, k, a.core) is None]
        unproved = [k for k in orph if not os.path.exists(os.path.join(a.core, case_name(*k) + '.json'))]
        print(json.dumps({'orphans': len(orph), 'orphans_to_certify': len(unproved)}), flush=True)
        for k in sorted(unproved, key=lambda k: (est.get(k, 1e12), k)):
            if disk_free_mb() < a.min_disk_mb:
                print('stop: disk below %d MB' % a.min_disk_mb, flush=True)
                break
            rec = one(k[0], k[1], a.work, certs, cadical, a.out, a.core, a.log, a.part_lits, sat_v2=a.sat_v2)
            if rec:
                rec['orphan'] = True
                print(json.dumps(rec), flush=True)


# ------------------------------------------------------------------ plan ---

def load_plan(path):
    """The seed plan of `families_k7.py`: `seed_bounds` {key: widened bounds} and `derived`
    {key: (seed key, method, v, s)} for the keys that are not seeds."""
    d = json.load(gzip.open(path, 'rt'))
    keys = [(tuple(k[1]), tuple(k[2])) for k in d['keys']]
    seeds = [(keys[i], [tuple(x) for x in b]) for i, b in d['seeds']]
    derived = {}
    for k, (si, m, v, s) in zip(keys, d['derive']):
        if m != 'self':
            derived[k] = (seeds[si][0], m, v, s)
    return {'seed_bounds': dict(seeds), 'derived': derived, 'summary': d['summary']}


def own_meta(k, core):
    p = os.path.join(core, case_name(*k) + '.json')
    return json.load(open(p)) if os.path.exists(p) else None


def derivation(plan, k, core):
    """How key `k` is proved once its certificates exist: ('L1' | 'L2', seed meta, v, s) from the
    certificate of its seed (with the bounds that certificate has), else ('own', meta) from its own
    certificate, else None.  A seed is its own certificate."""
    dv = seed_derivation(plan, k, core)
    if dv is not None:
        return dv
    m = own_meta(k, core)
    if m is not None and (k not in plan['seed_bounds'] or 'lean_bounds' in m):
        return ('own', m)
    return None


def seed_derivation(plan, k, core):
    if k not in plan['derived']:
        return None
    sk, meth, v, s = plan['derived'][k]
    sm = own_meta(sk, core)
    if sm is None or 'lean_bounds' not in sm:
        return None
    lb = [tuple(x) for x in sm.get('lean_bounds') or GC.dir_bounds(sk[1])]
    seed = (None, list(sk[0]), list(sk[1]))
    key = (None, list(k[0]), list(k[1]))
    if meth == 'L1' and list(sk[0]) == list(k[0]) and FK.wider_b(lb, FK.bounds_of(k[1])):
        return ('L1', sm, None, None)
    if meth == 'L2' and FK.subok(v, s, FK.win_of(sk[0]), lb, FK.win_of(k[0]), FK.bounds_of(k[1])):
        return ('L2', sm, v, s)
    dv = FK.derivable(seed, lb, key)          # the planned derivation failed: search again
    return (dv[0], sm, dv[1], dv[2]) if dv else None


# ----------------------------------------------------------------- final ---

def lst(c):
    return '[' + ', '.join(map(str, c)) + ']'


def proof_term(k, dv):
    """(proof of `Refuted (winOf ds) (boundsOf syms)`, certificate module) for key `k` and its
    derivation `dv` (`derivation`; None: the plain certificate of the key)."""
    m = module_name(*k)
    if dv is None or (dv[0] == 'own' and dv[1].get('lean_bounds') is None):
        return f'Tags.refuted_of_sat {m}.sat {m}.unsat', m
    if dv[0] == 'own':      # a seed: its widened certificate, narrowed back to its own bounds (L1)
        return (f'Families.refuted_key_of_wide (Tags.refuted_of_sat {m}.sat {m}.unsat)\n'
                f'    (by decide +kernel)'), m
    sm = dv[1]['module'].split('.')[-1]
    cert = f'(Tags.refuted_of_sat {sm}.sat {sm}.unsat)'
    if dv[0] == 'L1':
        return f'Families.refuted_key_of_wide {cert}\n    (by decide +kernel)', sm
    return (f'Families.refuted_key_sub (mkPerm {lst(dv[2])}) {dv[3]}\n    {cert}\n'
            f'    (by decide +kernel)'), sm


def chunk_module(ci, ch, part, n_chunks, dvs=None):
    mods = [module_name(*k) for k in ch]
    pts = [proof_term(k, dvs[k] if dvs else None) for k in ch]
    certs = sorted(set(c for _, c in pts))
    imports = ''.join(f'import LocalWindowUnsat.{m}\n' for m in certs)
    refuted = ''.join(f'theorem {m}.refuted : Refuted (winOf {lst(d)}) (boundsOf {lst(s)}) :=\n'
                      f'  {pt}\n\n' for m, (d, s), (pt, _) in zip(mods, ch, pts))
    nown = sum(1 for k in ch if (dvs is None or dvs[k][0] == 'own'))
    fam = '' if dvs is None else f'''
Seeds and families (`--plan`): {nown} of the keys have their own certificate (a seed with widened
bounds is narrowed back by L1, `Families.refuted_key_of_wide`); the other {len(ch) - nown} follow from
the widened certificate of their seed, by L1 (same window, `widerB`, {sum(1 for k in ch if dvs[k][0] == 'L1')} keys) or by L2
(`Families.refuted_key_sub`: the seed's window mapped into the key's by a cube automorphism
`amap (mkPerm v) s`, `subOK`, {sum(1 for k in ch if dvs[k][0] == 'L2')} keys).  The chunk imports the {len(certs)} certificates it uses.
'''
    term = 'trivial'
    for m in reversed(mods):
        term = f'And.intro {m}.refuted\n    ({term})'
    nh = sum(kind_of(*k) == 'H' for k in ch)
    return f'''import LocalWindowTags
{'' if dvs is None else 'import LocalWindowFamilies' + chr(10)}import LocalWindowDirKeysK7_P{part}
{imports}
/-!
# Chunk {ci} of the {n_chunks} chunks of new certificates of the seven-centre bound

Generated by `{ME} final`.
For each of the {len(ch)} keys `(ds, syms)` of `dirKeysK7_{ci}` ({nh} of them H9 windows: 9
directions, 7 counts, the last interior vertex uncounted), the packed core module
`LocalWindowCnf.K7…` proves that its UNSAT core follows from the snake conditions `Axioms`
(`sat`), and the replay `LocalWindowUnsat.K7…` refutes the core (`unsat`).  Together they give
`Refuted (winOf ds) (boundsOf syms)` (`Tags.refuted_of_sat`).
{fam}-/

set_option maxRecDepth 100000
{'' if dvs is None else '-- one declaration at a time: parallel elaboration keeps the kernel data of every `decide`' + chr(10) + '-- (1.0 GB for 50 L2 derivations, 0.46 GB without)' + chr(10) + 'set_option Elab.async false' + chr(10)}
namespace Snake9.LocalWindow

{refuted}theorem allRefutedK7_{ci} : AllRefutedList dirKeysK7_{ci} :=
  {term}

end Snake9.LocalWindow
'''


def aggregate_module(chunks):
    n = len(chunks)
    imports = ''.join(f'import LocalWindowDirUnsatK7_{ci}\n' for ci in range(n))
    term = "AllRefutedSrcs.nil'"
    for ci in reversed(range(n)):
        term = f"AllRefutedSrcs.cons' allRefutedK7_{ci}\n    ({term})"
    nk = sum(map(len, chunks))
    return f'''import LocalWindowDirKeysK7
{imports}
/-!
# The {nk} new refutations of the seven-centre bound

Generated by `{ME} final`.
`AllRefutedK7 = AllRefutedSrcs dirChunksK7` (`LocalWindowDirKeysK7`,
`milestones/25-k7-234/lean/scripts/gen_lean_glue7.py keys`) from the {n} chunk theorems `allRefutedK7_<c>` (`LocalWindowDirUnsatK7_<c>`), each built from the
kernel-checked replays `LocalWindowUnsat.K7*` (`milestones/25-k7-234/certify/replay_k7.py`)
and the clause-soundness theorems of the packed core modules `LocalWindowCnf.K7*`.
-/

set_option maxRecDepth 100000

namespace Snake9.LocalWindow

theorem allRefutedK7 : AllRefutedK7 :=
  {term}

end Snake9.LocalWindow

#print axioms Snake9.LocalWindow.allRefutedK7
'''


def final(a):
    chunks = new_chunks(a.keys, a.chunk)
    part = key_parts(chunks, a.keys_per_module)
    sel = range(len(chunks)) if not a.chunks else [int(c) for c in a.chunks.split(',')]
    missing = []
    plan = load_plan(a.plan) if a.plan else None
    unproved = []
    os.makedirs(a.out, exist_ok=True)
    for ci in sel:
        dvs = None
        if plan:
            dvs = {k: derivation(plan, k, a.core) for k in chunks[ci]}
            unproved += [module_name(*k) for k, dv in dvs.items() if dv is None]
            if any(dv is None for dv in dvs.values()):
                continue
            for k, dv in dvs.items():
                if dv[0] in ('L1', 'L2'):
                    assert FK.derivable((None, list(dv[1]['dirs']), list(dv[1]['syms'])),
                                        [tuple(x) for x in dv[1]['lean_bounds']], (None, list(k[0]), list(k[1])))
        for k in chunks[ci]:
            cm = module_name(*k) if not dvs else proof_term(k, dvs[k])[1]
            if not os.path.exists(os.path.join(a.out, 'LocalWindowUnsat', cm + '.lean')):
                missing.append(cm)
        open(os.path.join(a.out, f'LocalWindowDirUnsatK7_{ci}.lean'), 'w').write(
            chunk_module(ci, chunks[ci], part[ci], len(chunks), dvs))
    if unproved:
        raise SystemExit(f'{len(unproved)} keys have neither a certificate nor a certified seed that '
                         f'implies them (run `run --plan` to the end first), e.g. {unproved[:5]}')
    if not a.chunks:
        open(os.path.join(a.out, 'LocalWindowDirUnsatK7.lean'), 'w').write(aggregate_module(chunks))
    print(f'wrote {len(sel)} chunk modules' + ('' if a.chunks else ' and LocalWindowDirUnsatK7.lean') +
          f' in {a.out}; {len(set(missing))} replay modules not generated yet', flush=True)


def cnfsat(a):
    """Rewrite the packed core module of existing core JSONs (CNF regenerated and deleted)."""
    certs = os.path.join(a.work, 'certs')
    os.makedirs(certs, exist_ok=True)
    for n in a.names:
        gz = regen_cnf(json.load(open(os.path.join(a.core, n + '.json'))), os.path.join(certs, n + '.cnf.gz'))
        print(json.dumps(CP.emit(n, certs, a.core, a.out, part_lits=a.part_lits, sat_v2=a.sat_v2)), flush=True)
        os.remove(gz)


def regen(a):
    os.makedirs(a.out, exist_ok=True)
    for n in a.names:
        regen_cnf(json.load(open(os.path.join(a.core, n + '.json'))), os.path.join(a.out, n + '.cnf.gz'))
    print('regenerated', len(a.names), 'CNFs in', a.out)


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    r = sub.add_parser('run')
    r.add_argument('--keys', nargs='+', required=True, help='the key files of the chain')
    r.add_argument('--work', required=True)
    r.add_argument('--out', default=LEAN, help='Lean root that receives LocalWindowCnf/K7*.lean')
    r.add_argument('--core', default=CORE, help='core JSON directory')
    r.add_argument('--log', default=None)
    r.add_argument('--chunk', type=int, default=400, help='--chunk of gen_lean_glue7.py keys')
    r.add_argument('--kinds', default='k6,F,H', help='key kinds to certify (k6, F, H)')
    r.add_argument('--only', nargs='*', default=[], help='only these keys, as DIRS:SYMS digit strings')
    r.add_argument('--limit', type=int, default=0)
    r.add_argument('--max-est', type=float, default=0, help='skip keys with a larger hint estimate')
    r.add_argument('--min-disk-mb', type=int, default=700)
    r.add_argument('--fsize-mb', type=int, default=700, help='cap on a raw CaDiCaL proof')
    r.add_argument('--plan', default='', help='seed plan (families_k7.py): certify its seeds with widened '
                                              'bounds, then the keys their certificates no longer imply')
    c = sub.add_parser('cnfsat')
    c.add_argument('--work', required=True)
    c.add_argument('--out', default=LEAN)
    c.add_argument('--core', default=CORE)
    c.add_argument('names', nargs='+')
    for p in (r, c):
        p.add_argument('--part-lits', type=int, default=PART_LITS,
                       help='`check` in parts of at most this many literals, counters by ctrOKL '
                            '(gen_lean_cnfsat_packed.py --part-lits); 0: one `check`')
        p.add_argument('--sat-v2', action='store_true',
                       help='clause soundness by the checker family TagsW (gen_lean_cnfsat_packed.py --sat-v2)')
    f = sub.add_parser('final')
    f.add_argument('--keys', nargs='+', required=True)
    f.add_argument('--out', default=LEAN)
    f.add_argument('--chunk', type=int, default=400)
    f.add_argument('--keys-per-module', type=int, default=4000, help='as gen_lean_glue7.py keys')
    f.add_argument('--chunks', default='', help='only these chunk modules (no aggregate)')
    f.add_argument('--plan', default='', help='seed plan: derive keys from their seeds (L1/L2)')
    f.add_argument('--core', default=CORE, help='core JSON directory (with --plan)')
    g = sub.add_parser('regen')
    g.add_argument('--out', required=True)
    g.add_argument('--core', default=CORE)
    g.add_argument('names', nargs='+')
    a = ap.parse_args()
    if a.cmd == 'run':
        a.log = a.log or os.path.join(a.work, 'core_progress.jsonl')
        run(a)
    elif a.cmd == 'final':
        final(a)
    elif a.cmd == 'cnfsat':
        cnfsat(a)
    else:
        regen(a)


if __name__ == '__main__':
    main()
