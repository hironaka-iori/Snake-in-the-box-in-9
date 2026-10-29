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

Solver runs are sequential; every CaDiCaL call goes through a wrapper with `nice -n 19` and
a file-size cap on the raw proof.  Resumable: a key whose JSON and Cnf module exist is
skipped.

  nice -n 19 python3 gen_k7_core.py run --keys KEYS.json.gz --work DIR [--out ROOT] [--kinds H,F,k6]
                                        [--only DS:SYMS ...] [--limit N] [--max-est HINTS]
  python3 gen_k7_core.py cnfsat --work DIR [--out ROOT] NAME ...   # rewrite Cnf modules from core JSONs
  python3 gen_k7_core.py final --keys KEYS.json.gz [--out ROOT] [--chunks 0,1,...]
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

def one(dirs, syms, work, certs, cadical, out, core, log, part_lits):
    name, module = case_name(dirs, syms), module_name(dirs, syms)
    mp = os.path.join(core, name + '.json')
    if os.path.exists(mp) and os.path.exists(os.path.join(out, 'LocalWindowCnf', module + '.lean')):
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
    ids, finfo = GC.full_core_ids(name, work, cadical, [1], certs)
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
    json.dump(meta, open(mp, 'w'))
    r = CP.emit(name, certs, core, out, part_lits=part_lits)
    t3 = time.time()
    for p in (gz, os.path.join(work, name + '.cnf')):
        if os.path.exists(p):
            os.remove(p)
    rec = {'name': name, 'module': module, 'kind': meta['kind'], 'variables': enc.nv,
           'clauses': len(enc.clauses), 'cuts': ncuts, 'core': len(ids), 'core_lits': r['lits'],
           'full_hints': finfo['full_hints'], 'cnfsat_src_bytes': r['lean_bytes'], 'check_parts': r['check_parts'],
           'enc_s': round(t1 - t0, 2), 'core_s': round(t2 - t1, 2), 'emit_s': round(t3 - t2, 2)}
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
    keys.sort(key=lambda k: (est.get(k, 1e12), k))       # smallest estimate first
    n = 0
    for k in keys:
        if a.max_est and est.get(k, 0) > a.max_est:
            continue
        if disk_free_mb() < a.min_disk_mb:
            print('stop: disk below %d MB' % a.min_disk_mb, flush=True)
            break
        rec = one(k[0], k[1], a.work, certs, cadical, a.out, a.core, a.log, a.part_lits)
        if rec:
            n += 1
            print(json.dumps(rec), flush=True)
            if a.limit and n >= a.limit:
                break


# ----------------------------------------------------------------- final ---

def lst(c):
    return '[' + ', '.join(map(str, c)) + ']'


def chunk_module(ci, ch, part, n_chunks):
    mods = [module_name(*k) for k in ch]
    imports = ''.join(f'import LocalWindowUnsat.{m}\n' for m in mods)
    refuted = ''.join(f'theorem {m}.refuted : Refuted (winOf {lst(d)}) (boundsOf {lst(s)}) :=\n'
                      f'  Tags.refuted_of_sat {m}.sat {m}.unsat\n\n' for m, (d, s) in zip(mods, ch))
    term = 'trivial'
    for m in reversed(mods):
        term = f'And.intro {m}.refuted\n    ({term})'
    nh = sum(kind_of(*k) == 'H' for k in ch)
    return f'''import LocalWindowTags
import LocalWindowDirKeysK7_P{part}
{imports}
/-!
# Chunk {ci} of the {n_chunks} chunks of new certificates of the seven-centre bound

Generated by `{ME} final`.
For each of the {len(ch)} keys `(ds, syms)` of `dirKeysK7_{ci}` ({nh} of them H9 windows: 9
directions, 7 counts, the last interior vertex uncounted), the packed core module
`LocalWindowCnf.K7…` proves that its UNSAT core follows from the snake conditions `Axioms`
(`sat`), and the replay `LocalWindowUnsat.K7…` refutes the core (`unsat`).  Together they give
`Refuted (winOf ds) (boundsOf syms)` (`Tags.refuted_of_sat`).
-/

set_option maxRecDepth 100000

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
    for ci in sel:
        for k in chunks[ci]:
            if not os.path.exists(os.path.join(a.out, 'LocalWindowUnsat', module_name(*k) + '.lean')):
                missing.append(module_name(*k))
        open(os.path.join(a.out, f'LocalWindowDirUnsatK7_{ci}.lean'), 'w').write(
            chunk_module(ci, chunks[ci], part[ci], len(chunks)))
    if not a.chunks:
        open(os.path.join(a.out, 'LocalWindowDirUnsatK7.lean'), 'w').write(aggregate_module(chunks))
    print(f'wrote {len(sel)} chunk modules' + ('' if a.chunks else ' and LocalWindowDirUnsatK7.lean') +
          f' in {a.out}; {len(missing)} replay modules not generated yet', flush=True)


def cnfsat(a):
    """Rewrite the packed core module of existing core JSONs (CNF regenerated and deleted)."""
    certs = os.path.join(a.work, 'certs')
    os.makedirs(certs, exist_ok=True)
    for n in a.names:
        gz = regen_cnf(json.load(open(os.path.join(a.core, n + '.json'))), os.path.join(certs, n + '.cnf.gz'))
        print(json.dumps(CP.emit(n, certs, a.core, a.out, part_lits=a.part_lits)), flush=True)
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
    c = sub.add_parser('cnfsat')
    c.add_argument('--work', required=True)
    c.add_argument('--out', default=LEAN)
    c.add_argument('--core', default=CORE)
    c.add_argument('names', nargs='+')
    for p in (r, c):
        p.add_argument('--part-lits', type=int, default=PART_LITS,
                       help='`check` in parts of at most this many literals, counters by ctrOKL '
                            '(gen_lean_cnfsat_packed.py --part-lits); 0: one `check`')
    f = sub.add_parser('final')
    f.add_argument('--keys', nargs='+', required=True)
    f.add_argument('--out', default=LEAN)
    f.add_argument('--chunk', type=int, default=400)
    f.add_argument('--keys-per-module', type=int, default=4000, help='as gen_lean_glue7.py keys')
    f.add_argument('--chunks', default='', help='only these chunk modules (no aggregate)')
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
