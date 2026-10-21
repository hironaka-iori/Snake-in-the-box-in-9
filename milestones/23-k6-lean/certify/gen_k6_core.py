"""UNSAT cores and clause-soundness sources of the new certificates of the k6 bound 235.

The key set `../full_product/keys_235.json` has 1,287 keys.  652 of them are keys of the
replayed 237/236 sets (`dirKeysR4b`, `dirKeysR4`) and are reused as they are (see
`work/final_lean/LocalWindowDirGlue6.lean`).  This script certifies the other 635
(16 four-centre, 577 five-centre, 42 six-centre radius-4 windows), set name `k6`, Lean
module prefix `K`:

  1. the CNF: `wincert.Encoding(winOf dirs, alpha, radius 4)` plus the lazy cycle cuts
     that `wincert.decide` adds until the solver answers UNSAT.  The cuts are recorded (as
     vertex lists) in the core JSON, so the CNF is regenerated exactly from the JSON
     (`regen_cnf`; its SHA256 is recorded).  No CNF is committed.
  2. the UNSAT core: as `gen_lean_core.py --set r4 --no-core-lrat`, i.e. `full_core_ids`
     (the toolchain CaDiCaL with `--lrat`, configurations `FULL_PORTFOLIO`, each proof
     trimmed to the dependencies of the empty clause, the smallest kept; the clauses its
     hints use are the core).  The hint count of that proof is recorded as the estimate.
     The LRAT replayed in Lean is made later from the core alone by `core_lrat` (the
     full `PORTFOLIO`), when the replays are generated.
  3. `work/final_lean/LocalWindowCnf/K<dirs>A<syms>.lean` (noncomputable core data) and
     `work/final_lean/LocalWindowSat/K<dirs>A<syms>.lean` (packed clause soundness,
     `gen_lean_sat.process`, which re-derives every clause and its tag from the encoding).
  4. `data/lean_core_direction_k6/NAME.json` per key, `_summary.json`, and with `--finish`
     the keys module `LocalWindowDirKeysK6.lean` and the aggregate `LocalWindowDirSatK6.lean`.

Solver runs are sequential (one core); every CaDiCaL call goes through a wrapper with
`nice -n 19` and a file-size cap on the raw proof.  Resumable: keys whose JSON and Cnf
module exist are skipped.

  nice -n 19 python3 gen_k6_core.py run --work DIR [--limit N] [--max-est HINTS]
  python3 gen_k6_core.py finish
  python3 gen_k6_core.py glue --tag K235                  # LocalWindowDirGlue6K235.lean
  python3 gen_k6_core.py final --tag K235 --bound 235     # LocalWindowDirUnsatK6, UpperBound235
  python3 gen_k6_core.py regen --out CERTDIR [NAME ...]   # CNFs (.cnf.gz) for core_lrat
"""
import argparse, gzip, hashlib, json, os, shutil, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
S10 = os.path.join(ROOT, 'milestones', '10-window-aggregate', 'scripts')
sys.path.insert(0, S10)
import wincert                         # noqa: E402
import gen_lean_core as GC             # noqa: E402
import gen_lean_sat as GS              # noqa: E402

LEAN = os.path.join(ROOT, 'work', 'final_lean')
DATA10 = os.path.join(ROOT, 'milestones', '10-window-aggregate', 'data')
CORE = os.path.join(DATA10, 'lean_core_direction_k6')
KEYS = os.path.join(ROOT, 'milestones', '23-k6-lean', 'full_product', 'keys_235.json')
TOOLCHAIN_CADICAL = '/home/user/lean-deps/toolchain/lean-4.19.0-linux/bin/cadical'
FSIZE_KB = 700 * 1024        # raw proof cap (disk budget)
RADIUS = 4
ME = 'milestones/23-k6-lean/certify/gen_k6_core.py'


def lean_keys(mod):
    import re
    src = open(os.path.join(LEAN, mod + '.lean')).read()
    return [(tuple(map(int, d.split(','))), tuple(map(int, s.split(','))))
            for d, s in re.findall(r'\(\[([\d, ]+)\], \[([\d, ]+)\]\)', src)]


def split_keys():
    """(reused from R4b, reused from R4 only, new) in the order of keys_235.json."""
    ks = [(tuple(d), tuple(GC.dir_syms(a))) for d, a in json.load(open(KEYS))['keys']]
    b, r = set(lean_keys('LocalWindowDirKeysR4b')), set(lean_keys('LocalWindowDirKeysR4'))
    return ([k for k in ks if k in b], [k for k in ks if k not in b and k in r],
            [k for k in ks if k not in b and k not in r])


def case_name(dirs, syms):
    alpha = GC.dir_bounds(syms)
    return 'd' + ''.join(map(str, dirs)) + '_a' + '_'.join(
        f'{lo}' if lo == hi else f'{lo}-{hi}' for lo, hi in alpha)


def encoding(dirs, syms):
    alpha = [lo if lo == hi else (lo, hi) for lo, hi in GC.dir_bounds(syms)]
    return wincert.Encoding(wincert.window_from_dirs(list(dirs)), alpha, RADIUS)


def write_gz_cnf(enc, path):
    """Plain DIMACS text, gzipped with mtime 0; returns the SHA256 of the text."""
    txt = f'p cnf {enc.nv} {len(enc.clauses)}\n' + ''.join(' '.join(map(str, c)) + ' 0\n' for c in enc.clauses)
    data = txt.encode()
    with gzip.GzipFile(path, 'wb', mtime=0) as g:
        g.write(data)
    return hashlib.sha256(data).hexdigest()


def regen_cnf(meta, path):
    """The CNF of a core JSON: the encoding plus its recorded cycle cuts (checked by SHA256)."""
    enc = encoding(meta['dirs'], meta['syms'])
    for cyc in meta['cycle_cuts']:
        enc.add_cycle_cut(cyc)
    sha = write_gz_cnf(enc, path)
    assert sha == meta['cnf_sha256'] and len(enc.clauses) == meta['cnf_clauses'], meta['name']
    return path


def cadical_wrapper(work):
    p = os.path.join(work, 'cadical_nice.sh')
    open(p, 'w').write(f'#!/bin/bash\nulimit -f {FSIZE_KB}\nexec nice -n 19 {TOOLCHAIN_CADICAL} "$@"\n')
    os.chmod(p, 0o755)
    return p


def register(certs):
    GC.CADICAL_SETS['k6'] = dict(index='(k6) ' + os.path.relpath(KEYS, DATA10), certs=certs, core=CORE,
                                 prefix='K', keys_mod='LocalWindowDirKeysK6', keys='dirKeysK6',
                                 premise='AllRefutedK6', bound=235, reuse=None, radius=RADIUS,
                                 title='The {n} new radius-4 window certificates of the k6 bound 235')


def disk_free_mb():
    st = os.statvfs('/')
    return st.f_bavail * st.f_frsize // (1 << 20)


def one(dirs, syms, work, certs, cadical, log):
    name = case_name(dirs, syms)
    module = GC.dir_module(list(dirs), list(syms), 'K')
    mp = os.path.join(CORE, name + '.json')
    if os.path.exists(mp) and os.path.exists(os.path.join(LEAN, 'LocalWindowSat', module + '.lean')):
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
    case = {'case': name, 'dirs': list(dirs), 'alpha': [list(a) for a in GC.dir_bounds(syms)], 'radius': RADIUS,
            'variables': enc.nv, 'clauses': len(enc.clauses), 'cnf_sha256': sha}
    r = GC.dir5_one((case, work, cadical, [1], 'k6', 1, 'skip'))
    t2 = time.time()
    meta = json.load(open(mp))
    meta.update({'cycle_cuts': cuts, 'base_clauses': npre,
                 'cnf_source': 'regenerated: wincert.Encoding(winOf dirs, boundsOf syms, radius 4) plus '
                               'cycle_cuts (in order); SHA256 cnf_sha256 (gen_k6_core.regen_cnf)',
                 'hash_source': 'gen_k6_core.py'})
    json.dump(meta, open(mp, 'w'))
    # the Cnf module: say where the CNF comes from
    cp = os.path.join(LEAN, 'LocalWindowCnf', module + '.lean')
    src = open(cp).read()
    src = (src.replace('`milestones/10-window-aggregate/scripts/gen_lean_core.py --set k6`', '`' + ME + '`')
              .replace('clauses of the committed CNF', 'clauses of the CNF (regenerated from\n'
                       '`milestones/10-window-aggregate/data/lean_core_direction_k6/%s.json`)' % name))
    open(cp, 'w').write(src)
    GS.process(name, True, certs, CORE, True)
    t3 = time.time()
    for p in (gz, os.path.join(work, name + '.cnf')):
        if os.path.exists(p):
            os.remove(p)
    rec = {'name': name, 'module': module, 'variables': enc.nv, 'clauses': len(enc.clauses), 'cuts': ncuts,
           'core': len(meta['core_ids']), 'hints': meta['lrat']['hints'], 'lemmas': meta['lrat']['lemmas'],
           'enc_s': round(t1 - t0, 1), 'core_s': round(t2 - t1, 1), 'sat_s': round(t3 - t2, 1)}
    with open(log, 'a') as f:
        f.write(json.dumps(rec) + '\n')
    return rec


def order_new(new, costs_path):
    est = {}
    if costs_path and os.path.exists(costs_path):
        for o in json.load(open(costs_path)):
            est[(tuple(o['dirs']), tuple(o['syms']))] = o['est_hints']
    return sorted(new, key=lambda k: (est.get(k, 1e9), k)), est


def run(a):
    os.makedirs(CORE, exist_ok=True)
    os.makedirs(a.work, exist_ok=True)
    certs = os.path.join(a.work, 'certs')
    os.makedirs(certs, exist_ok=True)
    register(certs)
    cadical = cadical_wrapper(a.work)
    _, _, new = split_keys()
    assert len(new) == 635, len(new)
    keys, est = order_new(new, a.costs)
    n = 0
    for k in keys:
        if a.max_est and est.get(k, 0) > a.max_est:
            continue
        if disk_free_mb() < a.min_disk_mb:
            print('stop: disk below %d MB' % a.min_disk_mb, flush=True)
            break
        try:
            rec = one(k[0], k[1], a.work, certs, cadical, a.log)
        except (AssertionError, subprocess.SubprocessError) as e:
            with open(a.log, 'a') as f:
                f.write(json.dumps({'name': case_name(*k), 'failed': str(e)[:300]}) + '\n')
            for f_ in os.listdir(a.work):   # leftovers of the failed key
                if f_.startswith(case_name(*k)):
                    os.remove(os.path.join(a.work, f_))
            continue
        if rec:
            n += 1
            print(json.dumps(rec), flush=True)
            if a.limit and n >= a.limit:
                break


def keys_module():
    """LocalWindowDirKeysK6.lean (from the key split alone); returns the keys in its order."""
    _, _, new = split_keys()
    keys = sorted(new, key=lambda k: (len(k[0]), k[0], k[1]))
    body = ',\n  '.join(f'({list(d)}, {list(s)})' for d, s in keys)
    src = f'''import LocalWindowDirModel

/-!
# The {len(keys)} new radius-4 window certificates of the k6 bound 235

Generated by `{ME}`: the keys of `milestones/23-k6-lean/full_product/keys_235.json` that are
not keys of `dirKeysR4b` (237) or `dirKeysR4` (236).  The certificate of key `(ds, syms)` is the
module `LocalWindowCnf.K<ds>A<syms>`: the UNSAT core of the radius-4 local CNF of the canonical
window `winOf ds` with count bounds `boundsOf syms`.
-/

namespace Snake9.LocalWindow

def dirKeysK6 : List (List Nat × List Nat) := [
  {body}]

/-- The {len(keys)} new certificate statements of the k6 bound 235. -/
def AllRefutedK6 : Prop := AllRefutedList dirKeysK6

end Snake9.LocalWindow
'''
    p = os.path.join(LEAN, 'LocalWindowDirKeysK6.lean')
    if not (os.path.exists(p) and open(p).read() == src):
        open(p, 'w').write(src)
    return keys


def glue(a):
    """LocalWindowDirGlue6<T>.lean: `AllRefuted6<T>` (the premise of the k6 chain, key list of
    `gen_lean_automaton6.py --tag T`, i.e. `LocalWindowDirKeys6<T>`) from AllRefuted237,
    AllRefuted236 and AllRefutedK6, by `allRefuted_of_merge3` and one kernel merge check."""
    sys.path.insert(0, os.path.join(ROOT, 'milestones', '23-k6-lean', 'scripts'))
    import gen_lean_automaton6 as GA
    T = a.tag
    keys6 = GA.load_keys([KEYS])           # the generator's order (= dirKeys6<T>)
    km = os.path.join(LEAN, f'LocalWindowDirKeys6{T}.lean')
    if os.path.exists(km):
        import re
        src = open(km).read()
        got = [(tuple(map(int, d.split(','))), tuple(map(int, s.split(','))))
               for d, s in re.findall(r'\(\[([\d, ]+)\], \[([\d, ]+)\]\)', src)]
        assert got == keys6, 'LocalWindowDirKeys6%s.lean does not match keys_235.json' % T
    srcs = [lean_keys('LocalWindowDirKeysR4b'), lean_keys('LocalWindowDirKeysR4'), keys_module()]
    pos = [{k: i for i, k in enumerate(s)} for s in srcs]
    tags, last = [], [-1, -1, -1]
    for k in keys6:
        j = next(j for j in range(3) if k in pos[j])
        assert pos[j][k] > last[j], 'source %d is not in the order of the key list' % j
        last[j] = pos[j][k]
        tags.append(j)
    cnt = [tags.count(j) for j in range(3)]
    body = ',\n  '.join(', '.join(map(str, tags[t:t + 40])) for t in range(0, len(tags), 40))
    out = os.path.join(LEAN, f'LocalWindowDirGlue6{T}.lean')
    open(out, 'w').write(f'''import LocalWindowDirGlue6
import LocalWindowDirKeysR4b
import LocalWindowDirKeysR4
import LocalWindowDirKeysK6
import LocalWindowDirKeys6{T}

/-!
# The premise of the six-centre chain `{T}` from three certificate sets

Generated by `{ME} glue --tag {T}`.  Each of the {len(keys6)} keys of `dirKeys6{T}` is found in
one source: {cnt[0]} in `dirKeysR4b` (the bound 237), {cnt[1]} in `dirKeysR4` only (the bound
236), {cnt[2]} in `dirKeysK6` (the new certificates).  All four lists are sorted by
(length, directions, counts), so `merge6{T}` names the source of each key and `mergeOK` checks
it by one merge in the kernel.
-/

namespace Snake9.LocalWindow

def merge6{T} : List Nat := [
  {body}]

theorem merge6{T}_ok : mergeOK [dirKeysR4b, dirKeysR4, dirKeysK6] dirKeys6{T} merge6{T} = true := by
  decide +kernel

theorem allRefuted6{T}_of_parts (h237 : AllRefuted237) (h236 : AllRefuted236) (hk6 : AllRefutedK6) :
    AllRefuted6{T} :=
  allRefuted_of_merge3 h237 h236 hk6 merge6{T}_ok

end Snake9.LocalWindow

#print axioms Snake9.LocalWindow.allRefuted6{T}_of_parts
''')
    print('wrote', out, cnt, flush=True)


def finish(a):
    """_summary.json, the keys module of the new certificates and the Sat aggregate."""
    _, _, new = split_keys()
    metas, missing = [], []
    for d, s in new:
        p = os.path.join(CORE, case_name(d, s) + '.json')
        if os.path.exists(p):
            metas.append(json.load(open(p)))
        else:
            missing.append(case_name(d, s))
    tot = {'core_clauses': 0, 'cnf_clauses': 0, 'lemmas': 0, 'hints': 0, 'cadical': 0, 'variables_ge_4000': 0}
    per = {}
    for m in metas:
        tot['core_clauses'] += len(m['core_ids']); tot['cnf_clauses'] += m['cnf_clauses']
        tot['lemmas'] += m['lrat']['lemmas']; tot['hints'] += m['lrat']['hints']; tot['cadical'] += 1
        tot['variables_ge_4000'] += m['variables'] >= 4000
        per[m['name']] = {'module': m['module'].split('.')[-1], 'core_clauses': len(m['core_ids']),
                          'cnf_clauses': m['cnf_clauses'], 'variables': m['variables'],
                          'checker_offset': 5000 if m['variables'] >= 4000 else 4000 if m['variables'] >= 3000
                          else 3000 if m['variables'] >= 2400 else 2400,
                          'hash_source': m['hash_source'], **m['lrat']}
    json.dump({'set': 'k6', 'cases': len(metas), 'missing': missing, 'totals': tot, 'per_case': per,
               'note': 'New certificates of the k6 bound 235 (keys_235.json minus the keys of dirKeysR4b and '
                       'dirKeysR4).  lemmas/hints: trimmed cadical --lrat proof of the full CNF (estimate; '
                       'the replay uses core_lrat on the core).  checker_offset: literal offset of the '
                       'LRAT checker (5000 = the O5k checkers of milestone 23).'},
              open(os.path.join(CORE, '_summary.json'), 'w'), indent=1)
    print('summary', len(metas), 'cores,', len(missing), 'missing', tot, flush=True)
    if missing:
        return
    keys = keys_module()
    by_key = {(tuple(m['dirs']), tuple(m['syms'])): m['module'].split('.')[-1] for m in metas}
    assert set(by_key) == set(keys)
    order = [by_key[k] for k in keys]
    imports = ''.join(f'import LocalWindowSat.{m}\n' for m in sorted(order))
    unsat = ' ∧\n  '.join(f'Unsat {m}.cnf' for m in order)
    hs = ', '.join(f'h{i}' for i in range(len(order)))
    terms = ''.join(f'\n    (And.intro (Tags.refuted_of_sat {m}.sat h{i})' for i, m in enumerate(order))
    open(os.path.join(LEAN, 'LocalWindowDirSatK6.lean'), 'w').write(f'''import LocalWindowDirKeysK6
import LocalWindowTags
{imports}
/-!
# The {len(order)} new k6 certificates from their core refutations

Generated by `{ME}`.  Each module `LocalWindowSat.K…` proves that its UNSAT core follows from
the snake axioms (`sat`).  Hence the {len(order)} refutations `Unsat K….cnf` (listed in the order
of `dirKeysK6`) give `AllRefutedK6`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow

/-- Refutations of the {len(order)} new cores, in the order of `dirKeysK6`. -/
def AllUnsatK6 : Prop :=
  {unsat}

theorem allRefutedK6_of_unsat (h : AllUnsatK6) : AllRefutedK6 := by
  obtain ⟨{hs}⟩ := h
  exact{terms} trivial{")" * len(order)}

end Snake9.LocalWindow
''')
    print('wrote LocalWindowDirKeysK6.lean and LocalWindowDirSatK6.lean', flush=True)


def final(a):
    """The two modules that close the chain once the replays are built:

    * `work/final_lean/LocalWindowDirUnsatK6.lean`: the 635 replays `LocalWindowUnsat.K*`
      (generated by `replay_k6.py gen`, not committed) and the `sat` theorems give
      `allRefutedK6`;
    * `work/spectral/stronger/UpperBound<N>.lean`: `upper_bound_<N>` from
      `upper_<N>_of_refuted6<T>` (`gen_lean_chain6.py --tag T`) and the glue
      `allRefuted6<T>_of_parts` applied to `allRefuted237`, `allRefuted236`, `allRefutedK6`."""
    T, N = a.tag, a.bound
    keys = keys_module()
    metas = [json.load(open(os.path.join(CORE, case_name(d, s) + '.json'))) for d, s in keys]
    order = [m['module'].split('.')[-1] for m in metas]
    imports = ''.join(f'import LocalWindowUnsat.{m}\n' for m in order)
    terms = ',\n   '.join(f'{m}.unsat' for m in order)
    open(os.path.join(LEAN, 'LocalWindowDirUnsatK6.lean'), 'w').write(f'''import LocalWindowDirSatK6
{imports}
/-!
# The {len(order)} new k6 refutations

Generated by `{ME} final`.  Combines the kernel-checked LRAT refutations
`LocalWindowUnsat.K*` (generated by `milestones/23-k6-lean/certify/replay_k6.py gen`, not
committed) with the `sat` theorems of `LocalWindowDirSatK6` into `AllRefutedK6`.
-/

set_option maxRecDepth 100000

namespace Snake9.LocalWindow

theorem allUnsatK6 : AllUnsatK6 :=
  ⟨{terms}⟩

theorem allRefutedK6 : AllRefutedK6 := allRefutedK6_of_unsat allUnsatK6

end Snake9.LocalWindow

#print axioms Snake9.LocalWindow.allRefutedK6
''')
    stronger = os.path.join(ROOT, 'work', 'spectral', 'stronger')
    open(os.path.join(stronger, f'UpperBound{N}.lean'), 'w').write(f'''import AggregateDirection6{T}
import LocalWindowDirGlue6{T}
import LocalWindowDirUnsatR4b
import LocalWindowDirUnsatR4
import LocalWindowDirUnsatK6

/-!
# Unconditional bound {N}

Generated by `{ME} final --tag {T} --bound {N}`.  The premise `AllRefuted6{T}` of
`upper_{N}_of_refuted6{T}` (the six-centre automaton `{T}`) is assembled by
`allRefuted6{T}_of_parts` from three sets of kernel-checked window refutations: the 387 keys
of the bound 237 (`allRefuted237`), the 732 keys of the bound 236 (`allRefuted236`) and the
{len(order)} new certificates (`allRefutedK6`).
-/

namespace Snake9

theorem allRefuted6{T} : LocalWindow.AllRefuted6{T} :=
  LocalWindow.allRefuted6{T}_of_parts LocalWindow.allRefuted237 LocalWindow.allRefuted236
    LocalWindow.allRefutedK6

theorem upper_bound_{N} {{m : Nat}} (p : Snake m) : m ≤ {N} :=
  upper_{N}_of_refuted6{T} allRefuted6{T} p

theorem verified_interval_191_{N} :
    Nonempty (Snake 191) ∧ ∀ m, Nonempty (Snake m) → m ≤ {N} := by
  refine ⟨lower_bound, ?_⟩
  rintro m ⟨p⟩
  exact upper_bound_{N} p

end Snake9

#print axioms Snake9.upper_bound_{N}
#print axioms Snake9.verified_interval_191_{N}
''')
    print('wrote LocalWindowDirUnsatK6.lean and UpperBound%d.lean' % N, flush=True)


def regen(a):
    os.makedirs(a.out, exist_ok=True)
    names = a.names or sorted(json.load(open(os.path.join(CORE, '_summary.json')))['per_case'])
    for n in names:
        regen_cnf(json.load(open(os.path.join(CORE, n + '.json'))), os.path.join(a.out, n + '.cnf.gz'))
    print('regenerated', len(names), 'CNFs in', a.out)


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    r = sub.add_parser('run')
    r.add_argument('--work', required=True)
    r.add_argument('--log', default=None)
    r.add_argument('--costs', default=None, help='JSON list {dirs, syms, est_hints}: smallest first')
    r.add_argument('--limit', type=int, default=0)
    r.add_argument('--max-est', type=float, default=0, help='skip keys with a larger estimate')
    r.add_argument('--min-disk-mb', type=int, default=700)
    sub.add_parser('finish')
    fi = sub.add_parser('final')
    fi.add_argument('--tag', default='K235')
    fi.add_argument('--bound', type=int, default=235)
    gl = sub.add_parser('glue')
    gl.add_argument('--tag', default='K235')
    g = sub.add_parser('regen')
    g.add_argument('--out', required=True)
    g.add_argument('names', nargs='*')
    a = ap.parse_args()
    if a.cmd == 'run':
        a.log = a.log or os.path.join(a.work, 'progress.jsonl')
        run(a)
    elif a.cmd == 'finish':
        finish(a)
    elif a.cmd == 'glue':
        glue(a)
    elif a.cmd == 'final':
        final(a)
    else:
        regen(a)


if __name__ == '__main__':
    main()
