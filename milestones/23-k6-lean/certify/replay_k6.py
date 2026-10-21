"""Generate and build the kernel replays of the new k6 certificates (set `k6`, prefix `K`).

The analogue of `milestones/10-window-aggregate/scripts/run_direction_replays.py` for the
635 cores of `gen_k6_core.py` (data `milestones/10-window-aggregate/data/lean_core_direction_k6/`).
Differences:

* the CNF of each key is regenerated from its core JSON (`gen_k6_core.regen_cnf`, checked
  by SHA256) into the work directory and deleted afterwards;
* the LRAT is a CaDiCaL proof of the core alone (`gen_lean_core.core_lrat`, full portfolio,
  `--rounds` rounds of core shrinking), ids remapped to the CNF;
* the literal offset is 3000 / 4000 / 5000 from the variable count; offset 5000 (CNFs with
  4000 or more variables, i.e. most six-centre windows) uses the O5k checkers through
  `milestones/23-k6-lean/scripts/gen_lean_lrat_o5k.py` (14- to 17-bit words);
* the checkpoints of the data modules are packed at once (`pack_checkpoints.rewrite`,
  `NatPack.unpackL`), before anything is built.

  python3 replay_k6.py gen --work DIR [--out work/final_lean] [--shard i/n] [--limit N] [NAME ...]
  python3 replay_k6.py measure --work DIR     # hints of the core proofs only (no Lean files)
  python3 replay_k6.py build [--limit N]      # guarded, one module per `lean` call (generated cases only)
  python3 replay_k6.py sweep [--dry-run]      # delete built data sources (K*/Data*.lean)

Cases run smallest first (by the recorded hint estimate); a case whose main module exists is
skipped, so both steps resume.
"""
import argparse, json, os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
S10 = os.path.join(ROOT, 'milestones', '10-window-aggregate', 'scripts')
sys.path.insert(0, S10)
sys.path.insert(0, HERE)
import gen_k6_core as K                 # noqa: E402
import gen_lean_core as GC              # noqa: E402
import pack_checkpoints as PK           # noqa: E402

LEAN = K.LEAN
O5K = os.path.join(ROOT, 'milestones', '23-k6-lean', 'scripts', 'gen_lean_lrat_o5k.py')


def cases():
    per = json.load(open(os.path.join(K.CORE, '_summary.json')))['per_case']
    return sorted(per.items(), key=lambda kv: (kv[1]['hints'], kv[0]))


def offset(nv):
    return 2400 if nv < 2400 else 3000 if nv < 3000 else 4000 if nv < 4000 else 5000


def pack_dir(d):
    """Pack the checkpoint lists of the data modules just written."""
    n = 0
    for f in sorted(os.listdir(d)):
        if f.startswith('Data') and f.endswith('.lean'):
            p = os.path.join(d, f)
            text = open(p).read()
            if 'Snake9.NatPack.unpackL' in text:
                continue
            new, k = PK.rewrite(text)
            if k:
                open(p, 'w').write(new)
                n += 1
    return n


def gen(a):
    certs = os.path.join(a.work, 'certs')
    os.makedirs(certs, exist_ok=True)
    K.register(certs)
    cadical = K.cadical_wrapper(a.work)
    si, sn = map(int, a.shard.split('/'))
    done = spent = 0
    for i, (name, info) in enumerate(cases()):
        if i % sn != si or (a.names and name not in a.names):
            continue
        mod = info['module']
        if os.path.exists(os.path.join(a.out, 'LocalWindowUnsat', mod + '.lean')):
            continue
        if K.disk_free_mb() < a.min_disk_mb:
            raise SystemExit('stop: disk below %d MB' % a.min_disk_mb)
        meta = json.load(open(os.path.join(K.CORE, name + '.json')))
        K.regen_cnf(meta, os.path.join(certs, name + '.cnf.gz'))
        lrat, info2 = GC.core_lrat(name, meta['core_ids'], a.work, cadical, list(range(1, a.seeds + 1)), certs,
                                   rounds=a.rounds)
        off = offset(meta['variables'])
        for bits in ((14, 15, 16, 17) if off == 5000 else (13, 14, 15, 16, 17)):
            cmd = [sys.executable, O5K if off == 5000 else os.path.join(S10, 'gen_lean_lrat.py'),
                   '--work', a.work, '--data', K.CORE, '--out', a.out, '--seg', str(a.seg), '--cp', str(a.cp),
                   '--group', str(a.group), '--wbits', str(bits), '--off', str(off), '--noncomputable-data',
                   '--fast', '--split', name]
            r = subprocess.run(['nice', '-n', '19', *cmd], capture_output=True, text=True)
            if r.returncode == 0:
                npk = pack_dir(os.path.join(a.out, 'LocalWindowUnsat', mod))
                rec = {'case': name, 'module': mod, 'wbits': bits, 'off': off, 'core_lrat_hints': info2['hints'],
                       'core_lrat_lemmas': info2['lemmas'], 'est_hints': info['hints'], 'packed_data': npk,
                       **json.loads(r.stdout.strip().splitlines()[-1])}
                print(json.dumps(rec), flush=True)
                with open(os.path.join(a.work, 'replay_gen.jsonl'), 'a') as f:
                    f.write(json.dumps(rec) + '\n')
                break
            if 'too many slots' not in r.stderr and 'assert nslots' not in r.stderr:
                print(r.stderr[-2000:], file=sys.stderr)
                raise SystemExit(f'generation failed for {name}')
        else:
            raise SystemExit(f'{name}: too many slots even for the widest words')
        for ext in ('.lrat', '.lrat.json', '.core.cnf', '.cnf'):
            p = os.path.join(a.work, name + ext)
            if os.path.exists(p):
                os.remove(p)
        os.remove(os.path.join(certs, name + '.cnf.gz'))
        done += 1
        spent += rec['hints']
        if (a.limit and done >= a.limit) or (a.budget_hints and spent >= a.budget_hints):
            break


def measure(a):
    """Hints of the core proofs that `gen` will replay (core_lrat, same portfolio and seeds),
    without keeping the proofs: one line per case in core_lrat.jsonl of the work directory."""
    certs = os.path.join(a.work, 'certs')
    os.makedirs(certs, exist_ok=True)
    K.register(certs)
    cadical = K.cadical_wrapper(a.work)
    out = os.path.join(a.work, 'core_lrat.jsonl')
    seen = {json.loads(l)['case'] for l in open(out)} if os.path.exists(out) else set()
    for name, info in cases():
        if name in seen:
            continue
        if K.disk_free_mb() < a.min_disk_mb:
            raise SystemExit('stop: disk below %d MB' % a.min_disk_mb)
        meta = json.load(open(os.path.join(K.CORE, name + '.json')))
        K.regen_cnf(meta, os.path.join(certs, name + '.cnf.gz'))
        _, info2 = GC.core_lrat(name, meta['core_ids'], a.work, cadical, list(range(1, a.seeds + 1)), certs,
                                rounds=a.rounds)
        rec = {'case': name, 'module': info['module'], 'est_hints': info['hints'], 'hints': info2['hints'],
               'lemmas': info2['lemmas'], 'producer': info2['producer']}
        with open(out, 'a') as f:
            f.write(json.dumps(rec) + '\n')
        for ext in ('.lrat', '.lrat.json', '.core.cnf', '.cnf'):
            p = os.path.join(a.work, name + ext)
            if os.path.exists(p):
                os.remove(p)
        os.remove(os.path.join(certs, name + '.cnf.gz'))


def build(a):
    # only the cases generated so far (generation and building alternate under the disk cap)
    mods = ['LocalWindowUnsat.' + info['module'] for _, info in cases()
            if os.path.exists(os.path.join(LEAN, 'LocalWindowUnsat', info['module'] + '.lean'))]
    if a.limit:
        mods = mods[:a.limit]
    if not mods:
        raise SystemExit('no generated replay modules')
    cmd = [sys.executable, os.path.join(ROOT, 'work', 'guarded_lake_build.py'), '--jobs', str(a.jobs),
           '--heavy-jobs', str(a.heavy_jobs), '--min-free-gb', str(a.min_free_gb), '--rss-cap-gb', str(a.rss_cap_gb),
           '--trust-mtime', '--direct', '--log', os.path.join(LEAN, '.lake', 'guarded_build_k6.jsonl'), *mods]
    raise SystemExit(subprocess.run(cmd, cwd=LEAN).returncode)


def sweep(a):
    """Delete the data sources `LocalWindowUnsat/K*/Data*.lean` whose `.olean` is built and newer
    (imports only need the `.olean`; `guarded_lake_build.py --trust-mtime` treats them as
    prebuilt).  The same rule as the sweep of the R sets."""
    unsat = os.path.join(LEAN, 'LocalWindowUnsat')
    olean = os.path.join(LEAN, '.lake', 'build', 'lib', 'lean', 'LocalWindowUnsat')
    n = freed = 0
    for d in sorted(os.listdir(unsat)):
        if not d.startswith('K') or not os.path.isdir(os.path.join(unsat, d)):
            continue
        for f in os.listdir(os.path.join(unsat, d)):
            if not (f.startswith('Data') and f.endswith('.lean')):
                continue
            src, o = os.path.join(unsat, d, f), os.path.join(olean, d, f[:-5] + '.olean')
            if os.path.exists(o) and os.path.getmtime(o) > os.path.getmtime(src):
                freed += os.path.getsize(src)
                if not a.dry_run:
                    os.remove(src)
                n += 1
    print('%s %d data sources, %.1f MB; %d MB free' % ('would delete' if a.dry_run else 'deleted', n,
                                                       freed / 2**20, K.disk_free_mb()), flush=True)


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    g = sub.add_parser('gen')
    g.add_argument('--work', required=True)
    g.add_argument('--out', default=LEAN, help='Lean root that receives LocalWindowUnsat/K*')
    g.add_argument('--seg', type=int, default=25000)
    g.add_argument('--cp', type=int, default=3)
    g.add_argument('--group', type=int, default=4)
    g.add_argument('--seeds', type=int, default=2)
    g.add_argument('--rounds', type=int, default=1)
    g.add_argument('--shard', default='0/1')
    g.add_argument('--limit', type=int, default=0)
    g.add_argument('--budget-hints', type=float, default=0,
                   help='stop after the cases generated in this call reach this many hints (a batch)')
    g.add_argument('--min-disk-mb', type=int, default=1500)
    g.add_argument('names', nargs='*')
    m = sub.add_parser('measure')
    m.add_argument('--work', required=True)
    m.add_argument('--seeds', type=int, default=2)
    m.add_argument('--rounds', type=int, default=1)
    m.add_argument('--min-disk-mb', type=int, default=700)
    b = sub.add_parser('build')
    b.add_argument('--jobs', type=int, default=1)
    b.add_argument('--heavy-jobs', type=int, default=2)
    b.add_argument('--min-free-gb', type=float, default=6.0)
    b.add_argument('--rss-cap-gb', type=float, default=6.0)
    b.add_argument('--limit', type=int, default=0)
    w = sub.add_parser('sweep')
    w.add_argument('--dry-run', action='store_true')
    a = ap.parse_args()
    {'gen': gen, 'measure': measure, 'build': build, 'sweep': sweep}[a.cmd](a)


if __name__ == '__main__':
    main()
