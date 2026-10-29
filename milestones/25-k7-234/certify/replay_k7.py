"""Generate and build the packed kernel replays of the new k7 certificates (set `k7`, prefix `K7`).

The analogue of `milestones/23-k6-lean/certify/replay_k6.py gen --packed` for the cores of
`gen_k7_core.py` (data `milestones/10-window-aggregate/data/lean_core_direction_k7/`):

* the CNF of each key is regenerated from its core JSON (`gen_k7_core.regen_cnf`, checked by
  SHA256; H9 keys with `None` for the uncounted last interior vertex) into the work
  directory and deleted afterwards;
* the LRAT is a CaDiCaL proof of the core alone (`gen_lean_core.core_lrat`, the portfolio
  `PORTFOLIO`, `--seeds` seeds, `--rounds` rounds of core shrinking), ids remapped to the CNF;
* the literal offset is 3000 / 4000 / 5000 from the variable count.  Every H9 and F8 CNF has
  more than 4000 variables (radius-4 balls around 7 or 8 centres, and up to 7 counters of 441
  registers), so they use the O5k checkers (`gen_lean_lrat_o5k.py`, 14- to 17-bit words);
* one module per window, `LocalWindowUnsat/K7<ds>A<syms>.lean`, in the production encoding
  of milestones/26-replay-efficiency (`gen_lean_lrat.py --fast --split --noncomputable-data
  --packed`: proofs and checkpoints as `ProofPack` chunks, input slots as `NatPack` chunks).
  It imports the packed core module `LocalWindowCnf.K7…` and proves `K7….unsat : Unsat cnf`.

  python3 replay_k7.py gen --work DIR [--out ROOT] [--shard i/n] [--limit N] [--budget-hints H] [NAME ...]
  python3 replay_k7.py measure --work DIR      # hints of the core proofs only (no Lean files)
  python3 replay_k7.py build [--limit N]       # guarded, one module per `lean` call (generated cases only)

Cases run smallest first (by the full-proof hint estimate of the core JSON); a case whose
replay module exists is skipped, so every step resumes.
"""
import argparse, json, os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
S10 = os.path.join(ROOT, 'milestones', '10-window-aggregate', 'scripts')
sys.path.insert(0, S10)
sys.path.insert(0, HERE)
import gen_k7_core as K                 # noqa: E402
import gen_lean_core as GC              # noqa: E402

LEAN = K.LEAN
O5K = os.path.join(ROOT, 'milestones', '23-k6-lean', 'scripts', 'gen_lean_lrat_o5k.py')


def cases(core):
    out = []
    for f in sorted(os.listdir(core)):
        if f.endswith('.json') and not f.startswith('_'):
            m = json.load(open(os.path.join(core, f)))
            out.append((m['lrat']['hints'], m['name'], m))
    return [(n, m) for _, n, m in sorted(out)]


def offset(nv):
    return 2400 if nv < 2400 else 3000 if nv < 3000 else 4000 if nv < 4000 else 5000


def cleanup(work, certs, name):
    for p in [os.path.join(work, name + ext) for ext in ('.lrat', '.lrat.json', '.core.cnf', '.cnf')] + \
             [os.path.join(certs, name + '.cnf.gz')]:
        if os.path.exists(p):
            os.remove(p)


def gen(a):
    certs = os.path.join(a.work, 'certs')
    os.makedirs(certs, exist_ok=True)
    cadical = K.cadical_wrapper(a.work, a.fsize_mb)
    si, sn = map(int, a.shard.split('/'))
    done = spent = 0
    for i, (name, meta) in enumerate(cases(a.core)):
        if i % sn != si or (a.names and name not in a.names):
            continue
        mod = meta['module'].split('.')[-1]
        if os.path.exists(os.path.join(a.out, 'LocalWindowUnsat', mod + '.lean')):
            continue
        if K.disk_free_mb() < a.min_disk_mb:
            raise SystemExit('stop: disk below %d MB' % a.min_disk_mb)
        K.regen_cnf(meta, os.path.join(certs, name + '.cnf.gz'))
        _, info = GC.core_lrat(name, meta['core_ids'], a.work, cadical, list(range(1, a.seeds + 1)), certs,
                               rounds=a.rounds)
        off = offset(meta['variables'])
        for bits in ((14, 15, 16, 17) if off == 5000 else (13, 14, 15, 16, 17)):
            cmd = [sys.executable, O5K if off == 5000 else os.path.join(S10, 'gen_lean_lrat.py'),
                   '--work', a.work, '--data', a.core, '--out', a.out, '--seg', str(a.seg), '--cp', str(a.cp),
                   '--group', str(a.group), '--wbits', str(bits), '--off', str(off), '--noncomputable-data',
                   '--fast', '--split', '--packed', '--pack-chunk', str(a.pack_chunk), name]
            r = subprocess.run(['nice', '-n', '19', *cmd], capture_output=True, text=True)
            if r.returncode == 0:
                rec = {'case': name, 'module': mod, 'kind': meta.get('kind'), 'variables': meta['variables'],
                       'core': len(meta['core_ids']), 'wbits': bits, 'off': off,
                       'core_lrat_hints': info['hints'], 'core_lrat_lemmas': info['lemmas'],
                       'est_hints': meta['lrat']['hints'], 'producer': info['producer'],
                       'replay_src_bytes': os.path.getsize(os.path.join(a.out, 'LocalWindowUnsat', mod + '.lean')),
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
        cleanup(a.work, certs, name)
        done += 1
        spent += rec['hints']
        if (a.limit and done >= a.limit) or (a.budget_hints and spent >= a.budget_hints):
            break


def measure(a):
    """Hints of the core proofs that `gen` will replay (core_lrat, same portfolio, seeds and
    rounds), without keeping the proofs: one line per case in core_lrat.jsonl of the work
    directory."""
    certs = os.path.join(a.work, 'certs')
    os.makedirs(certs, exist_ok=True)
    cadical = K.cadical_wrapper(a.work, a.fsize_mb)
    out = os.path.join(a.work, 'core_lrat.jsonl')
    seen = {(json.loads(l)['case'], json.loads(l).get('seeds'), json.loads(l).get('rounds'))
            for l in open(out)} if os.path.exists(out) else set()
    for name, meta in cases(a.core):
        if (name, a.seeds, a.rounds) in seen or (a.names and name not in a.names):
            continue
        if K.disk_free_mb() < a.min_disk_mb:
            raise SystemExit('stop: disk below %d MB' % a.min_disk_mb)
        K.regen_cnf(meta, os.path.join(certs, name + '.cnf.gz'))
        _, info = GC.core_lrat(name, meta['core_ids'], a.work, cadical, list(range(1, a.seeds + 1)), certs,
                               rounds=a.rounds)
        rec = {'case': name, 'module': meta['module'].split('.')[-1], 'seeds': a.seeds, 'rounds': a.rounds,
               'est_hints': meta['lrat']['hints'], 'hints': info['hints'], 'lemmas': info['lemmas'],
               'producer': info['producer']}
        print(json.dumps(rec), flush=True)
        with open(out, 'a') as f:
            f.write(json.dumps(rec) + '\n')
        cleanup(a.work, certs, name)


def build(a):
    """`work/guarded_lake_build.py --direct --trust-mtime` on the replays generated so far
    (generation and building alternate under the disk cap).  The closure includes the packed
    core modules `LocalWindowCnf.K7*` (1.2-1.6 GB each with `--part-lits 4000`); both kinds are
    the heavy jobs (the replays need 0.6-2.5 GB)."""
    mods = ['LocalWindowUnsat.' + m['module'].split('.')[-1] for _, m in cases(a.core)
            if os.path.exists(os.path.join(a.out, 'LocalWindowUnsat', m['module'].split('.')[-1] + '.lean'))]
    if a.limit:
        mods = mods[:a.limit]
    if not mods:
        raise SystemExit('no generated replay modules')
    os.makedirs(os.path.join(a.out, '.lake'), exist_ok=True)
    cmd = [sys.executable, os.path.join(ROOT, 'work', 'guarded_lake_build.py'), '--root', a.out,
           '--jobs', str(a.jobs), '--heavy', r'^LocalWindow(Unsat|Cnf)\.K7', '--heavy-jobs', str(a.heavy_jobs),
           '--min-free-gb', str(a.min_free_gb), '--rss-cap-gb', str(a.rss_cap_gb), '--trust-mtime', '--direct',
           '--log', os.path.join(a.out, '.lake', 'guarded_build_k7.jsonl'), *mods]
    raise SystemExit(subprocess.run(cmd, cwd=a.out).returncode)


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    g = sub.add_parser('gen')
    g.add_argument('--work', required=True)
    g.add_argument('--out', default=LEAN, help='Lean root that receives LocalWindowUnsat/K7*')
    g.add_argument('--seg', type=int, default=25000)
    g.add_argument('--cp', type=int, default=3)
    g.add_argument('--group', type=int, default=4)
    g.add_argument('--pack-chunk', type=int, default=16384, help='bytes per ProofPack chunk')
    g.add_argument('--shard', default='0/1')
    g.add_argument('--limit', type=int, default=0)
    g.add_argument('--budget-hints', type=float, default=0,
                   help='stop after the cases generated in this call reach this many hints (a batch)')
    g.add_argument('names', nargs='*')
    m = sub.add_parser('measure')
    m.add_argument('--work', required=True)
    m.add_argument('names', nargs='*')
    for p in (g, m):
        p.add_argument('--core', default=K.CORE)
        p.add_argument('--seeds', type=int, default=2)
        p.add_argument('--rounds', type=int, default=1)
        p.add_argument('--min-disk-mb', type=int, default=1500)
        p.add_argument('--fsize-mb', type=int, default=700, help='cap on a raw CaDiCaL proof')
    b = sub.add_parser('build')
    b.add_argument('--core', default=K.CORE)
    b.add_argument('--out', default=LEAN, help='Lean root of the replays (guarded_lake_build.py --root)')
    b.add_argument('--jobs', type=int, default=1)
    b.add_argument('--heavy-jobs', type=int, default=3)
    b.add_argument('--min-free-gb', type=float, default=4.0)
    b.add_argument('--rss-cap-gb', type=float, default=3.5)
    b.add_argument('--limit', type=int, default=0)
    a = ap.parse_args()
    {'gen': gen, 'measure': measure, 'build': build}[a.cmd](a)


if __name__ == '__main__':
    main()
