"""Generate and kernel-check the LRAT replays of the direction-window cores.

`--set direction`: the 145 windows of the 239 bound; `--set direction5`: the 175 pruned
five-centre windows of the 238 bound; `--set r4`: the radius-4 set.

Step 1 (`gen`): for each case of the set's core directory (smallest proof first) run
gen_lean_lrat.py --fast (checker LratFast) with the literal offset chosen from the
variable count (2400, 3000 or 4000) and 13-, 14- or 15-bit words (LratFast14/15), the
smallest width whose database fits.  With --split the checker is LratFast2 (cached start
database, about 1.7 times faster kernel checks), whose keys must stay below 2^(bits-1), and
16-bit words are also tried.  Cases whose main module already exists are skipped, so the
step resumes.
Generation runs one case at a time (the largest LRAT files need a few GB in Python).

Step 2 (`build`): build every LocalWindowUnsat.D* module through
work/guarded_lake_build.py, which bounds concurrent Lean processes and memory (with
--direct it calls `lean` itself instead of `lake build`, which saves several seconds of
lake start-up per module).

  python run_direction_replays.py gen   --work ~/lean-deps/lrat-direction
  python run_direction_replays.py build --jobs 3
"""
import argparse, json, os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
DATA = os.path.join(HERE, '..', 'data', 'lean_core_direction')
UNSAT = os.path.join(ROOT, 'work', 'final_lean', 'LocalWindowUnsat')


def data_dir(a):
    return DATA + {'direction': '', 'direction5': '5', 'r4': '_r4', 'r4b': '_r4b'}[a.set]


def cases(a):
    summary = json.load(open(os.path.join(data_dir(a), '_summary.json')))['per_case']
    return sorted(summary.items(), key=lambda kv: kv[1]['hints'])


def gen(a):
    si, sn = map(int, a.shard.split('/'))
    for i, (name, info) in enumerate(cases(a)):
        if i % sn != si:
            continue
        mod = info['module']
        if os.path.exists(os.path.join(UNSAT, mod + '.lean')):
            continue
        meta = json.load(open(os.path.join(data_dir(a), name + '.json')))
        if meta.get('lrat_producer', '').startswith('core_lrat'):
            # cadical-cored window of the 238 set: the proof is regenerated from the core
            import gen_lean_core
            cadical = a.cadical or os.path.join(
                subprocess.check_output(['lean', '--print-prefix'], text=True).strip(), 'bin', 'cadical')
            certs = gen_lean_core.CADICAL_SETS[a.set]['certs']
            gen_lean_core.core_lrat(name, meta['core_ids'], a.work, cadical, list(range(1, a.seeds + 1)), certs,
                                    rounds=a.rounds)
        # literal offset above the variable count: 2400 / 3000 / 4000 (see gen_checker_variants.py)
        nv = meta.get('variables', 0)
        off = 2400 if nv < 2400 else 3000 if nv < 3000 else 4000
        assert nv < 4000, (name, nv)
        for bits in ((13, 14, 15, 16, 17) if a.split else (13, 14, 15, 16)):
            cmd = [sys.executable, os.path.join(HERE, 'gen_lean_lrat.py'), '--work', a.work,
                   '--data', data_dir(a), '--seg', str(a.seg), '--cp', str(a.cp), '--group', str(a.group),
                   '--wbits', str(bits), '--off', str(off), '--noncomputable-data', '--fast',
                   *(['--split'] if a.split else []), name]
            r = subprocess.run(cmd, capture_output=True, text=True)
            if r.returncode == 0:
                print(json.dumps({'case': name, 'module': mod, 'wbits': bits, 'off': off,
                                  'split': a.split, 'hints': info['hints']}), flush=True)
                if a.drop_lrat:   # regenerated deterministically by core_lrat when needed again
                    for ext in ('.lrat', '.lrat.json', '.core.cnf'):
                        p = os.path.join(a.work, name + ext)
                        if os.path.exists(p):
                            os.remove(p)
                break
            if 'too many slots' not in r.stderr and 'assert nslots' not in r.stderr:
                print(r.stderr[-2000:], file=sys.stderr)
                raise SystemExit(f'generation failed for {name}')
        else:
            raise SystemExit(f'{name}: too many slots even for the widest words')


def build(a):
    mods = ['LocalWindowUnsat.' + info['module'] for _, info in cases(a)]
    if a.limit:
        mods = mods[:a.limit]
    cmd = [sys.executable, os.path.join(ROOT, 'work', 'guarded_lake_build.py'), '--jobs', str(a.jobs),
           '--heavy-jobs', str(a.heavy_jobs),
           '--min-free-gb', str(a.min_free_gb), '--rss-cap-gb', str(a.rss_cap_gb),
           *(['--trust-mtime'] if a.trust_mtime else []), *(['--direct'] if a.direct else []), *mods]
    raise SystemExit(subprocess.run(cmd).returncode)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--set', choices=['direction', 'direction5', 'r4', 'r4b'], default='direction',
                    help='the 145 windows of the 239 bound, the 175 of the 238 bound, or the radius-4 set')
    sub = ap.add_subparsers(dest='cmd', required=True)
    g = sub.add_parser('gen')
    g.add_argument('--work', required=True)
    g.add_argument('--seg', type=int, default=25000)
    g.add_argument('--cp', type=int, default=3)
    g.add_argument('--group', type=int, default=4)
    g.add_argument('--cadical', default=None, help='direction5: cadical binary (default: toolchain)')
    g.add_argument('--seeds', type=int, default=2, help='direction5: cadical seeds per core proof')
    g.add_argument('--split', action='store_true', help='emit proofs for LratFast2 (see above)')
    g.add_argument('--shard', default='0/1', help='i/n: only every n-th case from i (run n processes in parallel)')
    g.add_argument('--drop-lrat', action='store_true',
                   help='delete each LRAT (and core CNF) once its Lean modules are written (saves disk)')
    g.add_argument('--rounds', type=int, default=1,
                   help='cadical portfolio rounds of core shrinking per regenerated proof (3 roughly halves the hints)')
    b = sub.add_parser('build')
    b.add_argument('--jobs', type=int, default=3, help='light (data) modules at a time')
    b.add_argument('--heavy-jobs', type=int, default=3, help='kernel-check modules at a time')
    b.add_argument('--min-free-gb', type=float, default=5.0)
    b.add_argument('--rss-cap-gb', type=float, default=6.0)
    b.add_argument('--limit', type=int, default=0, help='only the N smallest cases')
    b.add_argument('--direct', action='store_true', help='compile with `lean` instead of `lake build`')
    b.add_argument('--trust-mtime', action='store_true',
                   help='resume quickly: skip modules whose .olean is up to date by mtime')
    a = ap.parse_args()
    {'gen': gen, 'build': build}[a.cmd](a)


if __name__ == '__main__':
    main()
