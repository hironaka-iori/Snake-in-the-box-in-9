"""Generate and kernel-check the LRAT replays of the 145 direction-window cores.

Step 1 (`gen`): for each case of data/lean_core_direction (smallest proof first) run
gen_lean_lrat.py --fast (checker LratFast) with 13-bit words, or 14-bit words
(LratFast14) when the database has more than 8191 slots.  Cases whose main module already exists are skipped, so the step resumes.
Generation runs one case at a time (the largest LRAT files need a few GB in Python).

Step 2 (`build`): build every LocalWindowUnsat.D* module through
work/guarded_lake_build.py, which bounds concurrent Lean processes and memory.

  python run_direction_replays.py gen   --work ~/lean-deps/lrat-direction
  python run_direction_replays.py build --jobs 3
"""
import argparse, json, os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
DATA = os.path.join(HERE, '..', 'data', 'lean_core_direction')
UNSAT = os.path.join(ROOT, 'work', 'final_lean', 'LocalWindowUnsat')


def data_dir(a):
    return DATA + {'direction': '', 'direction5': '5', 'r4': '_r4'}[a.set]


def cases(a):
    summary = json.load(open(os.path.join(data_dir(a), '_summary.json')))['per_case']
    return sorted(summary.items(), key=lambda kv: kv[1]['hints'])


def gen(a):
    for name, info in cases(a):
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
            gen_lean_core.core_lrat(name, meta['core_ids'], a.work, cadical, list(range(1, a.seeds + 1)), certs)
        # literal offset above the variable count: 2400 / 3000 / 4000 (see gen_checker_variants.py)
        nv = meta.get('variables', 0)
        off = 2400 if nv < 2400 else 3000 if nv < 3000 else 4000
        assert nv < 4000, (name, nv)
        for bits in (13, 14, 15):
            cmd = [sys.executable, os.path.join(HERE, 'gen_lean_lrat.py'), '--work', a.work,
                   '--data', data_dir(a), '--seg', str(a.seg), '--cp', str(a.cp), '--group', str(a.group),
                   '--wbits', str(bits), '--off', str(off), '--noncomputable-data', '--fast', name]
            r = subprocess.run(cmd, capture_output=True, text=True)
            if r.returncode == 0:
                print(json.dumps({'case': name, 'module': mod, 'wbits': bits, 'off': off,
                                  'hints': info['hints']}), flush=True)
                break
            if 'nslots <= M' not in r.stderr and 'assert nslots' not in r.stderr:
                print(r.stderr[-2000:], file=sys.stderr)
                raise SystemExit(f'generation failed for {name}')
        else:
            raise SystemExit(f'{name}: too many slots even for 14-bit words')


def build(a):
    mods = ['LocalWindowUnsat.' + info['module'] for _, info in cases(a)]
    if a.limit:
        mods = mods[:a.limit]
    cmd = [sys.executable, os.path.join(ROOT, 'work', 'guarded_lake_build.py'), '--jobs', str(a.jobs),
           '--heavy-jobs', str(a.heavy_jobs),
           '--min-free-gb', str(a.min_free_gb), '--rss-cap-gb', str(a.rss_cap_gb),
           *(['--trust-mtime'] if a.trust_mtime else []), *mods]
    raise SystemExit(subprocess.run(cmd).returncode)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--set', choices=['direction', 'direction5', 'r4'], default='direction',
                    help='the 145 windows of the 239 bound, the 325 of the 238 bound, or the radius-4 set')
    sub = ap.add_subparsers(dest='cmd', required=True)
    g = sub.add_parser('gen')
    g.add_argument('--work', required=True)
    g.add_argument('--seg', type=int, default=25000)
    g.add_argument('--cp', type=int, default=3)
    g.add_argument('--group', type=int, default=4)
    g.add_argument('--cadical', default=None, help='direction5: cadical binary (default: toolchain)')
    g.add_argument('--seeds', type=int, default=2, help='direction5: cadical seeds per core proof')
    b = sub.add_parser('build')
    b.add_argument('--jobs', type=int, default=3, help='light (data) modules at a time')
    b.add_argument('--heavy-jobs', type=int, default=3, help='kernel-check modules at a time')
    b.add_argument('--min-free-gb', type=float, default=5.0)
    b.add_argument('--rss-cap-gb', type=float, default=6.0)
    b.add_argument('--limit', type=int, default=0, help='only the N smallest cases')
    b.add_argument('--trust-mtime', action='store_true',
                   help='resume quickly: skip modules whose .olean is up to date by mtime')
    a = ap.parse_args()
    {'gen': gen, 'build': build}[a.cmd](a)


if __name__ == '__main__':
    main()
