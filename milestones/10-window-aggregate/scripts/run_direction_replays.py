"""Generate and kernel-check the LRAT replays of the 145 direction-window cores.

Step 1 (`gen`): for each case of data/lean_core_direction (smallest proof first) run
gen_lean_lrat.py with 13-bit words, or 14-bit words when the database has more than
8191 slots.  Cases whose main module already exists are skipped, so the step resumes.
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


def cases():
    summary = json.load(open(os.path.join(DATA, '_summary.json')))['per_case']
    return sorted(summary.items(), key=lambda kv: kv[1]['hints'])


def gen(a):
    for name, info in cases():
        mod = info['module']
        if os.path.exists(os.path.join(UNSAT, mod + '.lean')):
            continue
        for bits in (13, 14):
            cmd = [sys.executable, os.path.join(HERE, 'gen_lean_lrat.py'), '--work', a.work,
                   '--data', DATA, '--seg', str(a.seg), '--cp', str(a.cp), '--group', str(a.group),
                   '--wbits', str(bits), name]
            r = subprocess.run(cmd, capture_output=True, text=True)
            if r.returncode == 0:
                print(json.dumps({'case': name, 'module': mod, 'wbits': bits, 'hints': info['hints']}), flush=True)
                break
            if 'nslots <= M' not in r.stderr and 'assert nslots' not in r.stderr:
                print(r.stderr[-2000:], file=sys.stderr)
                raise SystemExit(f'generation failed for {name}')
        else:
            raise SystemExit(f'{name}: too many slots even for 14-bit words')


def build(a):
    mods = ['LocalWindowUnsat.' + info['module'] for _, info in cases()]
    if a.limit:
        mods = mods[:a.limit]
    cmd = [sys.executable, os.path.join(ROOT, 'work', 'guarded_lake_build.py'), '--jobs', str(a.jobs),
           '--heavy-jobs', str(a.heavy_jobs),
           '--min-free-gb', str(a.min_free_gb), '--rss-cap-gb', str(a.rss_cap_gb), *mods]
    raise SystemExit(subprocess.run(cmd).returncode)


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    g = sub.add_parser('gen')
    g.add_argument('--work', required=True)
    g.add_argument('--seg', type=int, default=25000)
    g.add_argument('--cp', type=int, default=3)
    g.add_argument('--group', type=int, default=4)
    b = sub.add_parser('build')
    b.add_argument('--jobs', type=int, default=3, help='light (data) modules at a time')
    b.add_argument('--heavy-jobs', type=int, default=3, help='kernel-check modules at a time')
    b.add_argument('--min-free-gb', type=float, default=5.0)
    b.add_argument('--rss-cap-gb', type=float, default=6.0)
    b.add_argument('--limit', type=int, default=0, help='only the N smallest cases')
    a = ap.parse_args()
    {'gen': gen, 'build': build}[a.cmd](a)


if __name__ == '__main__':
    main()
