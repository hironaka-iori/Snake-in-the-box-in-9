"""Production build of the data module and the 792 shards of a seven-centre chain, on a small disk.

The shards (`gen_lean_automaton7.py`) are core Lean modules that import only
`WindowAutomaton7<T>Data`, which imports `WindowAutomaton7Defs` (work/spectral/stronger, compiled
into work/spectral/.verification/chain like every chain module).  They are built in
work/final_lean by `work/guarded_lake_build.py --direct --trust-mtime`, with
LEAN_PATH = work/spectral/.verification/chain, so their closure inside work/final_lean is the data
module and the shards only.

Sources are generated, and on a small disk they are deleted once built:

  prepare   runs gen_lean_automaton7.py into a temporary directory under work/final_lean/.lake,
            checks every data and shard source against the manifest (--manifest; written by
            --write-manifest the first time), and moves into work/final_lean the sources of the
            modules whose .olean does not exist yet (--limit N: only the first N missing shards,
            in the order of guarded_lake_build.py; --restore: every module).  Every placed source
            gets the fixed mtime SOURCE_EPOCH, older than any .olean of this build, so that a
            source regenerated later (byte-identical by the manifest) never makes a built module
            stale under --trust-mtime.
  stale     simulates guarded_lake_build.py (`closure`, `uptodate`, imported with importlib) on the
            data module and the shards and prints the modules it would build; fails if any of them
            is not a module of the tag.
  sweep     runs until the build process (--pid-file) exits: every --every seconds it deletes the
            source of each module the guarded log reports `ok` whose .olean exists and whose source
            matches the manifest (regenerable byte for byte by `prepare`); pauses the build
            (SIGSTOP to the build process and its descendants, found by PID through /proc) while
            the free disk is below --floor-mb and resumes it (SIGCONT) at --floor-mb + 10; writes a
            status JSON (--status).
  status    shards built, .olean bytes, CPU rate and projection from the guarded log.

  python3 shard_build7.py prepare --keys K --tag T --lam P/Q --manifest M [--write-manifest] [--limit N]
                                  [--min-disk-mb D]      (exit 2: nothing left; exit 3: disk)
  python3 shard_build7.py stale --tag T
  python3 shard_build7.py sweep --tag T --manifest M --log L --pid-file F [--floor-mb 250]
  python3 shard_build7.py status --tag T --log L
"""
import argparse, hashlib, importlib.util, json, os, re, shutil, signal, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))
LEAN = os.path.join(ROOT, 'work', 'final_lean')
LIB = os.path.join(LEAN, '.lake', 'build', 'lib', 'lean')
GEN = os.path.join(HERE, 'gen_lean_automaton7.py')
SOURCE_EPOCH = 1793232000          # 2026-10-29 00:00 UTC, before every .olean of this build
N_SHARDS = 792


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


def modules(T):
    """The data module and the shards, by module name."""
    out = [f'WindowAutomaton7{T}Data']
    import gen_lean_automaton7 as G
    shp = [c for c in G.rgs(8) if G.induced(c)]
    assert len(shp) == 132
    out += [f'WindowAutomaton7{T}Shard{i}_{t0}' for i in range(132) for t0 in range(1, 7)]
    return out


def read_manifest(p):
    m = {}
    for line in open(p):
        h, name = line.split()
        m[name] = h
    return m


def guarded():
    spec = importlib.util.spec_from_file_location('glb', os.path.join(ROOT, 'work', 'guarded_lake_build.py'))
    g = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(g)
    return g


def prepare(a):
    T = a.tag
    mods = modules(T)
    missing = [m for m in mods if a.restore or not os.path.exists(os.path.join(LIB, m + '.olean'))]
    data = f'WindowAutomaton7{T}Data'
    shards = sorted(m for m in missing if m != data)      # guarded_lake_build.py launches in this order
    if a.limit:
        shards = shards[:a.limit]
    want = ([data] if data in missing else []) + shards
    if not want:
        print('placed 0 sources (every module has its .olean)')
        sys.exit(2)
    free = shutil.disk_usage(LEAN).free / 2**20
    if free < a.min_disk_mb:
        print(f'placed 0 sources: {free:.0f} MB free, below --min-disk-mb {a.min_disk_mb}')
        sys.exit(3)
    tmp = os.path.join(LEAN, '.lake', f'gen7{T}')
    shutil.rmtree(tmp, ignore_errors=True)
    os.makedirs(tmp)
    cmd = [sys.executable, GEN, '--keys', *a.keys, '--tag', T, '--lam', a.lam, '--noncomputable',
           '--out-stronger', tmp, '--out-core', tmp, '--summary', os.path.join(tmp, 'summary.json')]
    if a.shard_v2:
        cmd += ['--shard-v2', a.shard_v2]
    if not a.write_manifest:
        sel = [m[len(f'WindowAutomaton7{T}Shard'):] for m in shards]
        cmd += ['--shards', ','.join(sel) if sel else 'none']
        if data not in want:
            cmd += ['--write', 'shards']   # the data module (22 MB of source) is not needed
    subprocess.run(cmd, check=True)
    if a.write_manifest:
        with open(a.manifest, 'w') as f:
            for m in mods:
                f.write(f'{sha(os.path.join(tmp, m + ".lean"))}  {m}.lean\n')
        print(f'wrote {a.manifest} ({len(mods)} sources)')
    man = read_manifest(a.manifest)
    placed = 0
    for m in want:
        p = os.path.join(tmp, m + '.lean')
        if sha(p) != man[m + '.lean']:
            raise SystemExit(f'{m}: source differs from the manifest')
        dst = os.path.join(LEAN, m + '.lean')
        if os.path.exists(dst) and sha(dst) != man[m + '.lean']:
            raise SystemExit(f'{dst} exists and differs from the manifest')
        os.replace(p, dst)
        os.utime(dst, (SOURCE_EPOCH, SOURCE_EPOCH))
        placed += 1
    shutil.rmtree(tmp)
    print(f'placed {placed} sources ({len(missing)} modules without .olean)')


def stale(a):
    T = a.tag
    g = guarded()
    targets = [m for m in modules(T) if os.path.exists(os.path.join(LEAN, m + '.lean'))
               or os.path.exists(os.path.join(LIB, m + '.olean'))]
    deps = g.closure(targets, trust_mtime=True)
    # the order of the build: a module is stale if it is not up to date or one of its deps is stale
    st = {}

    def is_stale(m):
        if m not in st:
            st[m] = any(is_stale(d) for d in deps[m]) or not g.uptodate(m, deps[m])
        return st[m]
    bad = sorted(m for m in deps if is_stale(m))
    other = [m for m in bad if not m.startswith(f'WindowAutomaton7{T}')]
    print(f'{len(deps)} modules in the closure inside {LEAN}; {len(bad)} stale; '
          f'{len(g.PREBUILT)} prebuilt (source deleted)')
    print('stale (first 10):', bad[:10])
    print('closure outside the tag:', sorted(m for m in deps if not m.startswith(f'WindowAutomaton7{T}')))
    if other:
        raise SystemExit(f'stale modules outside the tag: {other}')


def descendants(pid):
    kids = {}
    for d in os.listdir('/proc'):
        if d.isdigit():
            try:
                pp = int(open(f'/proc/{d}/stat').read().rsplit(')', 1)[1].split()[1])
            except Exception:
                continue
            kids.setdefault(pp, []).append(int(d))
    out, stack = [], [pid]
    while stack:
        p = stack.pop()
        out.append(p)
        stack += kids.get(p, [])
    return out


def alive(pid):
    try:
        os.kill(pid, 0)
        return True
    except OSError:
        return False


def log_status(path):
    st = {}
    if os.path.exists(path):
        for line in open(path):
            r = json.loads(line)
            st[r['module']] = r
    return st


def sweep(a):
    T = a.tag
    man = read_manifest(a.manifest)
    pid = int(open(a.pid_file).read().split()[0])
    paused = False
    while alive(pid):
        st = log_status(a.log)
        deleted = 0
        for m, r in st.items():
            src = os.path.join(LEAN, m + '.lean')
            if (r['status'] in ('ok', 'uptodate') and m.startswith(f'WindowAutomaton7{T}')
                    and os.path.exists(src) and os.path.exists(os.path.join(LIB, m + '.olean'))
                    and man.get(m + '.lean') == sha(src)):
                os.remove(src)
                deleted += 1
        free = shutil.disk_usage(LEAN).free / 2**20
        if free < a.floor_mb and not paused:
            for p in descendants(pid):
                os.kill(p, signal.SIGSTOP)
            paused = True
        elif free >= a.floor_mb + 10 and paused:
            for p in descendants(pid):
                os.kill(p, signal.SIGCONT)
            paused = False
        s = status_dict(T, st)
        s.update(time=time.strftime('%Y-%m-%d %H:%M:%S'), free_mb=round(free), paused=paused,
                 sources_deleted_now=deleted)
        json.dump(s, open(a.status, 'w'), indent=1)
        time.sleep(a.every)
    print('build process exited')


def status_dict(T, st):
    done = [r for m, r in st.items() if r['status'] == 'ok' and 'Shard' in m]
    bad = [m for m, r in st.items() if r['status'] not in ('ok', 'uptodate')]
    ob = sum(os.path.getsize(os.path.join(LIB, m + ext)) for m in st if st[m]['status'] == 'ok'
             for ext in ('.olean', '.ilean') if os.path.exists(os.path.join(LIB, m + ext)))
    cpu = sum(r['seconds'] for r in done)
    built = sum(os.path.exists(os.path.join(LIB, f'WindowAutomaton7{T}Shard{i}.olean'))
                for i in (f'{s}_{t}' for s in range(132) for t in range(1, 7)))
    return dict(shards_built=built, shards_total=N_SHARDS, shards_ok_in_log=len(done),
                not_ok=bad, olean_ilean_bytes_built=ob,
                shard_seconds=round(cpu), mean_shard_seconds=round(cpu / len(done), 1) if done else None,
                peak_rss_gb=max((r['peak_rss_gb'] for r in done), default=None))


def status(a):
    print(json.dumps(status_dict(a.tag, log_status(a.log)), indent=1))


def main():
    sys.path.insert(0, HERE)
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest='cmd', required=True)
    p = sub.add_parser('prepare')
    p.add_argument('--keys', nargs='+', required=True)
    p.add_argument('--tag', required=True)
    p.add_argument('--lam', required=True)
    p.add_argument('--manifest', required=True)
    p.add_argument('--write-manifest', action='store_true')
    p.add_argument('--limit', type=int, default=0)
    p.add_argument('--restore', action='store_true',
                   help='place the sources of all modules, built or not (e.g. before chain_audit.py, '
                        'which needs the source of every core module it imports); with the fixed mtime '
                        'they stay older than their .olean')
    p.add_argument('--shard-v2', default=None, choices=['t2', 't1', 'label'],
                   help='generate the shard v2 modules (gen_lean_automaton7.py --shard-v2 GRAIN); use the '
                        'v2 manifest (data/shards7_<T>_v2.sha256) and build WindowAutomaton7V2 into '
                        'work/spectral/.verification/chain first')
    p.add_argument('--min-disk-mb', type=float, default=0,
                   help='place nothing (exit 3) below this much free disk; generating needs about '
                        '30 kB per shard (and 23 MB for the data module, while it is not built)')
    s = sub.add_parser('stale')
    s.add_argument('--tag', required=True)
    w = sub.add_parser('sweep')
    w.add_argument('--tag', required=True)
    w.add_argument('--manifest', required=True)
    w.add_argument('--log', required=True)
    w.add_argument('--pid-file', required=True)
    w.add_argument('--status', required=True)
    w.add_argument('--floor-mb', type=float, default=250)
    w.add_argument('--every', type=float, default=60)
    t = sub.add_parser('status')
    t.add_argument('--tag', required=True)
    t.add_argument('--log', required=True)
    a = ap.parse_args()
    {'prepare': prepare, 'stale': stale, 'sweep': sweep, 'status': status}[a.cmd](a)


if __name__ == '__main__':
    main()
