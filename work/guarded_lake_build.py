"""Memory-guarded build of Lean modules in work/final_lean (macOS and Linux).

`lake build` starts one Lean process per core, and kernel-checked certificate modules
need several GB each, so building many of them at once can exhaust memory.  This
driver computes the local import closure of the requested modules and builds it in
dependency order, one module per `lake build` call (its imports are already built,
so lake starts a single Lean process).  It

* runs at most --heavy-jobs memory-heavy builds (kernel checks) and --jobs light
  builds at a time;
* starts a build only when at least --min-free-gb of memory is available;
* kills a build whose process group exceeds --rss-cap-gb, and stops launching
  new builds (and kills the newest one) while available memory is below --floor-gb.

Every finished module is logged to --log as one JSON line (module, status, seconds,
peak RSS).  Rerunning skips nothing explicitly: lake itself makes up-to-date modules
a fast no-op (about two seconds per module).  With --trust-mtime a module whose .olean
is newer than its source and than the .olean files of its imports is marked done
without calling lake, which makes resuming a large build instant; lake re-checks its
own traces when the final target is built normally.

With --direct each module is compiled by `lean -o` itself (LEAN_PATH = the project's
build directory), without starting lake.  Starting lake costs several seconds per call in a
project with thousands of modules, which dominated the build time of small modules; lake
writes no trace files then, so keep using --direct (with --trust-mtime to resume) for a
project built this way, and audit it with `lean` (e.g. work/spectral/chain_audit.py).

  python3 work/guarded_lake_build.py UpperBound241Core LocalWindowRefuted --jobs 3
"""
import argparse, json, os, re, signal, subprocess, sys, threading, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent / 'final_lean'   # overridden by --root


def available_gb():
    if sys.platform == 'darwin':
        out = subprocess.run(['vm_stat'], capture_output=True, text=True).stdout
        page = int(re.search(r'page size of (\d+)', out).group(1))
        pages = 0
        for key in ('Pages free', 'Pages inactive', 'Pages speculative', 'Pages purgeable'):
            m = re.search(key + r':\s+(\d+)', out)
            pages += int(m.group(1)) if m else 0
        return pages * page / 2**30
    for line in open('/proc/meminfo'):
        if line.startswith('MemAvailable:'):
            return int(line.split()[1]) / 2**20
    return 0.0


def group_rss_gb():
    """Resident memory per process group, in GB."""
    out = subprocess.run(['ps', '-axo', 'pgid=,rss='], capture_output=True, text=True).stdout
    rss = {}
    for line in out.splitlines():
        parts = line.split()
        if len(parts) == 2:
            rss[int(parts[0])] = rss.get(int(parts[0]), 0) + int(parts[1])
    return {g: kb / 2**20 for g, kb in rss.items()}


def module_path(mod):
    return ROOT / (mod.replace('.', '/') + '.lean')


def olean_path(mod):
    return ROOT / '.lake' / 'build' / 'lib' / 'lean' / (mod.replace('.', '/') + '.olean')


def ilean_path(mod):
    return ROOT / '.lake' / 'build' / 'lib' / 'lean' / (mod.replace('.', '/') + '.ilean')


def uptodate(mod, deps):
    """The .olean of `mod` is newer than its source and than its imports' .olean files."""
    o = olean_path(mod)
    if not o.exists():
        return False
    if mod in PREBUILT:
        return True
    t = o.stat().st_mtime
    if t < module_path(mod).stat().st_mtime:
        return False
    return all(olean_path(d).exists() and olean_path(d).stat().st_mtime <= t for d in deps)


PREBUILT = set()   # modules whose source is gone but whose .olean exists (--trust-mtime)


def closure(targets, trust_mtime=False):
    deps, stack = {}, list(targets)
    while stack:
        m = stack.pop()
        if m in deps:
            continue
        p = module_path(m)
        if not p.exists():
            if trust_mtime and olean_path(m).exists():
                # generated data whose source was deleted to save disk: its .olean is all
                # that importing modules need
                PREBUILT.add(m)
                deps[m] = []
                continue
            raise SystemExit(f'no source for module {m}: {p}')
        imps = re.findall(r'^import\s+(\S+)', p.read_text(), re.M)
        deps[m] = [d for d in imps if module_path(d).exists()
                   or (trust_mtime and olean_path(d).exists() and d.startswith('LocalWindow'))]
        stack += deps[m]
    return deps


def main():
    global ROOT
    ap = argparse.ArgumentParser()
    ap.add_argument('targets', nargs='+')
    ap.add_argument('--jobs', type=int, default=3, help='concurrent light builds')
    ap.add_argument('--heavy', default=r'\.Check\d+$',
                    help='regex of memory-heavy modules (kernel checks), limited by --heavy-jobs')
    ap.add_argument('--heavy-jobs', type=int, default=None, help='default: --jobs')
    ap.add_argument('--min-free-gb', type=float, default=5.0)
    ap.add_argument('--rss-cap-gb', type=float, default=6.0)
    ap.add_argument('--floor-gb', type=float, default=1.5)
    ap.add_argument('--root', default=str(ROOT), help='Lean project directory')
    ap.add_argument('--log', default=None, help='default: ROOT/.lake/guarded_build.jsonl')
    ap.add_argument('--lake', default=os.environ.get('LAKE', 'lake'))
    ap.add_argument('--direct', action='store_true',
                    help='compile each module with `lean -o` instead of `lake build` (see above)')
    ap.add_argument('--lean', default=os.environ.get('LEAN', 'lean'))
    ap.add_argument('--trust-mtime', action='store_true',
                    help='skip modules whose .olean is newer than their source and imports')
    a = ap.parse_args()
    ROOT = Path(a.root).resolve()
    if a.log is None:
        (ROOT / '.lake').mkdir(exist_ok=True)
        a.log = str(ROOT / '.lake' / 'guarded_build.jsonl')

    if a.heavy_jobs is None:
        a.heavy_jobs = a.jobs
    heavy = re.compile(a.heavy)
    deps = closure(a.targets, a.trust_mtime)
    done, failed, running = set(), {}, {}   # running: module -> (Popen, start, peak)
    lock = threading.Lock()
    log = open(a.log, 'a')
    logdir = Path(a.log).parent / 'guarded_logs'
    logdir.mkdir(parents=True, exist_ok=True)
    t_begin = time.time()
    print(f'{len(deps)} modules in the closure; jobs={a.jobs}, cap={a.rss_cap_gb} GB', flush=True)

    def finish(mod, status, note=''):
        proc, start, peak = running.pop(mod)
        rec = {'module': mod, 'status': status, 'seconds': round(time.time() - start, 1),
               'peak_rss_gb': round(peak, 2), 'note': note}
        log.write(json.dumps(rec) + '\n'); log.flush()
        if status == 'ok':
            done.add(mod)
        else:
            failed[mod] = rec
        if status != 'ok' or rec['seconds'] > 30:
            print(json.dumps(rec), flush=True)

    while len(done) + len(failed) < len(deps):
        # monitor
        rss = group_rss_gb()
        avail = available_gb()
        for mod in list(running):
            proc, start, peak = running[mod]
            cur = rss.get(proc.pid, 0.0)
            running[mod] = (proc, start, max(peak, cur))
            if cur > a.rss_cap_gb:
                os.killpg(proc.pid, signal.SIGKILL); proc.wait()
                finish(mod, 'killed', f'RSS {cur:.1f} GB over cap')
            elif proc.poll() is not None:
                out = (logdir / (mod + '.log')).read_text(errors='replace')
                ok = proc.returncode == 0 and "declaration uses 'sorry'" not in out
                finish(mod, 'ok' if ok else 'failed', '' if ok else out[-3000:])
        if avail < a.floor_gb and len(running) > 1:
            newest = max(running, key=lambda m: running[m][1])
            proc = running[newest][0]
            os.killpg(proc.pid, signal.SIGKILL); proc.wait()
            running.pop(newest)   # requeued: not marked done or failed
            print(f'low memory ({avail:.1f} GB): requeued {newest}', flush=True)
        # blocked modules (a dependency failed) count as failed
        for m in deps:
            if m not in done and m not in failed and m not in running and any(d in failed for d in deps[m]):
                failed[m] = {'module': m, 'status': 'blocked'}
        # launch
        ready = [m for m in sorted(deps) if m not in done and m not in failed and m not in running
                 and all(d in done for d in deps[m])]
        if a.trust_mtime:
            skipped = [m for m in ready if uptodate(m, deps[m])]
            if skipped:
                done.update(skipped)
                for m in skipped:
                    log.write(json.dumps({'module': m, 'status': 'uptodate', 'seconds': 0,
                                          'peak_rss_gb': 0, 'note': ''}) + '\n')
                log.flush()
                continue
        n_heavy = sum(1 for m in running if heavy.search(m))
        n_light = len(running) - n_heavy
        ready = [m for m in ready if (n_heavy < a.heavy_jobs if heavy.search(m) else n_light < a.jobs)]
        if ready and available_gb() >= a.min_free_gb:
            # prefer heavy modules so the slow kernel checks start as early as possible
            m = next((x for x in ready if heavy.search(x)), ready[0])
            if a.direct:
                olean_path(m).parent.mkdir(parents=True, exist_ok=True)
                cmd = [a.lean, f'--root={ROOT}', '-o', str(olean_path(m)), '-i', str(ilean_path(m)),
                       str(module_path(m))]
                lp = [str(ROOT / '.lake' / 'build' / 'lib' / 'lean')] + (
                    [os.environ['LEAN_PATH']] if os.environ.get('LEAN_PATH') else [])
                env = dict(os.environ, LEAN_PATH=os.pathsep.join(lp))
            else:
                cmd, env = [a.lake, 'build', m], None
            with open(logdir / (m + '.log'), 'w') as out:
                proc = subprocess.Popen(cmd, cwd=ROOT, stdout=out, env=env,
                                        stderr=subprocess.STDOUT, start_new_session=True)
            running[m] = (proc, time.time(), 0.0)
            continue
        time.sleep(0.25 if a.direct else 2)

    print(f'done {len(done)}/{len(deps)} in {time.time() - t_begin:.0f}s; failed {len(failed)}', flush=True)
    for m, rec in failed.items():
        print('FAILED', m, rec.get('status'), rec.get('note', '')[:500], flush=True)
    sys.exit(1 if failed else 0)


if __name__ == '__main__':
    main()
