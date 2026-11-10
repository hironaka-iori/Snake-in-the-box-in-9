"""Production batches of the 233 certificates: generate, build, sweep, under a disk cap.

One batch takes the next certificates (seeds of the plan and share keys, smallest hint count
first) whose replay `.olean` does not exist yet, up to --batch-hints LRAT hints (estimated), and:

  1. writes their packed core modules `LocalWindowCnf/<M>.lean` (`cert233.py cnf NAMES`);
  2. writes their replays `LocalWindowUnsat/<M>.lean` (`cert233.py replay NAMES`, checker v3);
  3. builds them with `work/guarded_lake_build.py --direct --trust-mtime --no-ilean` (at most
     --jobs `lean` processes, nice 10, RSS cap --rss-cap-gb), after a staleness simulation
     (`closure()`/`uptodate()`): it stops if anything but the batch's own new modules would be
     rebuilt;
  4. sweeps: deletes the sources of every built module (`--trust-mtime` then treats the `.olean`
     as a prebuilt leaf), so only `.olean` files stay.

Before each batch it waits until `df -m /` shows at least --reserve-mb + the batch's estimated size
(about 2.6 B per hint + 100 kB per module, sources included); the migration agent's headroom is in
--reserve-mb (default 1,400 MB: 400 MB floor + 1 GB).  Resumable: everything it writes is checked
for existence first, except that the source of a module whose last guarded build failed after
the source was written is deleted and regenerated (`reset_failed`).  A batch with at most 20
unbuilt modules does not stop the run; a module that fails twice is left out of the rest of
the run.  Log: `data/prod6SB233.jsonl`.

  setsid nohup nice -n 10 python3 prod233.py [--batch-hints 4e7] [--jobs 2] [--until UNIX] &
"""
import argparse, importlib.util, json, os, re, shutil, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, HERE)
import cert233 as C   # noqa: E402

LEAN = C.LEAN
LIB = os.path.join(LEAN, '.lake', 'build', 'lib', 'lean')
GLB = os.path.join(ROOT, 'work', 'guarded_lake_build.py')
LOG = os.path.join(C.DATA, 'prod6SB233.jsonl')
LEANBIN = '/home/user/lean-deps/toolchain/lean-4.19.0-linux/bin'
CHAIN = os.path.join(ROOT, 'work', 'spectral', '.verification', 'chain')


def log(rec):
    rec['t'] = round(time.time())
    print(json.dumps(rec), flush=True)
    with open(LOG, 'a') as f:
        f.write(json.dumps(rec) + '\n')


def built(d, n):
    return os.path.exists(os.path.join(LIB, d, n + '.olean'))


def stale_check(targets, batch):
    spec = importlib.util.spec_from_file_location('glb', GLB)
    g = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(g)
    from pathlib import Path
    g.ROOT = Path(LEAN)
    deps = g.closure(targets, True)
    st = {}

    def s(m):
        if m not in st:
            st[m] = any(s(d) for d in deps[m]) or not g.uptodate(m, deps[m])
        return st[m]
    bad = [m for m in deps if s(m) and m.split('.')[-1] not in batch]
    return len(deps), sorted(m for m in deps if st[m]), bad


GLOG = os.path.join(LEAN, '.lake', 'guarded_build_233cert.jsonl')
GLOGS = os.path.join(LEAN, '.lake', 'guarded_logs')


def last_status():
    st = {}
    if os.path.exists(GLOG):
        for line in open(GLOG):
            try:
                r = json.loads(line)
            except ValueError:
                continue
            if 'module' in r:
                st[r['module']] = r['status']
    return st


def reset_failed(names):
    """Delete the source of every module of `names` whose last guarded build failed (or was
    killed) after the source was written, so `cert233.py cnf`/`replay` (which skip existing
    sources) regenerate it with the current generator.  A source written after its failure
    (already regenerated) is kept."""
    st, out = last_status(), []
    for nm in names:
        for d in ('LocalWindowCnf', 'LocalWindowUnsat'):
            m, src = d + '.' + nm, os.path.join(LEAN, d, nm + '.lean')
            lg = os.path.join(GLOGS, m + '.log')
            if st.get(m) in ('failed', 'killed') and not built(d, nm) and os.path.exists(src) and \
                    os.path.exists(lg) and os.path.getmtime(src) < os.path.getmtime(lg):
                os.remove(src)
                out.append(m)
    return out


def sweep(names):
    n = 0
    for nm in names:
        for d in ('LocalWindowCnf', 'LocalWindowUnsat'):
            src = os.path.join(LEAN, d, nm + '.lean')
            if os.path.exists(src) and built(d, nm):
                os.remove(src)
                n += 1
    return n


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--batch-hints', type=float, default=4e7)
    ap.add_argument('--max-items', type=int, default=400)
    ap.add_argument('--jobs', type=int, default=2)
    ap.add_argument('--rss-cap-gb', type=float, default=6.5)
    ap.add_argument('--min-free-gb', type=float, default=3.0)
    ap.add_argument('--reserve-mb', type=int, default=1400)
    ap.add_argument('--kinds', default='seed,share')
    ap.add_argument('--until', type=float, default=0, help='start no batch after this UNIX time')
    ap.add_argument('--once', action='store_true')
    a = ap.parse_args()
    ns = C.argparse.Namespace(keys_from='', plan=C.PLAN, core=C.CORE, names=[])
    fails = {}   # module name -> failed builds in this run; after 2 it is left for a later run
    while True:
        if a.until and time.time() > a.until:
            log({'stop': 'until'})
            return
        items = [(h, it) for h, it, m in C.work_items(ns, set(a.kinds.split(',')))
                 if not built('LocalWindowUnsat', it[2]) and fails.get(it[2], 0) < 2]
        if not items:
            log({'done': 'all certificates built'})
            return
        batch, tot = [], 0
        for h, it in items:
            if batch and (tot + h > a.batch_hints or len(batch) >= a.max_items):
                break
            batch.append(it[2])
            tot += h
        reset = reset_failed(batch)
        if reset:
            log({'regenerate': reset})
        need = a.reserve_mb + int(tot * 2.6e-6 * 1.0) + len(batch) // 10 + 50
        while C.disk_free_mb() < need:
            log({'wait_disk': C.disk_free_mb(), 'need': need})
            time.sleep(300)
        t0 = time.time()
        env = dict(os.environ, PATH=LEANBIN + ':' + os.environ['PATH'])
        for step in ('cnf', 'replay'):
            r = subprocess.run([sys.executable, os.path.join(HERE, 'cert233.py'), step, '--kinds', a.kinds, '--min-disk-mb',
                                str(a.reserve_mb - 200), *batch], env=env, capture_output=True, text=True)
            if r.returncode:
                log({'error': step, 'stderr': r.stderr[-2000:]})
                return
        t1 = time.time()
        targets = ['LocalWindowUnsat.' + n for n in batch]
        ncl, stale, bad = stale_check(targets, set(batch))
        if bad:
            log({'error': 'stale modules outside the batch', 'bad': bad[:20]})
            return
        r = subprocess.run(['nice', '-n', '10', sys.executable, GLB, '--root', LEAN, '--direct', '--trust-mtime', '--no-ilean',
                            '--jobs', str(a.jobs), '--heavy', r'^LocalWindow(Unsat|Cnf)\.(S|T)', '--heavy-jobs', str(a.jobs),
                            '--rss-cap-gb', str(a.rss_cap_gb), '--min-free-gb', str(a.min_free_gb),
                            '--min-disk-mb', str(a.reserve_mb - 600),
                            '--log', os.path.join(LEAN, '.lake', 'guarded_build_233cert.jsonl'), *targets],
                           env=dict(env, LEAN_PATH=CHAIN), capture_output=True, text=True, cwd=LEAN)
        t2 = time.time()
        nok = sum(built('LocalWindowUnsat', n) for n in batch)
        nsw = sweep(batch)
        log({'batch': len(batch), 'hints_est': int(tot), 'closure': ncl, 'stale': len(stale), 'built': nok,
             'swept_sources': nsw, 'gen_s': round(t1 - t0), 'build_s': round(t2 - t1), 'rc': r.returncode,
             'tail': r.stdout[-600:], 'disk_free_mb': C.disk_free_mb(), 'first': batch[0], 'last': batch[-1]})
        bad_now = [n for n in batch if not built('LocalWindowUnsat', n)]
        for n in bad_now:
            fails[n] = fails.get(n, 0) + 1
        if r.returncode and (a.once or not bad_now or len(bad_now) > 20):
            return   # a failure that is not confined to a few modules: stop for inspection
        if a.once:
            return


if __name__ == '__main__':
    main()
