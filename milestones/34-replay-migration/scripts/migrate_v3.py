"""Drop-in migration of the Q (237), R (236) and K (235) window replays to the checker v3.

Each old replay `LocalWindowUnsat.<W>` (Q/R: split layout with `LratFast2`/`LratFast2F`, Data<k> and
Check<g> modules; K: packed split layout, `NatPack` checkpoints) is replaced by ONE module of the
same name for the checker v3 (`work/final_lean/LratV3.lean`), written by
`milestones/26-replay-efficiency/scripts/gen_lean_lrat_v3.py` from an LRAT proof that is
regenerated from the committed core by `gen_lean_core.core_lrat` with the original settings
(CaDiCaL portfolio, seeds 1-2; one core round for Q and K, two for R).  The theorem stays
`Snake9.LocalWindow.<W>.unsat : Unsat cnf`, `cnf` from `LocalWindowCnf.<W>`; `verify` checks that its
statement (printed with `pp.all`) is the same string as the old one.

Steps for one window (each resumable; state in STAGE and in the manifest):

  gen     LRAT from the core into STAGE/work/<W>/, v3 source STAGE/src/LocalWindowUnsat/<W>.lean;
          the LRAT and CNF files are deleted as soon as the source is written
  build   `nice -n 10 lean -o STAGE/lib/LocalWindowUnsat/<W>.olean` with LEAN_PATH = STAGE/lib
          first, then the production lib (STAGE/lib holds LratV3, ProofPack and the staged
          replays, and no LocalWindowCnf/ directory); the source is deleted afterwards
  verify  `pp.all` statement of `unsat` from the staged module equals the old one, and
          `#print axioms` gives exactly propext, Classical.choice, Quot.sound
  swap    the staged .olean is copied next to LocalWindowUnsat/<W>.olean and renamed over it, its
          mtime set to that of the old .olean (older than the aggregates, so --trust-mtime does
          not cascade); the old build directory LocalWindowUnsat/<W>/ (Data/Check .olean/.ilean),
          the old .ilean and the old sources (main and Check<g>) are deleted.  No source is left
          for <W>: guarded_lake_build.py --trust-mtime then treats it as prebuilt.

  python3 migrate_v3.py run [--jobs 2] [--min-disk-mb 250] [--stop-at UNIX_TIME] W ... | @FILE
  python3 migrate_v3.py status

Every event is one JSON line in milestones/34-replay-migration/data/manifest.jsonl.
"""
import argparse, hashlib, json, os, re, shutil, subprocess, sys, threading, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
S10 = os.path.join(ROOT, 'milestones', '10-window-aggregate', 'scripts')
S26 = os.path.join(ROOT, 'milestones', '26-replay-efficiency', 'scripts')
S23 = os.path.join(ROOT, 'milestones', '23-k6-lean', 'certify')
DATA = os.path.join(ROOT, 'milestones', '10-window-aggregate', 'data')
FINAL = os.path.join(ROOT, 'work', 'final_lean')
LIB = os.path.join(FINAL, '.lake', 'build', 'lib', 'lean')
MANIFEST = os.path.join(HERE, '..', 'data', 'manifest.jsonl')
LEAN = os.path.expanduser('~/.elan/toolchains/leanprover--lean4---v4.19.0/bin/lean')
CADICAL = os.path.join(os.path.dirname(LEAN), 'cadical')
STAGE = os.environ.get('V3STAGE', '/home/user/v3stage')
OFF = 4000
AXIOMS = ['Classical.choice', 'Quot.sound', 'propext']
for p in (S10, S26, S23):
    sys.path.insert(0, p)
import gen_lean_core as GC        # noqa: E402
import gen_lean_lrat_v3 as V3     # noqa: E402

SETS = {'Q': dict(set='r4b', data=os.path.join(DATA, 'lean_core_direction_r4b'), rounds=1),
        'R': dict(set='r4', data=os.path.join(DATA, 'lean_core_direction_r4'), rounds=2),
        'K': dict(set='k6', data=os.path.join(DATA, 'lean_core_direction_k6'), rounds=1)}
LOCK = threading.Lock()


def cases():
    out = {}
    for pre, S in SETS.items():
        for name, info in json.load(open(os.path.join(S['data'], '_summary.json')))['per_case'].items():
            if info['module'].startswith(pre):
                out[info['module']] = (name, pre, S)
    return out


def disk_free_mb():
    st = os.statvfs(ROOT)
    return st.f_bavail * st.f_frsize / 2**20


def avail_gb():
    for line in open('/proc/meminfo'):
        if line.startswith('MemAvailable:'):
            return int(line.split()[1]) / 2**20
    return 0.0


def log(rec):
    rec = dict(rec, t=round(time.time()))
    with LOCK:
        print(json.dumps(rec), flush=True)
        with open(MANIFEST, 'a') as f:
            f.write(json.dumps(rec) + '\n')


def manifest():
    st = {}
    if os.path.exists(MANIFEST):
        for line in open(MANIFEST):
            r = json.loads(line)
            if 'window' in r:
                st.setdefault(r['window'], {})[r['step']] = r
    return st


def old_files(w):
    """Every production file of the old replay of w (build products and sources)."""
    fs = []
    for e in ('.olean', '.ilean'):
        p = os.path.join(LIB, 'LocalWindowUnsat', w + e)
        if os.path.exists(p):
            fs.append(p)
    p = os.path.join(FINAL, 'LocalWindowUnsat', w + '.lean')
    if os.path.exists(p):
        fs.append(p)
    for d in (os.path.join(LIB, 'LocalWindowUnsat', w), os.path.join(FINAL, 'LocalWindowUnsat', w)):
        for dp, _, f in os.walk(d):
            fs += [os.path.join(dp, x) for x in f]
    return fs


def run_lean(args, env, cap_gb, cwd=None):
    p = subprocess.Popen(['nice', '-n', '10', LEAN, *args], env=env, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, cwd=cwd)
    killed, peak = [], [0]

    def guard():
        while True:
            try:
                rss = int([l for l in open('/proc/%d/status' % p.pid) if l.startswith('VmRSS')][0].split()[1])
            except Exception:
                return
            peak[0] = max(peak[0], rss)
            if rss > cap_gb * 2**20:
                os.kill(p.pid, 9)
                killed.append(rss)
                return
            time.sleep(0.5)
    threading.Thread(target=guard, daemon=True).start()
    t = time.time()
    out = p.stdout.read()
    _, st, ru = os.wait4(p.pid, 0)
    return dict(status=st, out=out.decode(errors='replace'), cpu=round(ru.ru_utime + ru.ru_stime, 2),
                wall=round(time.time() - t, 2), rss_gb=round(ru.ru_maxrss / 2**20, 3), killed=bool(killed))


def stage_paths(w):
    return dict(work=os.path.join(STAGE, 'work', w),
                src=os.path.join(STAGE, 'src', 'LocalWindowUnsat', w + '.lean'),
                olean=os.path.join(STAGE, 'lib', 'LocalWindowUnsat', w + '.olean'))


def gen(w, cs):
    name, pre, S = cs[w]
    P = stage_paths(w)
    if os.path.exists(P['src']):
        return
    os.makedirs(P['work'], exist_ok=True)
    meta = json.load(open(os.path.join(S['data'], name + '.json')))
    certs = GC.CADICAL_SETS[S['set']]['certs'] if pre != 'K' else k_certs(meta, name, P['work'])
    t0 = time.time()
    wrap = os.path.join(P['work'], 'cadical_nice.sh')   # the solver at nice 10, as the lean processes
    with open(wrap, 'w') as g:
        g.write('#!/bin/bash\nexec nice -n 10 %s "$@"\n' % CADICAL)
    os.chmod(wrap, 0o755)
    _, info = GC.core_lrat(name, meta['core_ids'], P['work'], wrap, [1, 2], certs, rounds=S['rounds'])
    t1 = time.time()
    os.makedirs(os.path.dirname(P['src']), exist_ok=True)
    tmp = os.path.join(P['work'], 'out')
    stats = V3.export(name, P['work'], S['data'], tmp, 60000, OFF, False)
    os.replace(os.path.join(tmp, 'LocalWindowUnsat', w + '.lean'), P['src'])
    shutil.rmtree(P['work'], ignore_errors=True)
    log(dict(window=w, step='gen', case=name, lemmas=info['lemmas'], hints=info['hints'],
             lrat_sha256=info['lrat_sha256'], segments=stats['segments'], wbits=stats['wbits'],
             src_bytes=os.path.getsize(P['src']),
             src_sha256=hashlib.sha256(open(P['src'], 'rb').read()).hexdigest(),
             lrat_s=round(t1 - t0, 1), gen_s=round(time.time() - t1, 1)))


def k_certs(meta, name, work):
    import gen_k6_core as K   # noqa: E402  (milestones/23-k6-lean/certify)
    certs = os.path.join(work, 'certs')
    os.makedirs(certs, exist_ok=True)
    K.register(certs)
    K.regen_cnf(meta, os.path.join(certs, name + '.cnf.gz'))
    return certs


def build(w, cap_gb):
    P = stage_paths(w)
    os.makedirs(os.path.dirname(P['olean']), exist_ok=True)
    env = dict(os.environ, LEAN_PATH=os.path.join(STAGE, 'lib') + ':' + LIB)
    r = run_lean(['--root=' + os.path.join(STAGE, 'src'), '-o', P['olean'], P['src']], env, cap_gb)
    ok = r['status'] == 0 and not r['killed'] and 'sorry' not in r['out'] and os.path.exists(P['olean'])
    rec = dict(window=w, step='build', ok=ok, cpu=r['cpu'], wall=r['wall'], rss_gb=r['rss_gb'],
               killed=r['killed'])
    if ok:
        rec['new_bytes'] = os.path.getsize(P['olean'])
        os.remove(P['src'])
    else:
        rec['error'] = r['out'][-1500:]
    log(rec)
    return ok


def stmt_file(ws, path):
    with open(path, 'w') as g:
        g.write(''.join('import LocalWindowUnsat.%s\n' % w for w in ws))
        g.write('set_option pp.all true\n')
        for w in ws:
            g.write('#check @Snake9.LocalWindow.%s.unsat\n#print axioms Snake9.LocalWindow.%s.unsat\n' % (w, w))


def parse_stmts(ws, out):
    res = {}
    for w in ws:
        m = re.search(r'^@?Snake9\.LocalWindow\.%s\.unsat : (.*?)$' % re.escape(w), out, re.M)
        a = re.search(r"'Snake9\.LocalWindow\.%s\.unsat' depends on axioms: \[(.*?)\]" % re.escape(w), out, re.S)
        res[w] = (m.group(1).strip() if m else None,
                  sorted(x.strip() for x in a.group(1).split(',')) if a else None)
    return res


def verify(ws):
    d = os.path.join(STAGE, 'verify')
    os.makedirs(d, exist_ok=True)
    f = os.path.join(d, 'V.lean')
    stmt_file(ws, f)
    old = run_lean([f], dict(os.environ, LEAN_PATH=LIB), 6.5)
    new = run_lean([f], dict(os.environ, LEAN_PATH=os.path.join(STAGE, 'lib') + ':' + LIB), 6.5)
    po, pn = parse_stmts(ws, old['out']), parse_stmts(ws, new['out'])
    good = []
    for w in ws:
        ok = po[w][0] is not None and po[w][0] == pn[w][0] and pn[w][1] == AXIOMS
        log(dict(window=w, step='verify', ok=ok, stmt=pn[w][0], old_stmt_same=po[w][0] == pn[w][0],
                 axioms=pn[w][1]))
        if ok:
            good.append(w)
    return good


def swap(w, old_mtime_floor):
    P = stage_paths(w)
    dst = os.path.join(LIB, 'LocalWindowUnsat', w + '.olean')
    fs = old_files(w)
    old_bytes = sum(os.path.getsize(x) for x in fs)
    old_mt = os.stat(dst).st_mtime
    # four Q mains were rebuilt after LocalWindowDirUnsatR4b (Oct 23): never newer than an importer
    mt = min(old_mt, old_mtime_floor - 1)
    shutil.copyfile(P['olean'], dst + '.new')
    os.utime(dst + '.new', (mt, mt))
    os.replace(dst + '.new', dst)
    for x in fs:
        if x != dst and os.path.exists(x):
            os.remove(x)
    for d in (os.path.join(LIB, 'LocalWindowUnsat', w), os.path.join(FINAL, 'LocalWindowUnsat', w)):
        shutil.rmtree(d, ignore_errors=True)
    new_bytes = os.path.getsize(dst)
    os.remove(P['olean'])
    log(dict(window=w, step='swap', ok=True, old_bytes=old_bytes, old_files=len(fs), new_bytes=new_bytes,
             freed=old_bytes - new_bytes, mtime=mt, old_mtime=old_mt))


IMPORTERS = {'Q': ('LocalWindowDirUnsatR4b', 'LocalWindowDirUnsatR4'), 'R': ('LocalWindowDirUnsatR4',),
             'K': ('LocalWindowDirUnsatK6',)}


def agg_floor(w):
    """The oldest .olean among the built aggregates that import w (Reuse7* are not built)."""
    return min(os.stat(os.path.join(LIB, m + '.olean')).st_mtime for m in IMPORTERS[w[0]])


def ensure_libs(production):
    """LratV3 and ProofPack for the staged builds (STAGE/lib) and, once, for the production lib:
    new files only, compiled against the production LocalWindowModel.olean."""
    for mod in ('ProofPack', 'LratV3'):
        for lib in [os.path.join(STAGE, 'lib')] + ([LIB] if production else []):
            o = os.path.join(lib, mod + '.olean')
            if os.path.exists(o):
                continue
            os.makedirs(lib, exist_ok=True)
            r = run_lean(['--root=' + FINAL, '-o', o, os.path.join(FINAL, mod + '.lean')],
                         dict(os.environ, LEAN_PATH=LIB), 6.5)
            log(dict(step='lib', module=mod, lib=lib, ok=r['status'] == 0, cpu=r['cpu'], out=r['out'][-500:]))
            assert r['status'] == 0, r['out']


def run(a):
    cs = cases()
    ensure_libs(not a.no_swap)
    st = manifest()
    todo = [w for w in a.windows if 'swap' not in st.get(w, {})]
    hints = {}
    for w in todo:
        name, pre, S = cs[w]
        hints[w] = json.load(open(os.path.join(S['data'], '_summary.json')))['per_case'][name]['hints']
    q_build, built, lock = [], [], threading.Lock()
    state = dict(gen_done=False, err=None)

    def stop():
        return a.stop_at and time.time() > a.stop_at

    def est(w):
        return max(0.2e-3 * hints[w], 1.1 * a.est.get(w, 0))

    def need_mb(w):
        return 1 + 40 * hints[w] / 2**20 * (2 if w[0] == 'R' else 1)

    def gen_worker():
        """Takes the first window of the order whose staging peak fits the free disk now (smaller
        windows go ahead of one that has to wait for disk freed by the swaps)."""
        try:
            pending = list(todo)
            while pending:
                if stop() or state['err']:
                    break
                pending = [w for w in pending if not (a.stop_at and est(w) > a.stop_at - time.time()
                                                      and not os.path.exists(stage_paths(w)['olean']))]
                free = disk_free_mb()
                w = next((w for w in pending if os.path.exists(stage_paths(w)['olean'])
                          or os.path.exists(stage_paths(w)['src']) or free - need_mb(w) >= a.min_disk_mb), None)
                if w is None:
                    time.sleep(20)
                    continue
                # do not run too far ahead of the builders
                while len(q_build) >= a.ahead and not stop():
                    time.sleep(5)
                pending.remove(w)
                if not os.path.exists(stage_paths(w)['olean']):
                    gen(w, cs)
                with lock:
                    q_build.append(w)
        except Exception as e:
            state['err'] = repr(e)
            log(dict(step='error', where='gen', error=repr(e)))
        finally:
            state['gen_done'] = True

    def build_worker():
        while True:
            with lock:
                w = q_build.pop(0) if q_build else None
            if w is None:
                if state['gen_done']:
                    return
                time.sleep(2)
                continue
            P = stage_paths(w)
            if not os.path.exists(P['olean']):
                if stop():
                    return
                if a.stop_at and est(w) > a.stop_at - time.time():
                    log(dict(window=w, step='deferred', reason='estimated build time beyond --stop-at'))
                    P2 = stage_paths(w)
                    if os.path.exists(P2['src']):
                        os.remove(P2['src'])
                    continue
                while avail_gb() < a.min_avail_gb:
                    time.sleep(10)
                if not build(w, a.rss_cap_gb):
                    continue
            with lock:
                built.append(w)

    ths = [threading.Thread(target=gen_worker)] + [threading.Thread(target=build_worker) for _ in range(a.jobs)]
    for t in ths:
        t.start()
    while any(t.is_alive() for t in ths) or built:
        time.sleep(5)
        with lock:
            if built and state.get('first_built') is None:
                state['first_built'] = time.time()
            batch = list(built) if (len(built) >= a.verify_batch or not any(t.is_alive() for t in ths[1:])
                                    or (built and time.time() - state['first_built'] > 120)) else []
            if batch:
                state['first_built'] = None
            for w in batch:
                built.remove(w)
        if batch:
            for w in verify(batch):
                if not a.no_swap:
                    swap(w, agg_floor(w))
    print(json.dumps(dict(done=True, err=state['err'], disk_free_mb=round(disk_free_mb()))), flush=True)


def status(a):
    st = manifest()
    sw = [r['swap'] for r in st.values() if 'swap' in r]
    print(json.dumps(dict(swapped=len(sw), old_bytes=sum(r['old_bytes'] for r in sw),
                          new_bytes=sum(r['new_bytes'] for r in sw), freed=sum(r['freed'] for r in sw),
                          by_prefix={p: sum(1 for r in sw if r['window'][0] == p) for p in 'QRK'},
                          failed=[w for w, r in st.items() if any(not x.get('ok', True) for x in r.values())],
                          disk_free_mb=round(disk_free_mb()))))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('cmd', choices=['run', 'status'])
    ap.add_argument('--jobs', type=int, default=2)
    ap.add_argument('--ahead', type=int, default=3, help='generated sources waiting for a builder at most')
    ap.add_argument('--verify-batch', type=int, default=8)
    ap.add_argument('--min-disk-mb', type=float, default=250)
    ap.add_argument('--min-avail-gb', type=float, default=4)
    ap.add_argument('--rss-cap-gb', type=float, default=6.5)
    ap.add_argument('--no-swap', action='store_true', help='pilot: gen, build and verify only')
    ap.add_argument('--stop-at', type=float, default=0, help='start no new step after this UNIX time')
    ap.add_argument('windows', nargs='*')
    a = ap.parse_args()
    ws = []
    a.est = {}
    for m in a.windows:
        if m.startswith('@'):
            for x in open(m[1:]):
                if x.strip() and not x.startswith('#'):
                    f = x.split('\t')
                    ws.append(f[0])
                    a.est[f[0]] = float(f[4])   # cpu_est_s of order.tsv
        else:
            ws.append(m)
    a.windows = ws
    {'run': run, 'status': status}[a.cmd](a)


if __name__ == '__main__':
    main()
