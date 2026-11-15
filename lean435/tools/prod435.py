#!/usr/bin/env python3
"""Distributed production of Lean 4.35 certificates for a certificate plan of
milestones/28-combined-identities/certplan231.py (milestone 36).

    prod435.py setup                                    port + build the 86-module core stack (once per machine)
    prod435.py run --plan P --index I --workers W --hours H [--procs 3] [--mem-gb 12] [--alone-gb 6]
    prod435.py status [--plan P]                        per-worker counts from the xfer/c435/w* branches
    prod435.py merge --out DIR                          all published interfaces + one manifest
    prod435.py free --plan P [--out F]                  the plan's free keys (233-era certificates, to rebuild in 4.35)
    prod435.py ctl --stop | --clear                     STOP all workers (xfer/c435/ctl), or clear it
    prod435.py one --plan P --name N --job-dir D        one certificate (used by `run`; also for tests)

Work item: one PAID certificate of the plan (`cert231.items`: ctx 7/8 keys, new 5-window share keys, new
plain keys). Worker I owns the items with sha1(module name) % W == I, where the module is
`LocalWindowCtxCert.<N>` (ctx) or `LocalWindowCert.<N>` (share, plain). Largest plan estimate first.

Per item (`one`, a subprocess with its own scratch directory):
  1. core      cert231.py cores  (CaDiCaL on the full CNF, the full-proof LRAT size)
  2. cnf       cert231.py cnf    (Cnf source, 4.19 form)
  3. replay    cert231.py replay (CaDiCaL LRAT of the core, checker v3 source, 4.19 form)
  4. to435.py  -> ONE 4.35 module: private data, `public theorem refuted : <literal statement>`
  5. build.py  against the locally built core stack (RssAnon watchdog)
  6. record    module, kind, key, level, sha256 of source and of every output part, hints, seconds,
               peak RSS, lean version, generator commit, host
cert231.py is run unchanged through cert435.py. Plain keys are certified one by one ("every key a seed":
a seed plan with no L1/L2 derivation, written by this script); `--seeds FILE` uses a real seed plan
(cert231.py plan) instead.

Publication, fast-forward only, to refs/heads/xfer/c435/w<I>: the PUBLIC .olean of every finished
certificate (flat file name `<Module>.olean`), `manifest.jsonl` (one line per certificate) and
`record.json` (worker state). No .olean.private and no sources (they are regenerable from the
generator commit). A restarted worker restores its manifest from its branch and skips what is there.
STOP: a file STOP in the work directory, or `prod435.py ctl --stop` (record.json {"stop": true} on
xfer/c435/ctl); running jobs finish, no new job starts.

Scheduling: at most --procs jobs (default 4) run at once, largest first; generation (CaDiCaL cores
and LRAT, single-threaded) is not limited further. Lean builds are admitted under a memory budget:
the predicted RssAnon of the running builds stays within --mem-gb (default 12 GB); a build predicted
above it runs alone; a waiting big build keeps its room (smaller builds pass it only if both fit).
A restart reuses a finished generation of the same certificate (job directory kept until published).
Prediction: 1.2 GB + 0.25 GB per million plan hints (see predict_gb); the watchdog kills a lean above max(7, 2 x prediction), at most 13 GB.

Work directory: $PROD435_HOME (default ~/l435/prod). Core stack: $PROD435_HOME/core.
"""
import argparse, gzip, hashlib, json, os, shutil, socket, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
HOME = os.environ.get('PROD435_HOME', os.path.expanduser('~/l435/prod'))
CORE = os.path.join(HOME, 'core')
LEAN = '/opt/lean-4.35.0-linux/bin/lean'
PFX = os.environ.get('PROD435_PFX', 'refs/heads/xfer/c435/')
PARTS = ('.olean', '.olean.server', '.olean.private', '.ir', '.ir.sig')
CAD_PATH = '/home/user/lean-deps/toolchain/lean-4.19.0-linux/bin/cadical'   # hard-coded by the 4.19 generators
sys.dont_write_bytecode = True


def log(msg):
    line = time.strftime('%H:%M:%S ') + msg
    print(line, flush=True)
    try:
        with open(os.path.join(HOME, 'prod435.log'), 'a') as f:
            f.write(line + '\n')
    except OSError:
        pass


def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def url():
    return subprocess.run(['git', 'config', '--get', 'remote.origin.url'], cwd=ROOT, capture_output=True,
                          text=True).stdout.strip()


# ------------------------------------------------------------------ plan items
def plan_items(plan):
    """[(module, kind, key, level, est, name)] of the paid certificates (cert231.items)."""
    sys.path.insert(0, os.path.join(ROOT, 'milestones', '35-231-lean', 'certify'))
    import cert231

    class A:
        pass
    A.plan = plan
    out = []
    for kind, k, name, est in cert231.items(A):
        mod = ('LocalWindowCtxCert.' if kind == 'ctx' else 'LocalWindowCert.') + name
        if kind == 'ctx':
            key, level = [k[0], list(k[1]), list(k[2])], k[3] + 1
        elif kind == 'share':
            key, level = [list(k[0]), list(k[1])], k[2] + 1
        else:
            key, level = [list(k[0]), list(k[1])], None
        out.append((mod, kind, key, level, est, name))
    return out


def mine(mod, I, W):
    return int(hashlib.sha1(mod.encode()).hexdigest(), 16) % W == I


def seeds_file(plan):
    """A seed plan in cert231's format in which every new plain key is its own seed (no widening)."""
    tag = os.path.basename(plan).replace('.json.gz', '')
    p = os.path.join(HOME, f'seeds_self_{tag}.json.gz')
    if os.path.exists(p):
        return p
    sys.path.insert(0, os.path.join(ROOT, 'milestones', '33-233-lean', 'certify'))
    import cert233 as C
    keys = [it[2] for it in plan_items(plan) if it[1] == 'plain']
    out = dict(summary=dict(keys=len(keys), seeds=len(keys), derived=0, note='prod435: every key a seed'),
               keys=[['k6', k[0], k[1]] for k in keys],
               seeds=[[i, [list(x) for x in C.GC.dir_bounds(tuple(k[1]))]] for i, k in enumerate(keys)],
               derive=[[i, 'self', None, None] for i in range(len(keys))])
    os.makedirs(HOME, exist_ok=True)
    tmp = p + '.tmp'
    with gzip.GzipFile(tmp, 'wb', mtime=0) as g:
        g.write(json.dumps(out, separators=(',', ':')).encode())
    os.replace(tmp, p)
    return p


def predict_gb(est):
    # peak RssAnon of the merged-module build, 4.35, by plan hints. Measured: 0.21 GB at 0.01 M,
    # 0.76 at 0.13, 1.16 at 0.23 (ctx), 1.52 at 0.38 (share), 1.51 at 1.62 (ctx), 1.66 at 3.93 (plain,
    # worker w0), 2.90 at 8.26 (share T012034A46536K21); 4.19: 6.9 GB RSS at 38.8 M replay hints.
    # Upper envelope: 1.2 GB + 0.25 GB per M.
    return 1.2 + 0.25 * est / 1e6


class Budget:
    """Admission of Lean builds under a memory budget shared by the jobs of this machine
    (HOME/budget.json under an flock). Fair: a build that does not fit registers as waiting; a later
    build is admitted past it only if both fit together (so a big build is never starved)."""

    def __init__(self, gb, limit):
        import fcntl
        self.fcntl, self.gb, self.limit = fcntl, gb, limit
        self.path = os.path.join(HOME, 'budget.json')
        self.lockf = open(os.path.join(HOME, 'budget.lock'), 'a')
        self.me = str(os.getpid())

    def _edit(self, f):
        self.fcntl.flock(self.lockf, self.fcntl.LOCK_EX)
        try:
            try:
                st = json.load(open(self.path))
            except (OSError, ValueError):
                st = {'run': {}, 'wait': {}}
            for k in ('run', 'wait'):
                st[k] = {p: v for p, v in st[k].items() if os.path.exists(f'/proc/{p}')}
            r = f(st)
            tmp = self.path + '.tmp'
            json.dump(st, open(tmp, 'w'))
            os.replace(tmp, self.path)
            return r
        finally:
            self.fcntl.flock(self.lockf, self.fcntl.LOCK_UN)

    def acquire(self):
        t0 = time.time()

        def try_(st):
            used = sum(st['run'].values())
            need = min(self.gb, self.limit)                  # a build above the budget runs alone
            bigger = [min(v, self.limit) for p, v in st['wait'].items() if p != self.me and v > self.gb]
            fits = not st['run'] or used + need <= self.limit
            fair = not bigger or used + need + max(bigger) <= self.limit   # never delays a bigger waiter
            if fits and fair:
                st['wait'].pop(self.me, None)
                st['run'][self.me] = need
                return True
            st['wait'][self.me] = self.gb
            return False
        while not self._edit(try_):
            time.sleep(3)
        return round(time.time() - t0, 1)

    def release(self):
        def rel(st):
            st['run'].pop(self.me, None)
            st['wait'].pop(self.me, None)
        self._edit(rel)


# ------------------------------------------------------------------ setup
def cmd_setup(a):
    t0 = time.time()
    os.makedirs(HOME, exist_ok=True)
    # no symlink needed: cert435.py points the generators at $CADICAL or `cadical` on PATH
    roots = open(os.path.join(ROOT, 'lean435', 'core-roots.txt')).read().split()
    src = os.path.join(HOME, 'core-src')
    subprocess.run([sys.executable, os.path.join(HERE, 'port.py'), '--out', src] + roots, check=True)
    r = subprocess.run([sys.executable, os.path.join(HERE, 'build.py'), '--src', src, '--build', CORE,
                        '--jobs', str(a.jobs)] + roots)
    if r.returncode != 0:
        raise SystemExit('setup: core build failed')
    man = os.path.join(CORE, 'core-manifest.jsonl')
    if os.path.exists(man):
        os.remove(man)
    subprocess.run([sys.executable, os.path.join(HERE, 'audit.py'), 'manifest', '--src', src, '--build', CORE,
                    '--out', man] + roots, check=True)
    log(f'setup done in {time.time() - t0:.0f} s: core stack in {CORE}')


# ------------------------------------------------------------------ one certificate
def cmd_one(a):
    """Generate, convert and build one certificate in --job-dir; writes JOB/result.json."""
    D = os.path.abspath(a.job_dir)
    os.makedirs(D, exist_ok=True)
    items = {it[5]: it for it in plan_items(a.plan)}
    mod, kind, key, level, est, name = items[a.name]
    env = dict(os.environ, CADICAL=a.cadical, CERT231_SCR=os.path.join(D, 'scr'), CERT435_DATA=os.path.join(D, 'data'),
               CERT435_CORE=os.path.join(HOME, 'cores'), CERT435_SEEDS=a.seeds or seeds_file(a.plan))
    c435 = [sys.executable, os.path.join(HERE, 'cert435.py')]
    secs = {}
    k1 = {'ctx': 'ctx', 'share': 'share', 'plain': 'plain'}[kind]
    k2 = {'ctx': 'ctx', 'share': 'share', 'plain': 'seed'}[kind]
    for step, kinds in (('cores', k1), ('cnf', k2), ('replay', k2)):
        t0 = time.time()
        extra = (['--seed-jobs', os.environ['PROD435_SEED_JOBS']]
                 if step == 'replay' and os.environ.get('PROD435_SEED_JOBS') else [])
        r = subprocess.run(['nice', '-n', '10'] + c435 + [step, '--plan', a.plan, '--kinds', kinds] + extra + [name],
                           env=env, capture_output=True, text=True)
        secs[step] = round(time.time() - t0, 1)
        open(os.path.join(D, f'{step}.log'), 'w').write(r.stdout + r.stderr)
        if r.returncode != 0 or '"error"' in r.stdout:
            return fail(D, mod, f'{step} failed: {(r.stdout + r.stderr)[-800:]}')
    t0 = time.time()
    out = os.path.join(D, 'scr', 'out')
    r = subprocess.run([sys.executable, os.path.join(HERE, 'to435.py'), '--in', out, '--out', os.path.join(D, 'src'),
                        name], capture_output=True, text=True)
    if r.returncode != 0:
        return fail(D, mod, f'to435 failed: {r.stdout[-400:]}{r.stderr[-800:]}')
    secs['to435'] = round(time.time() - t0, 1)
    cap = min(a.max_cap_gb, max(a.rss_cap_gb, predict_gb(est) * 2))
    # memory is controlled at the build only (generation above runs without a limit): builds are
    # admitted while the predicted RssAnon of the running builds stays within --mem-gb
    budget = Budget(predict_gb(est), a.mem_gb)
    secs['build_wait'] = budget.acquire()
    t0 = time.time()
    r = subprocess.run([sys.executable, os.path.join(HERE, 'build.py'), '--src', os.path.join(D, 'src'), '--build',
                        os.path.join(D, 'build'), '--lib', CORE, '--jobs', '1', '--big', f'{mod}={cap}', mod],
                       capture_output=True, text=True)
    secs['build'] = round(time.time() - t0, 1)
    budget.release()
    open(os.path.join(D, 'build.log'), 'w').write(r.stdout + r.stderr)
    if r.returncode != 0:
        return fail(D, mod, f'build failed: {(r.stdout + r.stderr)[-1500:]}')
    b = [json.loads(l) for l in open(os.path.join(D, 'build', 'build-log.jsonl'))][-1]
    srcf = os.path.join(D, 'src', mod.replace('.', '/') + '.lean')
    base = os.path.join(D, 'build', mod.replace('.', '/'))
    rep = {}
    rp = os.path.join(D, 'data', 'replay231_' + os.path.basename(a.plan).replace('.json.gz', '') + '.jsonl')
    if os.path.exists(rp):
        rep = json.loads(open(rp).read().strip().splitlines()[-1])
    core = {}
    cp = os.path.join(D, 'data', 'cores231_' + os.path.basename(a.plan).replace('.json.gz', '') + '.jsonl')
    if os.path.exists(cp):
        core = json.loads(open(cp).read().strip().splitlines()[-1])
    txt = open(srcf, encoding='utf-8').read()
    stmt = txt[txt.index('public theorem refuted'):].split(':=')[0].split(' : ', 1)[1].strip()
    res = dict(module=mod, kind=kind, key=key, level=level, name=name, plan=os.path.basename(a.plan),
               plan_est_hints=est, full_proof_hints=core.get('est_hints'), hints=rep.get('hints'),
               lemmas=rep.get('lemmas'), segments=rep.get('segments'), core_clauses=rep.get('core'),
               statement=stmt, imports=audit_header(srcf), source_sha256=sha(srcf), source_bytes=os.path.getsize(srcf),
               parts={e: sha(base + e) for e in PARTS if os.path.exists(base + e)},
               sizes={e: os.path.getsize(base + e) for e in PARTS if os.path.exists(base + e)},
               lean_cpu_s=b['cpu'], lean_wall_s=b['wall'], peak_anon_gb=b['anon_gb'], peak_rss_gb=b['rss_gb'],
               seconds=secs, lrat_s=rep.get('lrat_s'), producer=rep.get('producer'),
               lean=subprocess.run([LEAN, '--version'], capture_output=True, text=True).stdout.strip(),
               generator_commit=subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=ROOT, capture_output=True,
                                               text=True).stdout.strip(),
               core_manifest_sha256=sha(os.path.join(CORE, 'core-manifest.jsonl'))
               if os.path.exists(os.path.join(CORE, 'core-manifest.jsonl')) else None,
               host=socket.gethostname(), t=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()))
    json.dump(res, open(os.path.join(D, 'result.json'), 'w'))
    print(json.dumps(res))
    return 0


def audit_header(path):
    sys.path.insert(0, HERE)
    import audit
    return audit.header(path)


def fail(D, mod, msg):
    json.dump(dict(module=mod, error=msg[-3000:], t=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())),
              open(os.path.join(D, 'result.json'), 'w'))
    print(msg, file=sys.stderr)
    return 1


# ------------------------------------------------------------------ git transfer (farm231.py approach)
def git(*args, cwd=None, inp=None, timeout=600, binary=False):
    r = subprocess.run(['git', *args], cwd=cwd, capture_output=True, input=inp, timeout=timeout,
                       text=not binary)
    if r.returncode != 0:
        err = r.stderr if not binary else r.stderr.decode('utf-8', 'replace')
        raise RuntimeError(f'git {args[0]} failed: {err[-400:]}')
    return r.stdout


def retry(f, n=4, base=5):
    for i in range(n):
        try:
            return f()
        except (RuntimeError, subprocess.TimeoutExpired, OSError) as e:
            if i == n - 1:
                raise
            log(f'retry {i + 1}: {str(e)[:200]}')
            time.sleep(base * 2 ** i)


class Repo:
    """A persistent bare repository of this worker; only xfer/c435/* refs are ever fetched."""

    def __init__(self, pfx=None):
        self.pfx = pfx or PFX
        # local ref namespace: unchanged for the default prefix (workers), separate per other family
        self.ns = '' if self.pfx == PFX else 'f' + hashlib.sha1(self.pfx.encode()).hexdigest()[:8] + '/'
        self.b = os.path.join(HOME, 'git')
        if not os.path.exists(os.path.join(self.b, 'HEAD')):
            os.makedirs(self.b, exist_ok=True)
            git('init', '-q', '--bare', self.b)
        self.url = url()

    def ls(self):
        out = retry(lambda: git('ls-remote', self.url, self.pfx + '*', cwd=self.b, timeout=120))
        return {l.split('\t')[1][len(self.pfx):]: l.split('\t')[0] for l in out.splitlines() if '\t' in l}

    def fetch(self, names):
        if names:
            retry(lambda: git('fetch', '-q', '--depth', '1', self.url,
                              *[f'+{self.pfx}{n}:refs/x/{self.ns}{n}' for n in names], cwd=self.b))

    def files(self, name, only=None):
        out = {}
        for l in git('ls-tree', f'refs/x/{self.ns}{name}', cwd=self.b).splitlines():
            meta, path = l.split('\t')
            if only is None or path in only:
                out[path] = git('cat-file', 'blob', meta.split()[2], cwd=self.b, binary=True)
        return out

    def entries(self, name):
        return {l.split('\t')[1]: l.split('\t')[0].split()[2]
                for l in git('ls-tree', f'refs/x/{self.ns}{name}', cwd=self.b).splitlines()}

    def push(self, name, add, parent, msg):
        """New commit = parent's tree + `add` ({path: bytes}); pushed without force (fast-forward)."""
        ent = self.entries(name) if parent else {}
        for path, data in add.items():
            ent[path] = git('hash-object', '-w', '--stdin', cwd=self.b, inp=data, binary=True).decode().strip()
        tree = git('mktree', cwd=self.b, inp=''.join(f'100644 blob {s}\t{p}\n' for p, s in sorted(ent.items()))).strip()
        cmd = ['-c', 'user.name=prod435', '-c', 'user.email=prod435@localhost', 'commit-tree', tree, '-m', msg]
        if parent:
            cmd[-2:-2] = ['-p', parent]
        commit = git(*cmd, cwd=self.b).strip()
        retry(lambda: git('push', '-q', self.url, f'{commit}:{self.pfx}{name}', cwd=self.b))
        git('update-ref', f'refs/x/{self.ns}{name}', commit, cwd=self.b)
        return commit


# ------------------------------------------------------------------ run
def cmd_run(a):
    os.makedirs(HOME, exist_ok=True)
    I, W = a.index, a.workers
    me = f'w{I}'
    if not os.path.exists(os.path.join(CORE, 'LocalWindowShareCtx.olean')):
        raise SystemExit(f'no core stack in {CORE}: run `prod435.py setup` first')
    stopf = os.path.join(HOME, 'STOP')
    if os.path.exists(stopf):
        os.remove(stopf) if open(stopf).read().startswith('ctl') else None
    repo = Repo()
    done = {}
    tip = None
    if not a.no_sync:
        tips = repo.ls()
        if me in tips:
            repo.fetch([me])
            tip = tips[me]
            m = repo.files(me, only={'manifest.jsonl'}).get('manifest.jsonl', b'').decode()
            for l in m.splitlines():
                if l.strip():
                    r = json.loads(l)
                    done[r['module']] = r
            log(f'restored {len(done)} certificates from {PFX[11:]}{me} ({tip[:10]})')
    seeds = a.seeds or seeds_file(a.plan)
    todo = [it for it in plan_items(a.plan) if mine(it[0], I, W) and it[0] not in done]
    if a.names is not None:
        if not a.names:
            raise SystemExit('--names given without names')
        todo = [it for it in todo if it[5] in a.names or it[0] in a.names]
    if a.kinds:
        todo = [it for it in todo if it[1] in a.kinds.split(',')]
    todo.sort(key=lambda it: (-it[4], it[0]))           # largest first
    log(f'worker {I}/{W}: {len(todo)} certificates to do, {sum(it[4] for it in todo) / 1e6:.1f} M plan hints')
    failed = {}
    fp = os.path.join(HOME, f'failed_{me}.jsonl')
    if os.path.exists(fp):
        for l in open(fp):
            r = json.loads(l)
            failed[r['module']] = failed.get(r['module'], 0) + 1
    todo = [it for it in todo if failed.get(it[0], 0) < 2]
    if a.min_plan_hints:
        todo = [it for it in todo if it[4] >= a.min_plan_hints]
    if a.max_plan_hints:
        big = [it for it in todo if it[4] > a.max_plan_hints]
        todo = [it for it in todo if it[4] <= a.max_plan_hints]
        if big:
            log(f'{len(big)} certificates above --max-plan-hints {a.max_plan_hints:.3g} left out')
    running = {}                                        # module -> (proc, item, predicted GB, start)
    pending_pub = []
    t_end = time.time() + a.hours * 3600
    last_pub = last_ctl = 0
    stop = False

    def publish(force=False):
        nonlocal tip, last_pub
        if a.no_sync or not (pending_pub or force):
            return
        add = {}
        for res, D in pending_pub:
            add[res['module'] + '.olean'] = open(os.path.join(D, 'build', res['module'].replace('.', '/') + '.olean'),
                                                 'rb').read()
            done[res['module']] = res
        lines = sorted(json.dumps(r, sort_keys=True) for r in done.values())
        add['manifest.jsonl'] = ('\n'.join(lines) + '\n').encode()
        add['record.json'] = json.dumps(dict(index=I, workers=W, plan=os.path.basename(a.plan), host=socket.gethostname(),
                                             done=len(done), todo=len(todo) + len(running), failed=len(failed),
                                             t=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()))).encode()
        cur = repo.ls().get(me)
        if cur != tip:
            raise SystemExit(f'{PFX[11:]}{me} moved to {cur} under us (another worker with index {I}?): stopping')
        tip = repo.push(me, add, tip, f'prod435 {me}: {len(done)} certificates')
        log(f'published {len(pending_pub)} -> {PFX[11:]}{me} ({len(done)} in all, {tip[:10]})')
        for res, D in pending_pub:
            if not a.keep:
                shutil.rmtree(D, ignore_errors=True)
        pending_pub.clear()
        last_pub = time.time()

    while True:
        now = time.time()
        if not a.no_sync and now - last_ctl > 300:
            last_ctl = now
            try:
                tips = repo.ls()
                if 'ctl' in tips:
                    repo.fetch(['ctl'])
                    rec = json.loads(repo.files('ctl', only={'record.json'}).get('record.json', b'{}') or b'{}')
                    if rec.get('stop'):
                        open(stopf, 'w').write('ctl stop\n')
            except Exception as e:  # noqa: BLE001
                log(f'ctl check failed: {str(e)[:200]}')
        stop = os.path.exists(stopf) or now > t_end
        # start jobs
        def waiting():
            try:
                w = json.load(open(os.path.join(HOME, 'budget.json'))).get('wait', {})
            except (OSError, ValueError):
                return 0
            return sum(1 for x in running.values() if str(x[0].pid) in w)
        # a job whose build waits for memory does not hold a core: another job may start (up to 2 x procs)
        while not stop and todo and len(running) - waiting() < a.procs and len(running) < 2 * a.procs:
            it = todo[0]
            g = predict_gb(it[4])
            st = os.statvfs(HOME)
            if st.f_bavail * st.f_frsize < a.min_free_gb * 2**30:
                log('disk below the floor: not starting new jobs')
                break
            todo.pop(0)
            D = os.path.join(HOME, 'jobs', it[5])
            os.makedirs(D, exist_ok=True)                 # a finished generation of an earlier run is reused
            if os.path.exists(os.path.join(D, 'result.json')):
                os.remove(os.path.join(D, 'result.json'))
            cmd = [sys.executable, os.path.abspath(__file__), 'one', '--plan', a.plan, '--name', it[5], '--job-dir', D,
                   '--seeds', seeds, '--rss-cap-gb', str(a.rss_cap_gb), '--cadical', a.cadical,
                   '--mem-gb', str(a.mem_gb), '--max-cap-gb', str(a.max_cap_gb)]
            pr = subprocess.Popen(cmd, stdout=open(os.path.join(D, 'one.out'), 'w'), stderr=subprocess.STDOUT)
            running[it[0]] = (pr, it, g, time.time())
            log(f'start {it[0]} ({it[1]}, plan {it[4] / 1e6:.2f} M hints, predicted {g:.1f} GB)')
        # collect
        for mod in list(running):
            pr, it, g, t0 = running[mod]
            if pr.poll() is None:
                continue
            del running[mod]
            D = os.path.join(HOME, 'jobs', it[5])
            try:
                res = json.load(open(os.path.join(D, 'result.json')))
            except (OSError, ValueError):
                res = dict(module=mod, error=f'no result (exit {pr.returncode})')
            if 'error' in res:
                failed[mod] = failed.get(mod, 0) + 1
                with open(fp, 'a') as f:
                    f.write(json.dumps(dict(module=mod, plan_est_hints=it[4], memory='KILLED: RssAnon' in res['error'],
                                            error=res['error'][-1500:])) + '\n')
                log(f'FAILED {mod}: {res["error"][-300:]}')
                if 'KILLED: RssAnon' in res['error']:
                    failed[mod] = 99                      # memory: no retry on this machine
                    log(f'{mod} is too big for this machine (memory cap); listed in {fp}, not retried')
                elif failed[mod] < 2:
                    todo.append(it)
                continue
            log(f'done {mod}: {res["hints"]} hints, lean {res["lean_cpu_s"]} s, {res["peak_anon_gb"]} GB, '
                f'{sum(res["seconds"].values()):.0f} s in all')
            pending_pub.append((res, D))
        if pending_pub and (time.time() - last_pub > a.publish_every or not running):
            try:
                publish()
            except SystemExit:
                raise
            except Exception as e:  # noqa: BLE001
                log(f'publish failed (kept for the next try): {str(e)[:300]}')
        if not running and (stop or not todo):
            if pending_pub:
                publish()
            break
        time.sleep(2)
    log(f'worker {I}/{W} ends: {len(done)} published, {len(todo)} left, {len(failed)} failed'
        + (' (STOP)' if os.path.exists(stopf) else ''))


# ------------------------------------------------------------------ status / merge / free / ctl
def worker_manifests(repo, names):
    repo.fetch(names)
    out = {}
    for n in names:
        f = repo.files(n, only={'manifest.jsonl', 'record.json'})
        out[n] = ([json.loads(l) for l in f.get('manifest.jsonl', b'').decode().splitlines() if l.strip()],
                  json.loads(f.get('record.json', b'{}') or b'{}'))
    return out


def cmd_status(a):
    tot = dict(n=0, hints=0, cpu=0.0)
    have = set()
    for pfx in a.pfx or [PFX]:
        repo = Repo(pfx)
        tips = repo.ls()
        ws = sorted((n for n in tips if n.startswith('w')), key=lambda n: int(n[1:]))
        print(f'== {pfx}: {len(ws)} worker branches')
        if 'ctl' in tips:
            repo.fetch(['ctl'])
            print('ctl:', repo.files('ctl', only={'record.json'}).get('record.json', b'').decode())
        ms = worker_manifests(repo, ws)
        for n in ws:
            man, rec = ms[n]
            h = sum(r.get('hints') or 0 for r in man)
            c = sum(r.get('lean_cpu_s') or 0 for r in man)
            tot['n'] += len(man); tot['hints'] += h; tot['cpu'] += c
            have |= {r['module'] for r in man}
            print(f'{n}: {len(man)} certificates, {h / 1e6:.1f} M hints, lean {c / 3600:.2f} CPU-h; '
                  f'todo {rec.get("todo")}, failed {rec.get("failed")}, host {rec.get("host")}, at {rec.get("t")}')
    print(f'all: {tot["n"]} certificates ({len(have)} distinct modules), {tot["hints"] / 1e6:.1f} M hints, '
          f'lean {tot["cpu"] / 3600:.2f} CPU-h')
    for plan in a.plan or []:
        items = plan_items(os.path.abspath(plan))
        left = [it for it in items if it[0] not in have]
        print(f'plan {os.path.basename(plan)}: {len(items)} certificates, {len(left)} not published '
              f'({sum(it[4] for it in left) / 1e6:.0f} M plan hints)')


def cmd_merge(a):
    """All published interfaces of the given branch families into one directory and one manifest.
    A module published twice must have the same .olean sha256; otherwise it is rejected (left out,
    listed, exit 1)."""
    os.makedirs(a.out, exist_ok=True)
    lines, where, conflict, bad, nbr = {}, {}, set(), 0, 0
    for pfx in a.pfx or [PFX]:
        repo = Repo(pfx)
        tips = repo.ls()
        ws = sorted(n for n in tips if n.startswith('w'))
        nbr += len(ws)
        repo.fetch(ws)
        for w in ws:
            f = repo.files(w)
            for l in f.get('manifest.jsonl', b'').decode().splitlines():
                if not l.strip():
                    continue
                r = json.loads(l)
                m = r['module']
                data = f.get(m + '.olean')
                if data is None or hashlib.sha256(data).hexdigest() != r['parts']['.olean']:
                    print(f'{pfx}{w}: {m}.olean missing or not matching its manifest line', file=sys.stderr)
                    bad += 1
                    continue
                if m in lines:
                    if json.loads(lines[m])['parts']['.olean'] != r['parts']['.olean']:
                        conflict.add(m)
                        print(f'CONFLICT {m}: {where[m]} and {pfx}{w} published different .olean', file=sys.stderr)
                    continue
                p = os.path.join(a.out, m.replace('.', '/') + '.olean')
                os.makedirs(os.path.dirname(p), exist_ok=True)
                open(p, 'wb').write(data)
                lines[m] = json.dumps(r, sort_keys=True)
                where[m] = pfx + w
    for m in conflict:
        lines.pop(m, None)
        p = os.path.join(a.out, m.replace('.', '/') + '.olean')
        if os.path.exists(p):
            os.remove(p)
    open(os.path.join(a.out, 'manifest.jsonl'), 'w').write('\n'.join(lines[k] for k in sorted(lines)) + '\n')
    print(f'merged {len(lines)} certificate interfaces from {nbr} branches into {a.out}; '
          f'{len(conflict)} conflicting modules rejected, {bad} lines without a matching .olean')
    if conflict:
        sys.exit(1)


def cmd_collect(a):
    """Like `merge`, from local job directories (runs with --no-sync --keep; tests)."""
    jd = os.path.join(HOME, 'jobs')
    os.makedirs(a.out, exist_ok=True)
    lines = {}
    mp = os.path.join(a.out, 'manifest.jsonl')
    if os.path.exists(mp):
        for l in open(mp):
            if l.strip():
                lines[json.loads(l)['module']] = l.strip()
    for n in sorted(os.listdir(jd)):
        try:
            r = json.load(open(os.path.join(jd, n, 'result.json')))
        except (OSError, ValueError):
            continue
        if 'error' in r or (a.names and n not in a.names):
            continue
        src = os.path.join(jd, n, 'build', r['module'].replace('.', '/') + '.olean')
        if sha(src) != r['parts']['.olean']:
            continue
        dst = os.path.join(a.out, r['module'].replace('.', '/') + '.olean')
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        shutil.copyfile(src, dst)
        lines[r['module']] = json.dumps(r, sort_keys=True)
    open(mp, 'w').write('\n'.join(lines[k] for k in sorted(lines)) + '\n')
    print(f'collected {len(lines)} certificate interfaces into {a.out}')


def cmd_free(a):
    """The plan's free keys: what is reused from earlier (4.19) certificates and must be rebuilt in 4.35."""
    d = json.load(gzip.open(a.plan, 'rt'))
    out = []
    for r in d['plain']:
        if r['free']:
            out.append(dict(table='plain', key=r['key'], basis=r.get('basis')))
    for r in d['share']:
        if r['free']:
            out.append(dict(table='share', kind=r['kind'], key=r['key'], level=r['level'], basis=r.get('basis')))
    import collections
    c = collections.Counter((x['table'], x['basis']) for x in out)
    f = open(a.out, 'w') if a.out else None
    for x in out:
        if f:
            f.write(json.dumps(x) + '\n')
    for k, v in sorted(c.items()):
        print(f'{k[0]:6s} {k[1]:16s} {v:6d}  ' + {
            'reuse233': 'a 233-chain certificate (LocalWindowCnf/Unsat, 4.19): rebuild in 4.35',
            'reuse': 'a certificate of the 235-237 replays (4.19): rebuild in 4.35',
            'derive233_L1': 'glue only: L1 term from a 233 seed (the seed must be rebuilt)',
            'derive233_L2': 'glue only: L2 term from a 233 seed (the seed must be rebuilt)',
            'lean_floor': "main's floors (Floors233): the floors port, not a certificate",
            'free233': 'the 233 share certificate with its own cap: rebuild in 4.35',
        }.get(k[1], ''))
    print(f'{len(out)} free rows' + (f' -> {a.out}' if a.out else ''))


def cmd_ctl(a):
    repo = Repo()
    tips = repo.ls()
    parent = tips.get('ctl')
    if parent:
        repo.fetch(['ctl'])
    rec = dict(stop=bool(a.stop), t=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), host=socket.gethostname())
    c = repo.push('ctl', {'record.json': json.dumps(rec).encode()}, parent, f'prod435 ctl stop={rec["stop"]}')
    print(f'xfer/c435/ctl -> {c[:10]}: {rec}')


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest='cmd', required=True)
    p = sub.add_parser('setup')
    p.add_argument('--jobs', type=int, default=3)
    p = sub.add_parser('run')
    p.add_argument('--plan', required=True)
    p.add_argument('--index', type=int, required=True)
    p.add_argument('--workers', type=int, required=True)
    p.add_argument('--hours', type=float, default=24)
    p.add_argument('--procs', type=int, default=4, help='jobs at once (generation is single-threaded)')
    p.add_argument('--mem-gb', type=float, default=12, help='budget of predicted RssAnon of concurrent Lean builds')
    p.add_argument('--alone-gb', type=float, default=None, help='(not used any more; see --mem-gb)')
    p.add_argument('--rss-cap-gb', type=float, default=7, help='kill a lean above this (raised for big predictions)')
    p.add_argument('--max-cap-gb', type=float, default=13, help='upper limit of the per-build watchdog cap')
    p.add_argument('--min-free-gb', type=float, default=3)
    p.add_argument('--publish-every', type=float, default=600)
    p.add_argument('--seeds', default=None)
    p.add_argument('--kinds', default=None, help='ctx,share,plain (default all)')
    p.add_argument('--max-plan-hints', type=float, default=0, help='leave out certificates above this plan estimate')
    p.add_argument('--min-plan-hints', type=float, default=0, help='leave out certificates below this plan estimate')
    p.add_argument('--names', nargs='*', default=None)
    p.add_argument('--keep', action='store_true', help='keep the job directories (sources, private .olean)')
    p.add_argument('--no-sync', action='store_true', help='no git (tests)')
    p.add_argument('--cadical', default=os.environ.get('CADICAL') or shutil.which('cadical') or '/usr/local/bin/cadical')
    p = sub.add_parser('one')
    p.add_argument('--plan', required=True)
    p.add_argument('--name', required=True)
    p.add_argument('--job-dir', required=True)
    p.add_argument('--seeds', default=None)
    p.add_argument('--rss-cap-gb', type=float, default=7)
    p.add_argument('--mem-gb', type=float, default=12)
    p.add_argument('--max-cap-gb', type=float, default=13)
    p.add_argument('--cadical', default=os.environ.get('CADICAL') or shutil.which('cadical') or '/usr/local/bin/cadical')
    p = sub.add_parser('status')
    p.add_argument('--plan', action='append', default=None, help='plan(s) to count against (paid or free list)')
    p.add_argument('--pfx', nargs='+', default=None, help='branch families, default refs/heads/xfer/c435/')
    p = sub.add_parser('merge')
    p.add_argument('--out', required=True)
    p.add_argument('--pfx', nargs='+', default=None, help='branch families, default refs/heads/xfer/c435/')
    p = sub.add_parser('collect')
    p.add_argument('--out', required=True)
    p.add_argument('--names', nargs='*', default=None)
    p = sub.add_parser('free')
    p.add_argument('--plan', required=True)
    p.add_argument('--out', default=None)
    p = sub.add_parser('ctl')
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument('--stop', action='store_true')
    g.add_argument('--clear', action='store_true')
    a = ap.parse_args()
    if hasattr(a, 'plan') and isinstance(a.plan, str) and a.plan:
        a.plan = os.path.abspath(a.plan)
    r = {'setup': cmd_setup, 'run': cmd_run, 'one': cmd_one, 'status': cmd_status, 'merge': cmd_merge,
         'free': cmd_free, 'ctl': cmd_ctl, 'collect': cmd_collect}[a.cmd](a)
    sys.exit(r or 0)


if __name__ == '__main__':
    main()
