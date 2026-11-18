#!/usr/bin/env python3
"""Distributed production of Lean 4.35 certificates for a certificate plan of
milestones/28-combined-identities/certplan231.py (milestone 36).

    prod435.py setup                                    port + build the 86-module core stack (once per machine)
    prod435.py run --plan P --index I --workers W --hours H [--procs 4] [--mem-gb 12]   owner I of W
    prod435.py run --steal --plan P --index J --hours H                                helper J (work stealing)
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
above it runs alone; a waiting big build keeps its room (smaller builds pass it only if both fit, or,
while it is blocked anyway by running builds too big to run beside it, if the other running builds plus
the passing one leave room for it: small builds fill the idle cores beside a long big build).
A restart reuses a finished generation of the same certificate (job directory kept until published).
Prediction: 1.9 GB + 0.14 GB per million plan hints (see predict_gb); the watchdog kills a lean above max(7, 2 x prediction), at most 13 GB.
The generation phase of the replay step of a job from 5 M plan hints on (gen_lean_lrat_v3, Python, several GB)
also runs under the budget, with 1.0 GB + 0.15 GB per million plan hints (gen_gb): it is paused when it starts
until the budget admits it (its CaDiCaL phase before stays at ~0.4 GB). Such jobs were OOM-killed next to builds. Its
CaDiCaL seeds run with --seed-jobs auto (idle cores only; $PROD435_SEED_JOBS overrides), same proof.

Work stealing (helpers). `run --steal --index J --plan P` (no --workers) is helper J: it takes items
of the WHOLE plan, smallest first (owners go largest first, so they meet at the end), and publishes
to <family>help/w<J> (xfer/c435help/w<J>). Coordination, all on the remote:
  - every run (owner or helper) scans the published set of the family and of its helpers
    (manifest.jsonl / record.json of every w* branch, partial fetch, every --scan-every s) and drops
    what is published there;
  - claims: one ref per machine, single writer: <family>claim/o<I> (owners) and <family>claim/h<J>
    (helpers), each holding claims.json of what that machine holds (class Claims); readers take the
    union. Helpers claim a batch before starting it; owners claim the next items for their free
    slots. Ties: the earlier claim wins, within 5 s the lower (kind, index) (owners first); a claimant
    waits 15 s after writing before it reads, so both sides agree, and the rule is re-applied at every
    read of the claims (--claims-every s; a losing running job is stopped). Claims are renewed every
    --heartbeat s, kept 1 h after publication, and expire after --claim-ttl h (default 2) without
    renewal: a dead machine's items go back. A claim write that keeps failing never stops a run (the
    item goes unclaimed; a duplicate is harmless).
  - `--ignore-claims` (helpers, with --names): build the named items even if claimed (a stuck owner).
  - a helper ends its run once no unclaimed, unpublished item has been available for --steal-idle s
    (default 600; logged as 'helper idle'), so a chain of plans moves on to the next one.
  - families are separate: the paid family c435 never reads c435free (names do not clash today, but a
    free plain seed has widened bounds), and a helper of the free family would use c435freehelp.
status / merge read the family and its helpers by default; the same module published twice must have
the same .olean sha256 (deterministic builds), a different one is a CONFLICT.
`--no-steal-check` turns the scan and claims off for an owner. $PROD435_URL replaces the remote (tests).

Work directory: $PROD435_HOME (default ~/l435/prod). Core stack: $PROD435_HOME/core.
"""
import argparse, gzip, hashlib, json, os, random, re, shutil, socket, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
HOME = os.environ.get('PROD435_HOME', os.path.expanduser('~/l435/prod'))
CORE = os.path.join(HOME, 'core')
LEAN = '/opt/lean-4.35.0-linux/bin/lean'
PFX = os.environ.get('PROD435_PFX', 'refs/heads/xfer/c435/')
HELP_PFX = PFX.rstrip('/') + 'help/'          # helpers (`run --steal`) of this family: xfer/c435help/w<J>
CLAIM_PFX = PFX.rstrip('/') + 'claim/'        # claims, one ref per machine: xfer/c435claim/o<I>, h<J>
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
    if os.environ.get('PROD435_URL'):                     # tests: a local bare repository as the remote
        return os.environ['PROD435_URL']
    return subprocess.run(['git', 'config', '--get', 'remote.origin.url'], cwd=ROOT, capture_output=True,
                          text=True).stdout.strip()


# ------------------------------------------------------------------ plan items
def adapt():
    """$PROD435_ADAPTER (a script path, e.g. lean435/tools/c230.py): its apply() patches the generators
    (key encoding, names, statement bounds) in this process; the certificate steps then run through
    $PROD435_CERT (default cert435.py)."""
    p = os.environ.get('PROD435_ADAPTER')
    if p:
        import importlib.util
        spec = importlib.util.spec_from_file_location('prod435_adapter', p)
        m = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(m)
        m.apply()
        return m
    return None


def family_build_gb(src_bytes):
    """build_gb, or the adapter's own fit (`build_gb(src_bytes)` of $PROD435_ADAPTER) when it has one."""
    m = adapt()
    return m.build_gb(src_bytes) if m is not None and hasattr(m, 'build_gb') else build_gb(src_bytes)


def plan_items(plan):
    """[(module, kind, key, level, est, name)] of the paid certificates (cert231.items)."""
    sys.path.insert(0, os.path.join(ROOT, 'milestones', '35-231-lean', 'certify'))
    adapt()
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


GEN_BUDGET_HINTS = float(os.environ.get('PROD435_GEN_BUDGET_HINTS', 5e6))   # replay generations from this plan estimate on are admitted under the memory budget


def gen_gb(est):
    # peak RSS of the replay step's generation (LRAT -> Lean, Python), by plan hints: a python3 of
    # 5.03 GB anon was OOM-killed at 39.33 M (ctx8 C801230140A453564K42, owner w1, next to a lean build)
    return 1.0 + 0.15 * est / 1e6


def build_gb(src_bytes):
    # peak RssAnon of the build by the size of its merged Lean source (known when the build starts), fit on
    # 21,670 published 231/232 builds: p99 0.36 GB below 0.1 MB, 0.88 at 0.1-0.5, 1.29 at 0.5-2, 1.71 at 2-5,
    # 2.35 at 5-20 MB; from 20 MB the upper envelope 3.0 + 0.0253 GB per MB (9.06 GB at 304 MB, 7.33 at 193).
    # The plan estimate can be 200x too low (S01203A4443: 6.6 GB built against 1.9 predicted).
    m = src_bytes / 1e6
    return max(min(0.8 + 0.2 * m, 3.5), 3.0 + 0.0253 * m if m >= 20 else 0)


def predict_gb(est):
    # peak RssAnon of the merged-module build, 4.35, by plan hints. Measured: 0.21 GB at 0.01 M,
    # 0.76 at 0.13, 1.16 at 0.23 (ctx), 1.52 at 0.38 (share), 1.51 at 1.62 (ctx), 1.66 at 3.93 (plain,
    # worker w0), 2.90 at 8.26 (share T012034A46536K21), 9.06 at 57.73 (share T012345A44456K29, the
    # largest 563/1 job: 51.4 M hints, lean 19,039 s); 4.19: 6.9 GB RSS at 38.8 M replay hints.
    # Upper envelope with ~10% margin: 1.9 GB + 0.14 GB per M (was 1.2 + 0.25, 15.6 GB at 57.7 M).
    return 1.9 + 0.14 * est / 1e6


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
            if fits and not fair:
                # Fill beside a running big build (18 Nov, 230 farm: owners sat at load 1.0 on 4 cores for
                # hours: one 2-3 h build of ~8 GB predicted ran, the next big build waited, and every small
                # fill build waited behind it, since 8 + 1 + 8 > 12). The bigger waiter B cannot start before
                # the running builds that do not fit beside it (v > limit - B, 'large') end, whatever the small
                # ones do; so a build may pass it if the non-large running builds plus this one still leave
                # room for B: when the large ones end, B starts at once. If B is blocked only by small
                # builds, the strict rule above applies (they drain).
                B = max(bigger)
                large = sum(v for v in st['run'].values() if v > self.limit - B)
                rest = used - large
                fair = large + B > self.limit and rest + need + B <= self.limit
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
GEN_PROC = 'gen_lean_lrat_v3'   # the LRAT -> Lean generation of the replay step: the only phase that needs GBs


def descendants(pid):
    kids = {}
    for d in os.listdir('/proc'):
        if d.isdigit():
            try:
                f = open(f'/proc/{d}/stat').read()
                kids.setdefault(int(f[f.rindex(')') + 2:].split()[1]), []).append(int(d))
            except (OSError, ValueError, IndexError):
                pass
    out, todo = [], [pid]
    while todo:
        for c in kids.get(todo.pop(), []):
            out.append(c)
            todo.append(c)
    return out


def run_step(cmd, env, D, step, budget, secs):
    """Run a step; with a budget, its generation process is paused (SIGSTOP) when it appears until the
    budget admits it, then resumed, and the budget is released when the step ends. The CaDiCaL phase
    before it stays small (0.4 GB for 2.6 h at 39 M hints; generation peak 4.5-5 GB), so it holds no budget."""
    import signal
    import types
    fo, fe = open(os.path.join(D, f'{step}.out.tmp'), 'w+'), open(os.path.join(D, f'{step}.err.tmp'), 'w+')
    pr = subprocess.Popen(cmd, env=env, stdout=fo, stderr=fe, text=True)
    held = False
    try:
        while pr.poll() is None:
            if budget is not None and not held:
                for c in descendants(pr.pid):
                    try:
                        cl = open(f'/proc/{c}/cmdline', 'rb').read()
                    except OSError:
                        continue
                    if GEN_PROC.encode() in cl:
                        try:
                            os.kill(c, signal.SIGSTOP)
                        except OSError:
                            break
                        try:
                            secs['gen_wait'] = budget.acquire()
                            held = True
                        finally:
                            try:
                                os.kill(c, signal.SIGCONT)
                            except OSError:
                                pass
                        break
            time.sleep(2)
    finally:
        if held:
            budget.release()
    fo.seek(0); fe.seek(0)
    r = types.SimpleNamespace(returncode=pr.returncode, stdout=fo.read(), stderr=fe.read())
    fo.close(); fe.close()
    os.remove(fo.name); os.remove(fe.name)
    return r


def cmd_one(a):
    """Generate, convert and build one certificate in --job-dir; writes JOB/result.json."""
    D = os.path.abspath(a.job_dir)
    os.makedirs(D, exist_ok=True)
    items = {it[5]: it for it in plan_items(a.plan)}
    mod, kind, key, level, est, name = items[a.name]
    env = dict(os.environ, CADICAL=a.cadical, CERT231_SCR=os.path.join(D, 'scr'), CERT435_DATA=os.path.join(D, 'data'),
               CERT435_CORE=os.path.join(HOME, 'cores'), CERT435_SEEDS=a.seeds or seeds_file(a.plan))
    c435 = [sys.executable] + (os.environ['PROD435_CERT'].split() if os.environ.get('PROD435_CERT') else
                               [os.path.join(HERE, 'cert435.py')])
    secs = {}
    k1 = {'ctx': 'ctx', 'share': 'share', 'plain': 'plain'}[kind]
    k2 = {'ctx': 'ctx', 'share': 'share', 'plain': 'seed'}[kind]
    plan_est = est
    for step, kinds in (('cores', k1), ('cnf', k2), ('replay', k2)):
        if step == 'cnf':
            # the plan's estimate can be far too low (193 published items had real proofs > 5x it, e.g.
            # T012301A36425K28: plan 0.31 M, cores estimate 67.7 M); the cores step's full-proof estimate
            # x 0.6 is the plan-equivalent size (real proofs are 0.28-0.72 of it): use the larger one for
            # the generation budget, parallel seeds and the build's memory prediction and cap
            try:
                cp = os.path.join(D, 'data', 'cores231_' + os.path.basename(a.plan).replace('.json.gz', '') + '.jsonl')
                est = max(est, 0.6 * json.loads(open(cp).read().strip().splitlines()[-1]).get('est_hints', 0))
            except (OSError, ValueError, IndexError):
                pass
        t0 = time.time()
        # big replays run their CaDiCaL seeds in parallel on idle cores ('auto': idle cores + 1, at most 8,
        # limited by memory and disk); the proof chosen does not depend on it (same source sha256 measured)
        sj = os.environ.get('PROD435_SEED_JOBS') or ('auto' if est >= GEN_BUDGET_HINTS else None)
        extra = ['--seed-jobs', sj] if step == 'replay' and sj else []
        big = step == 'replay' and est >= GEN_BUDGET_HINTS
        r = run_step(['nice', '-n', '10'] + c435 + [step, '--plan', a.plan, '--kinds', kinds] + extra + [name],
                     env, D, step, Budget(gen_gb(est), a.mem_gb) if big else None, secs)
        secs[step] = round(time.time() - t0, 1)
        open(os.path.join(D, f'{step}.log'), 'w').write(r.stdout + r.stderr)
        if r.returncode != 0 or '"error"' in r.stdout:
            return fail(D, mod, f'{step} failed (exit {r.returncode}): {(r.stdout + r.stderr)[-800:]}'
                        + ('' if 'Traceback' in r.stderr or step != 'replay' else
                           ' [no traceback: probably killed, e.g. OOM; see dmesg]'))
    t0 = time.time()
    out = os.path.join(D, 'scr', 'out')
    r = subprocess.run([sys.executable, os.path.join(HERE, 'to435.py'), '--in', out, '--out', os.path.join(D, 'src'),
                        name], capture_output=True, text=True)
    if r.returncode != 0:
        return fail(D, mod, f'to435 failed: {r.stdout[-400:]}{r.stderr[-800:]}')
    secs['to435'] = round(time.time() - t0, 1)
    srcf = os.path.join(D, 'src', mod.replace('.', '/') + '.lean')
    bgb = family_build_gb(os.path.getsize(srcf))
    secs['build_pred_gb'] = round(bgb, 2)
    cap = min(a.max_cap_gb, max(a.rss_cap_gb, bgb * 2))
    # builds are admitted while the predicted RssAnon of the running builds (and admitted generations)
    # stays within --mem-gb
    budget = Budget(bgb, a.mem_gb)
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
               plan_est_hints=plan_est, sched_est_hints=round(est), full_proof_hints=core.get('est_hints'), hints=rep.get('hints'),
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


class Scan:
    """What is published on the branches of some families: the module names of every `manifest.jsonl`
    and the `running` lists of every `record.json`. Only those blobs are fetched (partial fetch by
    object id, --filter=blob:none), into a separate bare repository; a branch is re-read only when its
    tip moved."""

    def __init__(self, pfxs, skip_ref=None):
        self.pfxs, self.skip_ref = pfxs, skip_ref
        self.b = os.path.join(HOME, 'scan.git')
        if not os.path.exists(os.path.join(self.b, 'HEAD')):
            os.makedirs(self.b, exist_ok=True)
            git('init', '-q', '--bare', self.b)
        self.url = url()
        self.cache = {}                                   # ref -> (tip, modules, running)

    def _blobs(self, shas):
        miss = [x for x in shas if subprocess.run(['git', 'cat-file', '-e', x], cwd=self.b,
                                                   capture_output=True).returncode != 0]
        for i in range(0, len(miss), 200):
            retry(lambda: git('fetch', '-q', '--filter=blob:none', self.url, *miss[i:i + 200], cwd=self.b))

    def refresh(self):
        """-> (published modules, modules running at their owners) over all branches w* of the families."""
        tips = {}
        for pfx in self.pfxs:
            out = retry(lambda: git('ls-remote', self.url, pfx + 'w*', cwd=self.b, timeout=120))
            for l in out.splitlines():
                if '\t' in l:
                    t, ref = l.split('\t')
                    if ref != self.skip_ref and ref[len(pfx):].startswith('w'):
                        tips[ref] = t
        new = sorted({t for ref, t in tips.items() if self.cache.get(ref, (None,))[0] != t})
        for i in range(0, len(new), 100):
            retry(lambda: git('fetch', '-q', '--depth', '1', '--filter=blob:none', self.url, *new[i:i + 100],
                              cwd=self.b))
        want = {}
        for ref, t in tips.items():
            if self.cache.get(ref, (None,))[0] == t:
                continue
            ent = {l.split('\t')[1]: l.split()[2] for l in git('ls-tree', t, cwd=self.b).splitlines()}
            want[ref] = (t, ent.get('manifest.jsonl'), ent.get('record.json'))
        self._blobs([x for v in want.values() for x in v[1:] if x])
        for ref, (t, man, rec) in want.items():
            mods = set()
            if man:
                for l in git('cat-file', 'blob', man, cwd=self.b).splitlines():
                    if l.strip():
                        mods.add(json.loads(l)['module'])
            run = set()
            if rec:
                try:
                    run = set(json.loads(git('cat-file', 'blob', rec, cwd=self.b) or '{}').get('running') or [])
                except ValueError:
                    pass
            self.cache[ref] = (t, mods, run)
        for ref in list(self.cache):
            if ref not in tips:
                del self.cache[ref]
        pub = set().union(*[v[1] for v in self.cache.values()]) if self.cache else set()
        run = set().union(*[v[2] for v in self.cache.values()]) if self.cache else set()
        return pub, run


class Claims:
    """Claims, one ref per machine and a single writer per ref: <family>claim/o<I> (owner I) or
    <family>claim/h<J> (helper J), holding claims.json {module: [first claim time, renewal time]} of what
    that machine holds now (running or queued). The writer replaces it fast-forward on top of its own
    tip; no two machines ever write the same ref. Readers take the union of all claim refs (one
    ls-remote, then a fetch of the tips that moved).

    A claim is fresh while its renewal is younger than --claim-ttl h. Who keeps an item claimed twice:
    the earlier first claim (by more than WINDOW s); within WINDOW, the lower (kind, index), owners
    before helpers. A claimant writes its claim (re-stamped and written again if the push took more
    than 3 s, so a claim's time is when it became visible), waits SETTLE s and only then reads the
    union: two claims made within WINDOW are then seen by both sides, and a later claim always sees the
    earlier one, so both sides reach the same verdict. The rule is applied again at every refresh
    (a delayed push), and a loser drops the item (a running loser job is stopped). Nothing here can end a run: a write
    that keeps failing is given up (the item goes unclaimed; a duplicate is harmless, same .olean)."""

    WINDOW = 5
    SETTLE = 15

    def __init__(self, pfx, kind, index, ttl_h):
        self.pfx, self.kind, self.index, self.ttl = pfx, kind, index, ttl_h * 3600
        self.name = f'{kind}{index}'
        self.ref = pfx + self.name
        self.rank = (0 if kind == 'o' else 1, index)
        self.b = os.path.join(HOME, 'scan.git')
        if not os.path.exists(os.path.join(self.b, 'HEAD')):
            os.makedirs(self.b, exist_ok=True)
            git('init', '-q', '--bare', self.b)
        self.url = url()
        self.mine = {}                                    # module -> first claim time
        self.kept = {}                                    # published by me: claim kept until this time
        self.tip = None                                   # my ref's tip as last pushed / read
        self.cache = {}                                   # other ref -> (tip, {module: [t0, t1]})
        self.others = {}                                  # module -> [(rank, t0, t1)] fresh, other machines
        self.ok = 0                                       # time of the last good read

    @staticmethod
    def _rank(name):
        return (0 if name[0] == 'o' else 1, int(name[1:]))

    def read(self):
        """Refresh the union of the other machines' fresh claims (kept as is on a failure)."""
        try:
            out = git('ls-remote', self.url, self.pfx + '*', cwd=self.b, timeout=120)
            tips = {}
            for l in out.splitlines():
                if '\t' in l:
                    t, ref = l.split('\t')
                    nm = ref[len(self.pfx):]
                    if re.fullmatch(r'[oh]\d+', nm):
                        tips[nm] = t
            if self.name in tips and self.tip is None:
                self.tip = tips[self.name]
            new = sorted({t for nm, t in tips.items() if nm != self.name and self.cache.get(nm, (None,))[0] != t})
            for i in range(0, len(new), 100):
                git('fetch', '-q', '--depth', '1', self.url, *new[i:i + 100], cwd=self.b, timeout=300)
            for nm, t in tips.items():
                if nm == self.name or self.cache.get(nm, (None,))[0] == t:
                    continue
                try:
                    c = json.loads(git('cat-file', 'blob', f'{t}:claims.json', cwd=self.b) or '{}')
                except (RuntimeError, ValueError):
                    c = {}
                self.cache[nm] = (t, c)
            for nm in list(self.cache):
                if nm not in tips:
                    del self.cache[nm]
            now = time.time()
            oth = {}
            for nm, (t, c) in self.cache.items():
                for m, v in c.items():
                    if now - v[1] < self.ttl:
                        oth.setdefault(m, []).append((self._rank(nm), v[0], v[1]))
            self.others = oth
            self.ok = now
            return True
        except (RuntimeError, subprocess.TimeoutExpired, OSError, ValueError) as e:
            log(f'claims: read failed (kept the last union): {str(e)[:160]}')
            return False

    def busy(self):
        """Modules another machine holds a fresh claim on."""
        return set(self.others)

    def wins(self, m):
        t0 = self.mine.get(m, time.time())
        for rk, o0, _ in self.others.get(m, ()):
            if o0 < t0 - self.WINDOW or (abs(o0 - t0) <= self.WINDOW and rk < self.rank):
                return False
        return True

    def write(self):
        """Push my current claims (fast-forward on my own ref). False if it kept failing."""
        now = time.time()
        for m, t in list(self.kept.items()):
            if t < now:
                del self.kept[m]
                self.mine.pop(m, None)
        body = {m: [t0, now] for m, t0 in sorted(self.mine.items())}
        for i in range(4):
            try:
                blob = git('hash-object', '-w', '--stdin', cwd=self.b,
                           inp=json.dumps(body, separators=(',', ':')).encode(), binary=True).decode().strip()
                tree = git('mktree', cwd=self.b, inp=f'100644 blob {blob}\tclaims.json\n').strip()
                cmd = ['-c', 'user.name=prod435', '-c', 'user.email=prod435@localhost', 'commit-tree', tree,
                       '-m', f'prod435 claims {self.name}: {len(body)}']
                if self.tip:
                    cmd[-2:-2] = ['-p', self.tip]
                c = git(*cmd, cwd=self.b).strip()
                git('push', '-q', self.url, f'{c}:{self.ref}', cwd=self.b, timeout=120)
                self.tip = c
                return True
            except (RuntimeError, subprocess.TimeoutExpired, OSError) as e:
                # rejected: my ref moved (a restart with an older tip, or a second machine with my index):
                # take its tip as the parent and retry; network errors: back off
                try:
                    out = git('ls-remote', self.url, self.ref, cwd=self.b, timeout=120)
                    t = next((l.split('\t')[0] for l in out.splitlines() if l.endswith('\t' + self.ref)), None)
                    if t and t != self.tip:
                        git('fetch', '-q', '--depth', '1', self.url, t, cwd=self.b, timeout=120)
                        self.tip = t
                except (RuntimeError, subprocess.TimeoutExpired, OSError):
                    pass
                log(f'claims: write {i + 1} failed: {str(e)[:160]}')
                time.sleep(min(60, 3 * 2 ** i))
        log('claims: write given up (items stay unclaimed until the next write)')
        return False

    def claim(self, mods):
        """Claim modules, then keep those this machine wins; the rest are dropped again."""
        for _ in range(3):
            t = time.time()
            for m in mods:
                self.mine[m] = t
            if not self.write():
                return list(mods)                         # could not claim: go on unclaimed (harmless duplicate)
            if time.time() - t <= 3:
                break
        time.sleep(self.SETTLE)
        self.read()
        lost = [m for m in mods if not self.wins(m)]
        if lost:
            for m in lost:
                self.mine.pop(m, None)
            self.write()
        return [m for m in mods if m not in lost]

    def published(self, mods, keep_s=3600):
        # a published item keeps its claim for a while: until every scan has seen the publication
        for m in mods:
            if m in self.mine:
                self.kept[m] = time.time() + keep_s

    def drop(self, mods):
        mods = [m for m in mods if m in self.mine]
        for m in mods:
            del self.mine[m]
        if mods:
            self.write()


# ------------------------------------------------------------------ run
def cmd_run(a):
    os.makedirs(HOME, exist_ok=True)
    I, W = a.index, a.workers
    me = f'w{I}'
    steal = a.steal
    pub_pfx = HELP_PFX if steal else PFX
    if steal and W is None:
        W = 0
    elif W is None:
        raise SystemExit('--workers is required (except with --steal)')
    fam = f'{pub_pfx[11:]}{me}'
    if not os.path.exists(os.path.join(CORE, 'LocalWindowShareCtx.olean')):
        raise SystemExit(f'no core stack in {CORE}: run `prod435.py setup` first')
    stopf = os.path.join(HOME, 'STOP')
    if os.path.exists(stopf):
        os.remove(stopf) if open(stopf).read().startswith('ctl') else None
    repo = Repo(pub_pfx)
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
            log(f'restored {len(done)} certificates from {fam} ({tip[:10]})')
    seeds = a.seeds or seeds_file(a.plan)
    allitems = plan_items(a.plan)
    todo = [it for it in allitems if (steal or mine(it[0], I, W)) and it[0] not in done]
    if a.names is not None:
        if not a.names:
            raise SystemExit('--names given without names')
        todo = [it for it in todo if it[5] in a.names or it[0] in a.names]
    if a.kinds:
        todo = [it for it in todo if it[1] in a.kinds.split(',')]
    if steal:
        todo.sort(key=lambda it: (it[4], it[0]))        # helpers: smallest first (owners go largest first)
    else:
        todo.sort(key=lambda it: (-it[4], it[0]))       # largest first
    who = f'{fam}@{socket.gethostname()}'
    log(('helper ' + fam if steal else f'worker {I}/{W}') +
        f': {len(todo)} certificates to do, {sum(it[4] for it in todo) / 1e6:.1f} M plan hints')
    # work stealing: the published set of this family and of its helpers, and the claims of all machines
    scan = claims = None
    published, running_elsewhere, busy = set(), set(), set()
    last_scan = last_claims = last_beat = last_try = 0
    queue = []                                           # helpers: claimed, not started yet
    if not a.no_sync and not a.no_steal_check:
        scan = Scan([PFX, HELP_PFX], skip_ref=pub_pfx + me)
        claims = Claims(CLAIM_PFX, 'h' if steal else 'o', I, a.claim_ttl)

    def rescan(force=False):
        # published (anywhere in the family or its helpers): dropped for good; claimed by another machine
        # or running at an owner: skipped while that lasts (a stale claim gives the item back)
        nonlocal busy, last_scan, last_claims, todo, queue
        if scan is None:
            return
        now = time.time()
        if force or now - last_scan > a.scan_every:
            try:
                pub, run = scan.refresh()
                published.clear(); published.update(pub)
                running_elsewhere.clear(); running_elsewhere.update(run if steal else ())
            except Exception as e:  # noqa: BLE001
                log(f'scan failed (kept the last one): {str(e)[:200]}')
            last_scan = now
        if force or now - last_claims > a.claims_every:
            claims.read()
            last_claims = now
            busy = set() if a.ignore_claims else claims.busy() | running_elsewhere
            # an item claimed twice: the loser drops it (queued), or stops its job if it is running
            lost = [] if a.ignore_claims else [m for m in list(claims.mine) if not claims.wins(m)]
            for m in lost:
                if m in running:
                    pr = running.pop(m)[0]
                    try:
                        os.killpg(pr.pid, 9)
                    except OSError:
                        pass
                    pr.wait()
                    log(f'{m}: claimed earlier by another machine: job stopped')
            queue[:] = [it for it in queue if it[0] not in lost]
            if lost:
                claims.drop(lost)
        for m in [m for m in running if m in published]:
            # published elsewhere meanwhile (a duplicate, e.g. --ignore-claims or an expired claim): stop it
            pr = running.pop(m)[0]
            try:
                os.killpg(pr.pid, 9)
            except OSError:
                pass
            pr.wait()
            log(f'{m}: published elsewhere: job stopped')
        n0 = len(todo) + len(queue)
        todo = [it for it in todo if it[0] not in published]
        gone = [it[0] for it in queue if it[0] in published]
        queue = [it for it in queue if it[0] not in published]
        if gone:
            claims.drop(gone)
        if n0 - len(todo) - len(queue):
            log(f'{n0 - len(todo) - len(queue)} certificates published elsewhere: skipped')

    rng = random.Random(f'{I}-{os.getpid()}-{time.time()}')

    def claim_batch(free):
        # helpers: a batch of small items nobody holds: at least `free` items and --claim-batch-hints of work.
        # All helpers sort alike (smallest first), so taking the very first candidates made them all race for
        # the same few items, and the 5 s tie rule (lower index wins) starved the high-index helpers (h17: no
        # build for 3 h, "claimed 0, 8-10 lost" every round). Now each helper draws its batch at random from a
        # wide window of the smallest unclaimed candidates, then runs it smallest first.
        nonlocal todo
        cands = [it for it in todo if it[0] not in published and it[0] not in busy and it[0] not in claims.mine]
        win = cands[:max(400, 50 * free)]
        rng.shuffle(win)
        got = []
        for it in win:
            got.append(it)
            if (len(got) >= free and sum(x[4] for x in got) >= a.claim_batch_hints) or len(got) >= 200:
                break
        if not got:
            return []
        got.sort(key=lambda it: (it[4], it[0]))
        keep = set(claims.claim([it[0] for it in got]))
        if a.ignore_claims:
            keep = {it[0] for it in got}
        busy.update(it[0] for it in got if it[0] not in keep)   # lost: stays in todo, skipped while claimed
        todo = [it for it in todo if it[0] not in keep]
        mine_ = [it for it in got if it[0] in keep]
        queue.extend(mine_)
        log(f'claimed {len(mine_)} certificates ({sum(it[4] for it in mine_) / 1e6:.2f} M plan hints)'
            + (f'; {len(got) - len(mine_)} lost to other claims' if len(got) > len(mine_) else '')
            + f' (window {len(win)} of {len(cands)} unclaimed)')
        return mine_

    def heartbeat():
        nonlocal last_beat
        if claims is None or time.time() - last_beat < a.heartbeat:
            return
        last_beat = time.time()
        if claims.mine:
            claims.write()

    if steal and claims is None:
        raise SystemExit('--steal needs git (no --no-sync)')
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
                                             helper=steal, done=len(done), todo=len(todo) + len(queue) + len(running),
                                             failed=len(failed), running=sorted(running),
                                             t=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()))).encode()
        cur = repo.ls().get(me)
        if cur != tip:
            raise SystemExit(f'{fam} moved to {cur} under us (another worker with index {I}?): stopping')
        tip = repo.push(me, add, tip, f'prod435 {me}: {len(done)} certificates')
        log(f'published {len(pending_pub)} -> {fam} ({len(done)} in all, {tip[:10]})')
        for res, D in pending_pub:
            if not a.keep:
                shutil.rmtree(D, ignore_errors=True)
        if claims is not None:
            claims.published([res['module'] for res, D in pending_pub])
        pending_pub.clear()
        last_pub = time.time()

    last_avail, idle_end = time.time(), False
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
        rescan()
        heartbeat()
        # start jobs
        def waiting():
            try:
                w = json.load(open(os.path.join(HOME, 'budget.json'))).get('wait', {})
            except (OSError, ValueError):
                return 0
            return sum(1 for x in running.values() if str(x[0].pid) in w)
        # a job whose build waits for memory does not hold a core: another job may start (up to 2 x procs)
        while not stop and len(running) - waiting() < a.procs and len(running) < 2 * a.procs:
            if steal:
                if not queue and todo and time.time() - last_try > 120:
                    last_try = time.time()
                    try:
                        if claim_batch(a.procs - (len(running) - waiting())):
                            last_try = 0
                    except Exception as e:  # noqa: BLE001
                        log(f'claim failed (continuing): {str(e)[:200]}')
                src = queue
            else:
                src = todo
            free_ = [i for i, x in enumerate(src) if x[0] not in busy]            # claimed elsewhere: later
            fill = not steal and bool(waiting()) and bool(free_)
            if fill:
                # owners: a build of mine waits for memory, so another big job would wait too: fill the
                # free core with my smallest item (small builds fit beside big ones)
                k = min(free_, key=lambda i: (src[i][4], src[i][0]))
            else:
                k = free_[0] if free_ else None
            if k is None:
                break
            it = src[k]
            if claims is not None and not steal and it[0] not in claims.mine:
                # owners: claim the next items for all free slots at once (one settle wait)
                nfree = max(1, a.procs - (len(running) - waiting()))
                batch = [it] + ([] if fill else [x for x in src if x[0] not in busy and x[0] not in claims.mine
                                                 and x is not it][:nfree - 1])
                keep = set(claims.claim([x[0] for x in batch]))
                lost = [x[0] for x in batch if x[0] not in keep]
                busy.update(lost)
                if lost:
                    log(f'{len(lost)} certificates claimed by another machine: later')
                if it[0] not in keep:
                    continue
            g = predict_gb(it[4])
            st = os.statvfs(HOME)
            if st.f_bavail * st.f_frsize < a.min_free_gb * 2**30:
                log('disk below the floor: not starting new jobs')
                break
            src.pop(k)
            D = os.path.join(HOME, 'jobs', it[5])
            os.makedirs(D, exist_ok=True)                 # a finished generation of an earlier run is reused
            if os.path.exists(os.path.join(D, 'result.json')):
                os.remove(os.path.join(D, 'result.json'))
            cmd = [sys.executable, os.path.abspath(__file__), 'one', '--plan', a.plan, '--name', it[5], '--job-dir', D,
                   '--seeds', seeds, '--rss-cap-gb', str(a.rss_cap_gb), '--cadical', a.cadical,
                   '--mem-gb', str(a.mem_gb), '--max-cap-gb', str(a.max_cap_gb)]
            pr = subprocess.Popen(cmd, stdout=open(os.path.join(D, 'one.out'), 'w'), stderr=subprocess.STDOUT,
                                  start_new_session=True)     # its own process group (stopped as a whole)
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
                    (queue if steal else todo).append(it)
                if claims is not None and (failed[mod] >= 2 or not steal):
                    claims.drop([mod])                    # give the item back at once
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
        if steal:
            # a helper ends when nothing unclaimed and unpublished has been available for --steal-idle s
            # (items claimed elsewhere only come back if those claims expire), so chained plans advance
            if running or queue or any(it[0] not in busy and it[0] not in published for it in todo):
                last_avail = time.time()
            elif time.time() - last_avail > a.steal_idle:
                log(f'helper idle: no unclaimed unpublished item for {a.steal_idle:.0f} s '
                    f'({len(todo)} left, all claimed elsewhere): ending')
                idle_end = True
        if not running and (stop or idle_end or not (todo or queue)):
            if pending_pub:
                publish()
            break
        time.sleep(2)
    log(('helper ' + fam if steal else f'worker {I}/{W}') + f' ends: {len(done)} published, {len(todo) + len(queue)} left, {len(failed)} failed'
        + (' (STOP)' if os.path.exists(stopf) else '') + (' (idle)' if idle_end else ''))


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
    for pfx in a.pfx or [PFX, HELP_PFX]:
        repo = Repo(pfx)
        tips = repo.ls()
        ws = sorted((n for n in tips if n.startswith('w')), key=lambda n: int(n[1:]))
        pass
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
    try:
        cl = Claims(CLAIM_PFX, 'x', 0, 2)
        cl.name = ''
        cl.read()
        print(f'claims: {len(cl.cache)} claim refs, {len(cl.others)} modules with a fresh claim (< 2 h)')
    except Exception as e:  # noqa: BLE001
        print(f'claims: unreadable ({str(e)[:100]})')
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
    for pfx in a.pfx or [PFX, HELP_PFX]:
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
    p.add_argument('--workers', type=int, default=None, help='W (owners); not used with --steal')
    p.add_argument('--steal', action='store_true', help='helper: take unpublished, unclaimed items of the whole '
                   'plan, smallest first, publish to <family>help/w<INDEX> (claims on <family>claim/h<INDEX>)')
    p.add_argument('--no-steal-check', action='store_true', help='owners: do not skip what helpers published or claimed')
    p.add_argument('--scan-every', type=float, default=600, help='s between scans of the published set')
    p.add_argument('--claim-ttl', type=float, default=2, help='hours a helper claim stays fresh without renewal')
    p.add_argument('--heartbeat', type=float, default=1200, help='s between renewals of a helper\'s claims')
    p.add_argument('--claims-every', type=float, default=120, help='s between reads of the claim refs')
    p.add_argument('--ignore-claims', action='store_true', help='helpers: build items even if another machine '
                   'claims them (a stuck owner; with --names; a duplicate publication is harmless)')
    p.add_argument('--steal-idle', type=float, default=600, help='helpers: end after this many s without an '
                   'unclaimed unpublished item')
    p.add_argument('--claim-batch-hints', type=float, default=5e6, help='helpers claim at least this much work at once')
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
