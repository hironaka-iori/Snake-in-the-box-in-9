#!/usr/bin/env python3
"""Refinement toward 231 on several machines at once (milestone 28, "Farm toward 231").

A symmetric worker with no coordinator.  W workers (index 0..W-1) run loop4's tests on the
near-critical part of the k6 product, each on the windows it owns, and exchange their result files
through short-lived git branches (refs/heads/xfer/231/w<I>, one per worker, fast-forward only).

Epoch (default 8 minutes):
  1. sync: `git ls-remote` of xfer/231/*, scoped depth-1 fetch of the peer branches whose tip changed,
     peer files written to data/farm231/<kind>_w<J>.jsonl.gz; a STOP record on xfer/231/ctl stops all;
  2. state: loop4.State rebuilt from every record (the milestone's data files plus data/farm231/*);
  3. evaluate: Howard's lambda and minimum cycle (loop4.State.evaluate), integer Bellman-Ford
     potential phi at lambda on the live core, reduced costs rc(e) = Q w(e) - P + phi(u) - phi(v) >= 0;
     a line goes to data/farm231/rounds_w<I>.jsonl;
  4. candidates: edges of the minimum cycle first, then the edges of the live core of
     {rc <= d Q} for d = 0, 1, 2, 3, 4, 6, 8, ... weight units (an edge of that core lies on a cycle
     whose mean is close to lambda + d; plain small rc alone is no signal, since every edge of the
     shortest-path forest has rc = 0); per edge, loop4's first open test of its step:
     (A) untested 6-window plain, (B) never-solved 5-window plain, (C) one threshold when
     lambda + margin - 120 A > S5: the 5-window at its next level, else ctx 7, then ctx 8;
  5. partition: a test is run only by worker int(sha1(window key).hexdigest(), 16) % W; the key is the
     window (k6, k5 or (ctx, dirs, t)), not the level, so one worker owns a window's whole ladder;
  6. run: a pool of --procs processes with loop4's work(); results are appended by the solver
     processes to data/farm231/{plain,share,ctx}_w<I>.jsonl (loop4's record formats) and applied to
     the in-memory state as they arrive; every --regen-s seconds (and whenever the queue runs dry)
     lambda, phi and the candidates are recomputed from the updated state, so the next level of a
     window that just succeeded is queued at once.  The pool is never drained at an epoch boundary:
     jobs started in one epoch finish in the next;
  7. publish: commit of this worker's files (gzip -9) with the previous tip as parent, pushed to
     refs/heads/xfer/231/w<I>.  A restarted worker first merges its branch's files into its local
     files, so it continues where its predecessor stopped.
Long retries (loop4's phase D) only when no owned candidate is left, at most procs - 1 at a time.
Exit when --hours is over, free disk < 300 MB, data/farm231/STOP exists, or the ctl branch says stop.

usage:
  nice -n 10 python3 farm231.py run --index I --workers W --hours H [--procs 4] [--epoch-min 8]
                                    [--tl 60] [--tl-thr 120] [--tl-long 1800] [--margin 12]
  python3 farm231.py status [--no-exact]
  python3 farm231.py stop [--clear]
  python3 farm231.py merge
Time limits as loop4 ran: plain tests --tl (60 s), thresholds --tl-thr (120 s), long retries --tl-long.
Environment: FARM_URL (git URL, default the GitHub URL of origin), FARM_SCR (scratch directory for the
temporary bare repositories, default ~/.farm231).
"""
import argparse, glob, gzip, hashlib, itertools, json, os, queue, shutil, signal, subprocess, sys
import tempfile, time
import multiprocessing as mp
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
import comb as C
import solvers as SV
import share7 as S7
import loop as LP
import loop3 as L3
import loop4 as L4

DATA = os.path.join(HERE, 'data')
FARM = os.path.join(DATA, 'farm231')
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
URL = os.environ.get('FARM_URL', 'https://github.com/hironaka-iori/Snake-in-the-box-in-9')
PFX = 'refs/heads/xfer/231/'
SCR = os.environ.get('FARM_SCR', os.path.join(os.path.expanduser('~'), '.farm231'))
KINDS = ('plain', 'share', 'ctx', 'rounds')
LEVELS_D = [0, 1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64]
LAM231 = 125400 / 225 / 120            # alpha units; the exact test adds R / (225 Q) (eval232.py)
OPLAIN_K6 = os.path.join(C.MS, '11-local-ceiling', 'k6_loop', 'oracle_plain.jsonl')
INF = 10 ** 6


def log(*a):
    C.log(*a)


# ------------------------------------------------------------------ record files
def read_lines(path):
    """Complete, parseable JSON lines of a (possibly gzipped, possibly growing) file."""
    if not os.path.exists(path):
        return []
    try:
        raw = gzip.open(path, 'rb').read() if path.endswith('.gz') else open(path, 'rb').read()
    except (OSError, EOFError) as e:
        log(f'cannot read {path}: {e}')
        return []
    out = []
    for l in raw.decode('utf-8', 'replace').split('\n'):
        l = l.strip()
        if not l:
            continue
        try:
            json.loads(l)
        except ValueError:
            continue                     # a line cut by a killed process
        out.append(l)
    return out


def farm_files(kind):
    return sorted(glob.glob(os.path.join(FARM, f'{kind}_w*.jsonl')) +
                  glob.glob(os.path.join(FARM, f'{kind}_w*.jsonl.gz')))


def farm_records(kind):
    for f in farm_files(kind):
        for l in read_lines(f):
            yield json.loads(l)


def own_path(kind, I):
    return os.path.join(FARM, f'{kind}_w{I}.jsonl')


def union_into(path, lines):
    """Append to `path` the lines that it does not hold yet; returns the number appended."""
    have = set(read_lines(path))
    new = [l for l in lines if l not in have]
    if new:
        raw = open(path, 'rb').read() if os.path.exists(path) else b''
        with open(path, 'a') as f:
            if raw and not raw.endswith(b'\n'):
                f.write('\n')                # never glue a record to a cut line
            f.write('\n'.join(new) + '\n')
    return len(new)


# ------------------------------------------------------------------ loaders of the existing modules,
# extended by the farm files (the existing loaders keep reading every committed data file)
_own_plain_unsat, _share_records, _ctx_records = C.own_plain_unsat, C.share_records, S7.records


def own_plain_unsat_farm():
    out = _own_plain_unsat()
    for r in farm_records('plain'):
        if r['result'] == 'UNSAT':
            for t in itertools.product(*[C.lumped_choices(a) for a in r['alpha']]):
                out.append(C.fp.lkey(tuple(r['dirs']), t))
    return out


def share_records_farm():
    O = _share_records()
    for r in farm_records('share'):
        if len(r['alpha']) == 5:
            O.apply(r)
    return O


def ctx_records_farm():
    return _ctx_records() + list(farm_records('ctx'))


C.own_plain_unsat = own_plain_unsat_farm
C.share_records = share_records_farm
S7.records = ctx_records_farm


class State(L4.State):
    """loop4.State on every record, the farm files included."""
    def __init__(self, tllong=1800):
        C.fp.K6.OPLAIN = OPLAIN_K6           # fp.Status redirects this module global; reset it per build
        super().__init__()
        n = 0
        for r in farm_records('plain'):      # loop4's second-Status reader, on the farm files
            if r['result'] == 'UNSAT':
                for t in itertools.product(*[C.lumped_choices(a) for a in r['alpha']]):
                    self.S.st[C.fp.lkey(tuple(r['dirs']), t)] = 'UNSAT'
            elif all(a[0] == a[1] or tuple(a) == (6, 21) for a in r['alpha']):
                k = C.fp.lkey(tuple(r['dirs']), tuple(C.GA.sym_of(tuple(a)) for a in r['alpha']))
                if self.S.st.get(k) in (None, 'TIMEOUT'):
                    self.S.st[k] = r['result']; n += 1
        # long retries already made (by any worker): TIMEOUT at >= 90 % of the long limit
        for r in farm_records('share'):
            if r['result'] == 'TIMEOUT' and r.get('seconds', 0) >= 0.9 * tllong and len(r['alpha']) == 5:
                self.long_tried.add(('5', C.fp.lkey(tuple(r['dirs']), tuple(C.GA.sym_of(tuple(a)) for a in r['alpha']))))
        for r in farm_records('ctx'):
            if r['result'] == 'TIMEOUT' and r.get('seconds', 0) >= 0.9 * tllong:
                self.long_tried.add((r['ctx'], tuple(r['dirs']), tuple(r['t'])))
        C.log(f'farm plain statuses reloaded ({n})')

    def potentials(self, lam):
        """Integer BF at lambda on the live core; returns (L, rc) with rc in units of 1 / Q."""
        idx = np.nonzero(self.ok)[0]
        U = self.G['U'][idx].astype(np.int64); V = self.G['V'][idx].astype(np.int64)
        L = idx[C.prune(int(self.G['n']), U, V)]
        U, V = self.G['U'][L].astype(np.int64), self.G['V'][L].astype(np.int64)
        w = 120 * self.G['A'][L].astype(np.int64) + self.G['S5'][L]
        P, Q = lam.numerator, lam.denominator
        pi, it = C.bellman_ford(int(self.G['n']), U, V, Q * w - P, 40000)
        if pi is None:
            raise RuntimeError('Bellman-Ford did not converge at lambda')
        return L, U, V, Q * w - P + pi[U] - pi[V]


# ------------------------------------------------------------------ candidates and ownership
def keystr(kind, key):
    if kind == 'c':
        ctx, c, t = key
        return 'X' + json.dumps([int(ctx), [int(x) for x in c], [int(x) for x in t]], separators=(',', ':'))
    return 'W' + json.dumps([[int(x) for x in key[0]], [int(x) for x in key[1]]], separators=(',', ':'))


def owner(ks, W):
    return int(hashlib.sha1(ks.encode()).hexdigest(), 16) % W


def step_job(st, e, need_lvl, tlp, tlt):
    """loop4's first open test of the step of transition e (an index into st.G), or None.
    Known UNSAT windows exclude the transition, as loop4 does."""
    ds, t, k5, k6 = C.step_windows(int(st.G['G'][e]), st.Pr)
    S = st.S.st
    if S.get(k6) == 'UNSAT' or S.get(k5) == 'UNSAT':
        if st.ok[e]:
            st.exclude(k6 if S.get(k6) == 'UNSAT' else k5)
        return None
    if S.get(k6) is None:
        return ('p6', k6, C.canon(ds[1:8]), t, tlp)
    s = st.share_state(k5)
    if S.get(k5) is None and not s.get('tested'):
        return ('p5', k5, tlp)
    need = need_lvl - 120 * int(st.G['A'][e])
    cur = int(st.G['S5'][e])
    if need <= cur:
        return None
    T = LP.next_T(s)
    if T is not None and T > cur:
        return ('t', k5, T, tlt)
    for ctx in (7, 8):
        c = C.canon(ds[8 - ctx:])
        T = L3.next_level(cur, st.X.get((ctx, c, tuple(t))))
        if T is not None:
            return ('c', (ctx, c, tuple(t)), T, tlt)
    return None


def long_job(st, e, tllong):
    """loop4's phase D for the step of e: a timed-out level above S5, or None."""
    ds, t, k5, k6 = C.step_windows(int(st.G['G'][e]), st.Pr)
    cur = int(st.G['S5'][e])
    s = st.share_state(k5)
    if ('5', k5) not in st.long_tried and s['fail'] < INF and s['lb'] < s['ub'] and s['fail'] > cur:
        return ('t', k5, min(s['fail'], s['ub']), tllong), ('5', k5)
    for ctx in (7, 8):
        c = C.canon(ds[8 - ctx:])
        sx = st.X.get((ctx, c, tuple(t)))
        if (ctx, c, tuple(t)) not in st.long_tried and cur < sx['fail'] < INF and sx['fail'] <= sx['ub']:
            return ('c', (ctx, c, tuple(t)), sx['fail'], tllong), (ctx, c, tuple(t))
    return None


def job_id(job):
    kind = job[0]
    T = job[2] if kind in ('t', 'c') else None
    return (kind, keystr(kind, job[1]), T)


def ordered_edges(st, lam, cyc):
    """Edge indices (into st.G) in priority order with their level: the minimum cycle (level -1),
    then the live core of {rc <= d Q} for d in LEVELS_D (within a level, by rc)."""
    t0 = time.time()
    L, U, V, rc = st.potentials(lam)
    tbf = time.time() - t0
    Q = lam.denominator
    seen = np.zeros(len(L), bool)
    out = [(int(e), -1) for e in cyc]
    pos = np.searchsorted(L, np.array(cyc, np.int64))
    seen[pos[(pos < len(L))]] = True
    for d in LEVELS_D:
        sel = np.nonzero(rc <= d * Q)[0]
        core = sel[C.prune(int(st.G['n']), U[sel], V[sel])]
        core = core[~seen[core]]
        seen[core] = True
        core = core[np.argsort(rc[core], kind='stable')]
        out.extend((int(L[i]), d) for i in core)
    return out, tbf


def candidates(st, lam, cyc, a, exclude_ids, busy=()):
    """Owned candidate jobs in priority order: list of (prio, job).  exclude_ids: job ids in flight or
    done in this process; busy: window keys with a job in flight.  Also returns the owned phase-D jobs (only if no candidate is left)."""
    t0 = time.time()
    edges, tbf = ordered_edges(st, lam, cyc)
    need_lvl = float(lam) + a.margin
    out, ids, longs = [], set(), []
    budget = a.budget or int(a.procs * a.epoch_min * 60 / 8 * 3)
    scanned = 0
    for e, d in edges:
        if len(out) >= budget:
            break
        scanned += 1
        if not st.ok[e]:
            continue
        job = step_job(st, e, need_lvl, a.tl, a.tl_thr)
        if job is None:
            continue
        ks = keystr(job[0], job[1])
        if owner(ks, a.workers) != a.index:
            continue
        jid = job_id(job)
        if jid in ids or jid in exclude_ids or ks in busy:
            continue
        ids.add(jid)
        rank = {'p6': 0, 'p5': 1, 't': 2, 'c': 2}[job[0]]
        out.append(((d, rank, len(out)), job))
    if not out:
        for e, d in edges[:200000]:
            if not st.ok[e]:
                continue
            lj = long_job(st, e, a.tl_long)
            if lj is None:
                continue
            job, lt = lj
            ks = keystr(job[0], job[1])
            if owner(ks, a.workers) != a.index or job_id(job) in exclude_ids or ks in busy:
                continue
            longs.append((job, lt))
            if len(longs) >= a.procs - 1:
                break
    out.sort(key=lambda z: z[0])
    return out, longs, dict(bf_s=round(tbf, 2), cand_s=round(time.time() - t0, 2), scanned=scanned,
                            edges=len(edges))


def apply_result(st, job, r):
    kind = job[0]
    if kind == 'p6':
        k6 = job[1]; st.S.st[k6] = r['result']
        if r['result'] == 'UNSAT':
            st.exclude(k6)
        elif r['result'] == 'SAT':
            st.X.apply(dict(dirs=list(job[2]), t=list(job[3]), ctx=7, result='SAT', witness5=r['witness5']))
    elif kind == 'p5':
        k5 = job[1]; st.S.st[k5] = r['result']
        if r['result'] == 'UNSAT':
            st.exclude(k5)
        elif r['result'] == 'SAT':
            st.O.apply(dict(dirs=r['dirs'], alpha=r['alpha'], kind='plain', result='SAT', witness=r['witness']))
    elif kind == 't':
        LP.apply_share(st, job[1], r)
    else:
        st.ctx_apply(r)


def tag(job, r):
    k = job[0]
    if k == 'c':
        k = f"c{r['ctx']}"
    if job[-1] > 1000:
        k = k.upper()                       # long retry
    return f"{k}:{r['result']}"


# ------------------------------------------------------------------ git transfer (xfer233.py approach)
def git(*args, cwd=None, inp=None, timeout=300):
    """git with text input/output; raises RuntimeError on failure."""
    r = subprocess.run(['git', *args], cwd=cwd or ROOT, capture_output=True, text=True, input=inp, timeout=timeout)
    if r.returncode != 0:
        raise RuntimeError(f'git {args[0]} failed: {r.stderr[-400:]}')
    return r.stdout


def gitb(*args, cwd=None, inp=None):
    """git with bytes input/output."""
    r = subprocess.run(['git', *args], cwd=cwd, capture_output=True, input=inp, timeout=300)
    if r.returncode != 0:
        raise RuntimeError(f'git {args[0]} failed: {r.stderr.decode("utf-8", "replace")[-400:]}')
    return r.stdout


def retry(f, n=3, base=5):
    for i in range(n):
        try:
            return f()
        except (RuntimeError, subprocess.TimeoutExpired, OSError) as e:
            if i == n - 1:
                raise
            log(f'retry {i + 1}: {str(e)[:200]}')
            time.sleep(base * 2 ** i)


def bare():
    os.makedirs(SCR, exist_ok=True)
    b = tempfile.mkdtemp(dir=SCR, prefix='x')
    git('init', '-q', '--bare', b, cwd=SCR)
    return b


def ls_remote():
    out = retry(lambda: git('ls-remote', URL, PFX + '*', timeout=120))
    return {l.split('\t')[1][len(PFX):]: l.split('\t')[0] for l in out.splitlines() if '\t' in l}


def fetch_trees(names, tips):
    """Depth-1 fetch of the branches `names` (one call); returns {name: {path: bytes}}."""
    if not names:
        return {}
    b = bare()
    try:
        retry(lambda: git('fetch', '-q', '--depth', '1', URL, *[f'{PFX}{n}:refs/x/{n}' for n in names],
                          cwd=b, timeout=600))
        out = {}
        for n in names:
            files = {}
            for l in gitb('ls-tree', f'refs/x/{n}', cwd=b).decode().splitlines():
                meta, path = l.split('\t')
                if meta.split()[1] == 'blob':
                    files[path] = gitb('cat-file', 'blob', meta.split()[2], cwd=b)
            out[n] = files
        return out
    finally:
        shutil.rmtree(b, ignore_errors=True)


def push_tree(name, files, parent, msg):
    """One commit with `files` ({path: bytes}) and `parent` (or none), pushed to xfer/231/<name>
    (fast-forward: the remote refuses a push whose parent is not its tip)."""
    b = bare()
    try:
        if parent:
            retry(lambda: git('fetch', '-q', '--depth', '1', URL, f'{PFX}{name}:refs/x/p', cwd=b, timeout=600))
        entries = []
        for path, data in sorted(files.items()):
            sha = gitb('hash-object', '-w', '--stdin', cwd=b, inp=data).decode().strip()
            entries.append(f'100644 blob {sha}\t{path}')
        tree = git('mktree', cwd=b, inp='\n'.join(entries) + '\n').strip()
        cmd = ['-c', 'user.name=farm231', '-c', 'user.email=farm231@localhost', 'commit-tree', tree, '-m', msg]
        if parent:
            cmd[-2:-2] = ['-p', parent]
        commit = git(*cmd, cwd=b).strip()
        retry(lambda: git('push', '-q', URL, f'{commit}:{PFX}{name}', cwd=b, timeout=600))
        return commit
    finally:
        shutil.rmtree(b, ignore_errors=True)


class Sync:
    """Branch tips and transfers of one worker (index None: a reader, e.g. `status`)."""
    def __init__(self, index):
        self.I = index
        self.tips_p = os.path.join(FARM, '.tips.json')
        try:
            self.tips = json.load(open(self.tips_p))
        except (OSError, ValueError):
            self.tips = {}
        self.pushed = None                   # tip of our branch as we pushed it
        self.remote = {}
        self.last_sig = None

    def save(self):
        tmp = self.tips_p + '.tmp'
        json.dump(self.tips, open(tmp, 'w')); os.replace(tmp, self.tips_p)

    def _merge_own(self, files):
        """Union of a branch tree of our own index into the local files."""
        n = 0
        for kind in KINDS:
            data = files.get(f'{kind}.jsonl.gz')
            if data:
                lines = [l for l in gzip.decompress(data).decode().split('\n') if l.strip()]
                n += union_into(own_path(kind, self.I), lines)
        return n

    def restore(self):
        """Worker start: merge the files of our own branch into the local files."""
        self.remote = ls_remote()
        me = f'w{self.I}'
        if me in self.remote:
            tr = fetch_trees([me], self.remote)[me]
            n = self._merge_own(tr)
            self.pushed = self.remote[me]
            log(f'restored {n} records from xfer/231/{me} ({self.pushed[:10]})')
        return self.remote

    def pull(self):
        """Fetch peer branches whose tip changed; returns (n branches fetched, stop flag)."""
        self.remote = ls_remote()
        stop = False
        names = [n for n, sha in self.remote.items() if n != f'w{self.I}' and self.tips.get(n) != sha
                 and (n == 'ctl' or n.startswith('w'))]
        trees = fetch_trees(names, self.remote)
        for n, files in trees.items():
            if n == 'ctl':
                try:
                    stop = bool(json.loads(files.get('record.json', b'{}')).get('stop'))
                except ValueError:
                    pass
                sp = os.path.join(FARM, 'STOP')
                if not stop and os.path.exists(sp) and open(sp).read().startswith('stop via xfer'):
                    os.remove(sp)             # the ctl branch was cleared
            else:
                for kind in KINDS:
                    data = files.get(f'{kind}.jsonl.gz')
                    if data is None:
                        continue
                    p = os.path.join(FARM, f'{kind}_{n}.jsonl.gz')
                    open(p + '.tmp', 'wb').write(data); os.replace(p + '.tmp', p)
            self.tips[n] = self.remote[n]
        if 'ctl' in names:
            self.tips['ctl_stop'] = stop
        else:
            stop = bool(self.tips.get('ctl_stop'))
        if stop:
            open(os.path.join(FARM, 'STOP'), 'w').write('stop via xfer/231/ctl\n')
        self.save()
        return len(names), stop

    def publish(self, meta):
        me = f'w{self.I}'
        tip = self.remote.get(me)
        if tip and tip != self.pushed:       # someone else pushed this index (or a restart): merge first
            n = self._merge_own(fetch_trees([me], self.remote)[me])
            log(f'merged {n} records from a foreign tip {tip[:10]} of {me}')
            self.pushed = tip
        files = {}
        for kind in KINDS:
            lines = read_lines(own_path(kind, self.I))
            files[f'{kind}.jsonl.gz'] = gzip.compress(('\n'.join(lines) + '\n').encode() if lines else b'', 9, mtime=0)
            meta[f'n_{kind}'] = len(lines)
        sig = hashlib.sha1(b''.join(files[k] for k in sorted(files))).hexdigest()
        if sig == self.last_sig and tip == self.pushed:
            return None
        files['record.json'] = json.dumps(meta).encode()
        commit = push_tree(me, files, tip, f'farm231 w{self.I} {meta.get("lam")}')
        self.pushed = commit; self.remote[me] = commit; self.last_sig = sig
        return commit


# ------------------------------------------------------------------ run
STOPPING = []


def _sigterm(*_):
    STOPPING.append('signal')


def run(a):
    os.makedirs(FARM, exist_ok=True)
    stopf = os.path.join(FARM, 'STOP')
    if os.path.exists(stopf) and open(stopf).read().startswith('stop via xfer') and not a.no_sync:
        os.remove(stopf)                  # came from the ctl branch: the first sync decides again
    if os.path.exists(stopf):
        log(f'{stopf} exists: not starting (remove it to run)'); return
    I, W = a.index, a.workers
    SV.OPL, SV.OSH, L4.CTXB = own_path('plain', I), own_path('share', I), own_path('ctx', I)
    rounds_p = own_path('rounds', I)
    sync = Sync(I)
    if not a.no_sync:
        try:
            sync.restore()
        except Exception as e:  # noqa: BLE001 - network trouble must not stop the worker
            log(f'restore failed: {str(e)[:300]}')
    pool = mp.get_context('fork').Pool(a.procs)    # forked before the state: small children
    signal.signal(signal.SIGTERM, _sigterm)         # after the fork: the children keep the default
    results = queue.Queue()
    inflight = {}                                   # job id -> (job, start, long?)
    done = set()
    t_start = time.time(); t_end = t_start + a.hours * 3600
    epoch = 0
    stats = {}
    st = None

    def handle(job, r):
        """One finished job: off the in-flight list, into the state (if there is one) and the stats."""
        jid = job_id(job)
        inflight.pop(jid, None); done.add(jid)
        if 'error' in r:
            log(f'job {jid} failed: {r["error"][:300]}')
            return 0
        if st is not None:
            apply_result(st, job, r)
        k = tag(job, r); stats[k] = stats.get(k, 0) + 1
        return 1

    while True:
        # ---------------- epoch start: sync, state, evaluate
        te = time.time()
        nfetch, stop = 0, False
        if not a.no_sync:
            try:
                nfetch, stop = sync.pull()
            except Exception as e:  # noqa: BLE001
                log(f'sync failed: {str(e)[:300]}')
        stop = stop or os.path.exists(stopf)
        t_sync = time.time() - te
        st = None
        t0 = time.time()
        st = State(a.tl_long)
        t_build = time.time() - t0
        while not results.empty():                  # results that arrived during the rebuild
            handle(*results.get())
        t0 = time.time()
        lam, cyc, nlive = st.evaluate()
        t_eval = time.time() - t0
        cands, longs, cinfo = candidates(st, lam, cyc, a, set(inflight) | done, {x[1] for x in inflight})
        rec = dict(time=time.strftime('%Y-%m-%d %H:%M:%S'), epoch=epoch, index=I, workers=W, lam=str(lam),
                   mu=float(lam) / 120, m_real=C.bound_real(float(lam), 1, 0, 0), len=len(cyc), live=nlive,
                   tests=stats, n_tests=sum(stats.values()), owned_candidates=len(cands), long_candidates=len(longs),
                   inflight=len(inflight), fetched=nfetch, sync_s=round(t_sync, 1), build_s=round(t_build, 1),
                   eval_s=round(t_eval, 2), rss_mb=round(C.rss_mb()), **cinfo)
        with open(rounds_p, 'a') as f:
            f.write(json.dumps(rec) + '\n')
        log(f"epoch {epoch}: lambda {lam} = {rec['mu']:.4f} m<={rec['m_real']:.3f} len {len(cyc)} "
            f"cands {len(cands)} tests {stats} [sync {t_sync:.0f}s build {t_build:.0f}s eval {t_eval:.1f}s "
            f"bf {cinfo['bf_s']}s cand {cinfo['cand_s']}s]")
        stats = {}
        if not a.no_sync:
            try:
                c = sync.publish(dict(index=I, workers=W, lam=str(lam), mu=float(lam) / 120, time=rec['time']))
                if c:
                    log(f'published {c[:10]} to xfer/231/w{I}')
            except Exception as e:  # noqa: BLE001
                log(f'publish failed: {str(e)[:300]}')
        if stop or STOPPING or time.time() >= t_end or C.disk_mb() < 300:
            why = 'STOP' if stop else 'signal' if STOPPING else 'hours over' if time.time() >= t_end else 'disk low'
            log(f'exit: {why}')
            break
        # ---------------- run until the epoch is over
        t_epoch = time.time() + a.epoch_min * 60
        t_regen = time.time()
        nres_since = 0
        while time.time() < min(t_epoch, t_end) and not STOPPING and not os.path.exists(stopf):
            nlong = sum(1 for v in inflight.values() if v[2])
            # fill free slots: candidates first, long retries only when no candidate is left
            busy = {x[1] for x in inflight}          # window keys in flight
            while len(inflight) < a.procs and (cands or longs):
                if cands:
                    _, job = cands.pop(0)
                    jid = job_id(job)
                    if jid in done or jid in inflight or jid[1] in busy:
                        continue
                    lng = False
                else:
                    job, lt = longs.pop(0)
                    jid = job_id(job)
                    if nlong >= a.procs - 1 or jid in done or jid in inflight or lt in st.long_tried:
                        continue
                    st.long_tried.add(lt); lng = True; nlong += 1
                inflight[jid] = (job, time.time(), lng); busy.add(jid[1])
                pool.apply_async(L4.work, (job,), callback=results.put,
                                 error_callback=lambda ex, j=job: results.put((j, {'error': repr(ex)})))
            try:
                job, r = results.get(timeout=2)
            except queue.Empty:
                job = None
            while job is not None:
                nres_since += handle(job, r)
                try:
                    job, r = results.get_nowait()
                except queue.Empty:
                    job = None
            if (nres_since and time.time() - t_regen > a.regen_s) or (not cands and not longs and nres_since):
                lam, cyc, nlive = st.evaluate()
                cands, longs, cinfo = candidates(st, lam, cyc, a, set(inflight) | done, {x[1] for x in inflight})
                log(f'  regen: lambda {lam} = {float(lam) / 120:.4f} len {len(cyc)} cands {len(cands)} '
                    f'long {len(longs)} inflight {len(inflight)} [{cinfo["cand_s"]}s] {stats}')
                t_regen = time.time(); nres_since = 0
            if not cands and not longs and not inflight and time.time() - t_regen > 60:
                lam, cyc, nlive = st.evaluate()
                cands, longs, cinfo = candidates(st, lam, cyc, a, set(inflight) | done, {x[1] for x in inflight})
                t_regen = time.time()
                if not cands and not longs:
                    log('  nothing to test for this worker; waiting for peers')
                    time.sleep(min(30, max(0, t_epoch - time.time())))
        epoch += 1
    # ---------------- exit: let running jobs finish within the grace period, then publish
    t_g = time.time() + a.grace
    while inflight and time.time() < t_g:
        try:
            handle(*results.get(timeout=2))
        except queue.Empty:
            pass
    pool.terminate(); pool.join()
    if inflight:
        log(f'{len(inflight)} jobs cut at exit')
    if stats:
        with open(rounds_p, 'a') as f:
            f.write(json.dumps(dict(time=time.strftime('%Y-%m-%d %H:%M:%S'), epoch=epoch, index=I, workers=W,
                                    final=True, tests=stats, n_tests=sum(stats.values()))) + '\n')
    if not a.no_sync:
        try:
            sync.remote = ls_remote()
            c = sync.publish(dict(index=I, workers=W, time=time.strftime('%Y-%m-%d %H:%M:%S'), final=True))
            log(f'final publish {c and c[:10]}')
        except Exception as e:  # noqa: BLE001
            log(f'final publish failed: {str(e)[:300]}')


# ------------------------------------------------------------------ other subcommands
def status(a):
    os.makedirs(FARM, exist_ok=True)
    if not a.no_sync:
        sy = Sync(None)
        n, stop = sy.pull()
        log(f'fetched {n} branches; stop flag {stop}')
    st = State()
    lam, cyc, nlive = st.evaluate()
    print(json.dumps(dict(lam=str(lam), mu=round(float(lam) / 120, 5), m_real=round(C.bound_real(float(lam), 1, 0, 0), 4),
                          cycle=len(cyc), live=nlive, need_231_alpha_at_R0=round(LAM231, 4))), flush=True)
    if not a.no_exact:
        import eval232
        ex = eval232.exact_best(st.G, lam)        # st.G: allowed transitions of the fresh build
        best = min(ex, key=lambda r: (r['bound'], -r['slack'])) if ex else None
        if best:
            print(json.dumps(dict(exact_bound=best['bound'], lam_t=f"{best['P']}/{best['Q']}", R=best['R'],
                                  need_231_alpha=round((125400 + best['R'] / best['Q']) / 225 / 120, 4))), flush=True)
    per = {}
    for kind in KINDS:
        for f in farm_files(kind):
            w = os.path.basename(f).split('_w')[1].split('.')[0]
            d = per.setdefault(w, {})
            d[kind] = max(d.get(kind, 0), len(read_lines(f)))   # own .jsonl and a fetched .gz copy
    for w in sorted(per, key=lambda x: int(x)):
        last = None
        for f in (own_path('rounds', w), own_path('rounds', w) + '.gz'):
            ls = [json.loads(l) for l in read_lines(f)]
            ls = [r for r in ls if 'lam' in r]
            if ls and (last is None or ls[-1]['time'] > last['time']):
                last = ls[-1]
        c = {k: per[w].get(k, 0) for k in KINDS}
        print(f'w{w}: {c}  last: ' + (json.dumps({k: last[k] for k in ('time', 'epoch', 'lam', 'mu', 'len', 'tests')
                                                    if k in last}) if last else '-'), flush=True)


def stop(a):
    rem = ls_remote()
    meta = dict(stop=not a.clear, time=time.strftime('%Y-%m-%d %H:%M:%S'))
    files = {'record.json': json.dumps(meta).encode()}
    if not a.clear:
        files['STOP'] = b'stop\n'
    c = push_tree('ctl', files, rem.get('ctl'), 'farm231 ' + ('clear' if a.clear else 'stop'))
    log(f'pushed {c[:10]} to xfer/231/ctl: stop={not a.clear}')
    if a.clear and os.path.exists(os.path.join(FARM, 'STOP')):
        os.remove(os.path.join(FARM, 'STOP'))


def merge(a):
    outs = {'plain': 'oracle_plain_r231.jsonl.gz', 'share': 'oracle_share_r231.jsonl.gz', 'ctx': 'ctxshare_r231.jsonl.gz'}
    for kind, name in outs.items():
        p = os.path.join(DATA, name)
        lines = set(read_lines(p))
        n0 = len(lines)
        for f in farm_files(kind):
            lines.update(read_lines(f))
        with gzip.open(p + '.tmp', 'wt', compresslevel=9) as f:
            for l in sorted(lines):
                f.write(l + '\n')
        os.replace(p + '.tmp', p)
        log(f'{name}: {len(lines)} records ({len(lines) - n0} new)')


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    sp = ap.add_subparsers(dest='cmd', required=True)
    r = sp.add_parser('run')
    r.add_argument('--index', type=int, required=True)
    r.add_argument('--workers', type=int, required=True)
    r.add_argument('--hours', type=float, required=True)
    r.add_argument('--procs', type=int, default=4)
    r.add_argument('--epoch-min', type=float, default=8)
    r.add_argument('--tl', type=float, default=60, help='plain tests (loop4: 60 s)')
    r.add_argument('--tl-thr', type=float, default=120, help='thresholds (loop4: 120 s)')
    r.add_argument('--tl-long', type=float, default=1800, help='long retries (loop4: 1800 s)')
    r.add_argument('--margin', type=float, default=12, help='need level = lambda + margin (weight units)')
    r.add_argument('--budget', type=int, default=0, help='owned candidates per regeneration (0: procs*epoch_min*60/8*3)')
    r.add_argument('--regen-s', type=float, default=60)
    r.add_argument('--grace', type=float, default=150)
    r.add_argument('--no-sync', action='store_true', help='no git transfer (local tests)')
    s = sp.add_parser('status')
    s.add_argument('--no-exact', action='store_true')
    s.add_argument('--no-sync', action='store_true')
    t = sp.add_parser('stop')
    t.add_argument('--clear', action='store_true')
    sp.add_parser('merge')
    a = ap.parse_args()
    if a.cmd == 'run':
        assert 0 <= a.index < a.workers
    {'run': run, 'status': status, 'stop': stop, 'merge': merge}[a.cmd](a)


if __name__ == '__main__':
    main()
