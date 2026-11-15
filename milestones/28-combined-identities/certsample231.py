#!/usr/bin/env python3
"""Measured LRAT sizes of a sample of the 231 certificate plan, on several machines (milestone 28,
"Certificate plan for 231").

For one record (kind, key, level) of `data/certsample231_list.jsonl.gz` this script builds the
certificate's CNF and its LRAT refutation with the toolchain of the unconditional 233
(milestones/33-233-lean/certify/cert233.py), and counts the hints:

  plain  key [dirs, lumped syms]: cert233.core_plain (gen_k7_core.encoding, radius 4, lazy cycle
         cuts by wincert.decide; CaDiCaL --lrat --no-binary --unsat on the full CNF, trimmed:
         `est_hints`), then the replay proof of the core as `cert233.py replay` makes it
         (gen_lean_core.core_lrat with the 7-configuration PORTFOLIO, seeds 1 and 2, 1 round:
         `hints`, the number the Lean replay module carries);
  5      key [dirs (6), lumped syms (5)], level L: cert233.core_share at cap L-1
         (share233.TaggedShare, M = 12, lazy cuts by share233.solve, the same CaDiCaL runs), the
         core renumbered by cert233.share_compact, then the replay proof of the compact core;
  c7/c8  key [canonical ctx dirs (7 or 8), 6 lumped counts of the last 6 centres], level L: the
         same with TaggedShareCtx below, i.e. share233.TaggedShare whose share totalizers cover only
         the TRAILING 5 centres (share7.SubShareEncoding's centre range); for c8 the first centre's
         count is free, bounds (1, 21).  No Lean bridge exists for these yet; the CNF has the clause
         kinds of TaggedShare, so the proof size is measured the same way.
  The level L is the level the plan needs (re-solved there, as the 233 production did); the source
  record (`source_T`, `seconds`) is the cheapest UNSAT solver call at a level >= L.

One JSON line per record goes to data/certsample231/res_w<I>.jsonl: kind, key, level, source_T,
seconds (solver seconds of the source record), status (UNSAT | SAT | TIMEOUT | FILE_LIMIT | ERROR),
solve_s, est_hints (trimmed full proof), hints (replay proof), lemmas, proof_bytes (the replay LRAT,
ids remapped as gen_lean_lrat_v3 reads it), full_s and replay_s (CaDiCaL + trim wall time),
wall_s, peak_rss_mb (max over the record's process and its CaDiCaL children), core_clauses,
variables, host, version.  Every record runs in its own child process with a wall-time limit
(--rec-hours); its work files are deleted right after it.

Distribution (the farm231.py approach): worker I of W processes the records with
int(sha1(key).hexdigest(), 16) % W == I; with --procs P, one lane takes the records in increasing
source seconds and P - 1 lanes in decreasing order (the slow tail first), so both ends are covered
when --hours runs out.  The result file is published to refs/heads/xfer/231s/w<I> (one commit with
res.jsonl.gz, parent = the previous tip: fast-forward only, never forced, never deleted) every
--publish-min minutes and at the end; at start the worker merges that branch's file into its local
file and skips the records already done.

  nice -n 10 python3 certsample231.py run --index I --workers W --hours H [--procs 4]
                     [--rec-hours 3] [--fsize-mb 6000] [--list data/certsample231_list.jsonl.gz]
  python3 certsample231.py status [--merge]   # all xfer/231s/w* branches; --merge writes
                                              # data/certsample231_results.jsonl.gz
  python3 certsample231.py one '<json record>'   # one record, result on stdout (no file, no git)

Dependencies (a fresh 4-core / 15 GB container; verified from a fresh sparse clone):
  * python3 (>= 3.9), git, a C++ compiler and make (to build CaDiCaL);
  * pip packages: numpy, python-sat (`pysat.solvers.Cadical153` is used for the lazy-cut solves,
    exactly as in the 233 pipeline; no other pip package);
  * CaDiCaL 2.1.3, the binary of the 233 production (it ships in the Lean 4.19.0 toolchain's bin/;
    the source build is the same version):
        git clone --depth 1 --branch rel-2.1.3 https://github.com/arminbiere/cadical ~/cadical-2.1.3
        (cd ~/cadical-2.1.3 && ./configure && make -j4)        # -> ~/cadical-2.1.3/build/cadical
    The binary is found as $CADICAL, else the Lean toolchain's, else ~/cadical-2.1.3/build/cadical,
    else `cadical` on PATH.  No drat-trim, cake_lpr or Lean is needed: trimming is
    gen_lean_core.trim_lrat (Python).
  * the repository paths (sparse checkout, about 10 MB):
        git clone --depth 1 --filter=blob:none --sparse -b research/unconditional-241 \\
            https://github.com/hironaka-iori/Snake-in-the-box-in-9 snake && cd snake
        git sparse-checkout set --no-cone /milestones/28-combined-identities/certsample231.py \\
            /milestones/28-combined-identities/data/certsample231_list.jsonl.gz \\
            /milestones/33-233-lean/certify/ /milestones/10-window-aggregate/scripts/ \\
            /milestones/25-k7-234/certify/
        pip install numpy python-sat
        cd milestones/28-combined-identities
        nice -n 10 python3 certsample231.py run --index I --workers W --hours H
  Environment: FARM_URL (git URL, default the GitHub URL), FARM_SCR (temporary bare repositories,
  default ~/.farm231), CERTS_WORK (work directory, default ~/certsample231-work).
"""
import argparse, gzip, hashlib, itertools, json, os, resource, shutil, signal, socket, subprocess, sys
import tempfile, threading, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
MS = os.path.join(ROOT, 'milestones')
LIST = os.path.join(HERE, 'data', 'certsample231_list.jsonl.gz')
OUTD = os.path.join(HERE, 'data', 'certsample231')
URL = os.environ.get('FARM_URL', 'https://github.com/hironaka-iori/Snake-in-the-box-in-9')
PFX = 'refs/heads/xfer/231s/'
SCR = os.environ.get('FARM_SCR', os.path.join(os.path.expanduser('~'), '.farm231'))
WORK = os.environ.get('CERTS_WORK', os.path.join(os.path.expanduser('~'), 'certsample231-work'))
VERSION = 1


def log(*a):
    print(time.strftime('%H:%M:%S'), *a, flush=True)


def find_cadical():
    for p in (os.environ.get('CADICAL'), '/home/user/lean-deps/toolchain/lean-4.19.0-linux/bin/cadical',
              os.path.join(os.path.expanduser('~'), 'cadical-2.1.3', 'build', 'cadical'), shutil.which('cadical')):
        if p and os.path.exists(p):
            return p
    raise SystemExit('no CaDiCaL binary: set CADICAL (see the docstring)')


def rkey(r):
    return json.dumps([r['kind'], r['key'], r.get('level')], separators=(',', ':'))


def owner(r, W):
    return int(hashlib.sha1(json.dumps(r['key'], separators=(',', ':')).encode()).hexdigest(), 16) % W


# ------------------------------------------------------------------ one record (child process)
def _imports():
    for p in (os.path.join(MS, '10-window-aggregate', 'scripts'), os.path.join(MS, '25-k7-234', 'certify'),
              os.path.join(MS, '33-233-lean', 'certify')):
        if p not in sys.path:
            sys.path.insert(0, p)
    import cert233
    return cert233


def ctx_share_class(share233):
    import itertools as it

    class TaggedShareCtx(share233.TaggedShare):
        """share233.TaggedShare with the share totalizers over the centre indices `share_ci` only (the
        clauses and tags of every other part unchanged; the cap totalizer runs over these centres)."""
        def __init__(self, dirs, bounds, cap, share_ci, M=12):
            from gen_lean_sat import TaggedEncoding
            from wincert import window_from_dirs
            self.window = window_from_dirs(list(dirs)); self.bounds = [tuple(b) for b in bounds]
            self.cap = cap; self.M = M
            alpha = [b[0] if b[0] == b[1] else tuple(b) for b in self.bounds]
            base = TaggedEncoding(self.window, alpha, radius=4)
            self.nv = base.nv; self.meaning = base.meaning; self.smeaning = {}; self.ctrs = base.ctrs
            self.clauses = base.clauses; self.tags = [('old', t) for t in base.tags]; self.var = base.var
            self.ball = base.ball
            self.tots = []; spec = []; ulits = []
            for ci, c in enumerate(self.window[1:-1], 1):
                if ci not in share_ci:
                    continue
                used = {(c ^ self.window[ci - 1]).bit_length() - 1, (c ^ self.window[ci + 1]).bit_length() - 1}
                cs = []
                for kk in range(9):
                    if kk in used:
                        continue
                    q = c ^ (1 << kk); es = []
                    for a, b in it.combinations(range(9), 2):
                        if kk in (a, b):
                            continue
                        e = self.fresh(('sq', q, a, b)); es.append(e)
                        self.add([self.var[v] for v in (q, q ^ (1 << a), q ^ (1 << b), q ^ (1 << a) ^ (1 << b))] + [e],
                                 ('emptyE',))
                    et, ge = self.totalizer(es, ('emp', q), up=True)
                    dt, gd = self.totalizer([self.var[q ^ (1 << a)] for a in range(9)], ('nb', q), up=False, down=True)
                    tmax = min(cap + 1, M * len(es)); cs.append((kk, tmax))
                    for t in range(1, tmax + 1):
                        u = self.fresh(('u', q, t)); ulits.append(u)
                        for d in range(1, 10):
                            need = (t * d + M - 1) // M
                            if need > len(es):
                                continue
                            clause = [u, -ge[need]]
                            if d < 9:
                                clause.append(gd[d + 1])
                            self.add(clause, ('shareCl', et, dt))
                spec.append(cs)
            ti, out = self.totalizer(ulits, ('cap', spec), up=True, limit=cap + 1)
            self.add([-out[cap + 1]], ('shareCap', ti))
            self.nbase = len(self.clauses)
    return TaggedShareCtx


def ctx_enc(cert233, kind, dirs, t, level):
    TSC = ctx_share_class(cert233.share233)
    bounds = cert233.GC.dir_bounds(t)
    if kind == 'c8':
        bounds = [(1, 21)] + bounds
    nwin = len(dirs) + 1
    k = nwin - 2                                   # last centre index
    return TSC(list(dirs), bounds, level - 1, set(range(k - 4, k + 1)), M=12)


def cadical_wrapper(work, cad, fsize_mb):
    p = os.path.join(work, 'cadical_lim.sh')
    open(p, 'w').write(f'#!/bin/bash\nulimit -f {fsize_mb * 1024}\nexec {cad} "$@"\n')
    os.chmod(p, 0o755)
    return p


def prove(r, work, fsize_mb, tl):
    """Proof of one record; returns the result fields (raises on error)."""
    cert233 = _imports()
    GC, K = cert233.GC, cert233.K
    certs = os.path.join(work, 'certs'); os.makedirs(certs, exist_ok=True)
    cad = cadical_wrapper(work, find_cadical(), fsize_mb)
    kind = r['kind']
    out = {}
    t0 = time.time()
    if kind == 'plain':
        k = (tuple(r['key'][0]), tuple(r['key'][1]))
        meta = cert233.core_plain(k, work, certs, cad)
        out.update(solve_s=meta['secs']['decide'], full_s=meta['secs']['core'])
        gz = cert233.regen_plain(meta, certs)
    else:
        if kind == '5':
            enc = cert233.share_enc((tuple(r['key'][0]), tuple(r['key'][1]), r['level'] - 1))
        else:
            enc = ctx_enc(cert233, kind, r['key'][0], r['key'][1], r['level'])
        name = 'X' + hashlib.sha1(rkey(r).encode()).hexdigest()[:16]
        npre = len(enc.clauses)
        st, cuts, sec = cert233.share233.solve(enc, tl)
        out['solve_s'] = round(sec, 2)
        if st != 'UNSAT':
            out['status'] = st
            return out
        gz = os.path.join(certs, name + '.cnf.gz')
        cert233.write_cnf_gz(enc.nv, enc.clauses, gz)
        t1 = time.time()
        cnf = GC.extract_cnf(name, work, certs)
        nl, nh, desc, ids = GC.best_cadical_proof(cnf, os.path.join(work, name + '.full'), cad, [1],
                                                  portfolio=[['--unsat']], rounds=1)
        os.remove(os.path.join(work, name + '.full.lrat'))
        for p in (gz, cnf):
            if os.path.exists(p):
                os.remove(p)
        out['full_s'] = round(time.time() - t1, 2)
        ren, core, tags, used_c = cert233.share_compact(enc, ids)
        rl = lambda x: (1 if x > 0 else -1) * ren[abs(x)]          # noqa: E731
        gz = os.path.join(certs, name + '.cnf.gz')
        cert233.write_cnf_gz(len(ren), [[rl(x) for x in c] for c in core], gz)
        meta = dict(name=name, variables=len(ren), core_ids=list(range(1, len(ids) + 1)),
                    lrat=dict(lemmas=nl, hints=nh), full_clauses=len(enc.clauses), cuts=len(cuts), base=npre)
    out.update(est_hints=meta['lrat']['hints'], est_lemmas=meta['lrat'].get('lemmas'),
               core_clauses=len(meta['core_ids']), variables=meta['variables'])
    t2 = time.time()
    lrat, info = GC.core_lrat(meta['name'], meta['core_ids'], work, cad, [1, 2], certs, rounds=1)
    out.update(status='UNSAT', hints=info['hints'], lemmas=info.get('lemmas'), proof_bytes=os.path.getsize(lrat),
               replay_s=round(time.time() - t2, 2), producer=info['producer'])
    out['prove_s'] = round(time.time() - t0, 2)
    return out


def one(rec_json, fsize_mb=6000, tl=36000.0, work=None):
    r = json.loads(rec_json)
    work = work or tempfile.mkdtemp(prefix='certsample231_')
    os.makedirs(work, exist_ok=True)
    try:
        try:
            out = prove(r, work, fsize_mb, tl)
        except AssertionError as e:
            msg = str(e)
            out = dict(status='FILE_LIMIT' if ('UNSATISFIABLE' in msg or 'File size' in msg) else 'ERROR',
                       error=msg[-400:])
        except Exception as e:                       # noqa: BLE001
            out = dict(status='ERROR', error=repr(e)[-400:])
    finally:
        shutil.rmtree(work, ignore_errors=True)
    rs = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    rc = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    out['peak_rss_mb'] = round(max(rs, rc) / 1024, 1)
    out['rss_self_mb'] = round(rs / 1024, 1)
    return out


# ------------------------------------------------------------------ git transfer (farm231.py's approach)
def git(*args, cwd=None, inp=None, timeout=300):
    r = subprocess.run(['git', *args], cwd=cwd or HERE, capture_output=True, text=True, input=inp, timeout=timeout)
    if r.returncode != 0:
        raise RuntimeError(f'git {args[0]} failed: {r.stderr[-400:]}')
    return r.stdout


def gitb(*args, cwd=None, inp=None):
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
    b = tempfile.mkdtemp(dir=SCR, prefix='s')
    git('init', '-q', '--bare', b, cwd=SCR)
    return b


def ls_remote():
    out = retry(lambda: git('ls-remote', URL, PFX + '*', timeout=120))
    return {l.split('\t')[1][len(PFX):]: l.split('\t')[0] for l in out.splitlines() if '\t' in l}


def fetch_trees(names):
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
    """One commit with `files` and `parent`, pushed to xfer/231s/<name> (fast-forward only)."""
    b = bare()
    try:
        if parent:
            retry(lambda: git('fetch', '-q', '--depth', '1', URL, f'{PFX}{name}:refs/x/p', cwd=b, timeout=600))
        entries = []
        for path, data in sorted(files.items()):
            sha = gitb('hash-object', '-w', '--stdin', cwd=b, inp=data).decode().strip()
            entries.append(f'100644 blob {sha}\t{path}')
        tree = git('mktree', cwd=b, inp='\n'.join(entries) + '\n').strip()
        cmd = ['-c', 'user.name=certsample231', '-c', 'user.email=certsample231@localhost', 'commit-tree', tree, '-m', msg]
        if parent:
            cmd[-2:-2] = ['-p', parent]
        commit = git(*cmd, cwd=b).strip()
        retry(lambda: git('push', '-q', URL, f'{commit}:{PFX}{name}', cwd=b, timeout=600))
        return commit
    finally:
        shutil.rmtree(b, ignore_errors=True)


def read_lines(path):
    if not os.path.exists(path):
        return []
    out = []
    for l in open(path, 'rb').read().decode('utf-8', 'replace').split('\n'):
        l = l.strip()
        if l:
            try:
                json.loads(l); out.append(l)
            except ValueError:
                pass
    return out


def publish(I, path, state):
    lines = read_lines(path)
    if not lines or len(lines) == state.get('published', -1):
        return
    me = f'w{I}'
    tip = ls_remote().get(me)
    data = gzip.compress(('\n'.join(lines) + '\n').encode(), 9, mtime=0)
    rec = json.dumps(dict(index=I, records=len(lines), time=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
                          host=socket.gethostname(), version=VERSION)).encode()
    try:
        push_tree(me, {'res.jsonl.gz': data, 'record.json': rec}, tip, f'certsample231 w{I}: {len(lines)} records')
        state['published'] = len(lines)
        log(f'published {len(lines)} records to xfer/231s/{me}')
    except (RuntimeError, subprocess.TimeoutExpired) as e:
        log(f'publish failed (will retry): {str(e)[:200]}')


# ------------------------------------------------------------------ run / status
def load_list(path):
    return [json.loads(l) for l in gzip.open(path, 'rt') if l.strip()]


def sort_x(r):
    return r['model_hints'] if r['kind'] == 'plain' else (r.get('seconds') or 0.0)


def run(a):
    os.makedirs(OUTD, exist_ok=True); os.makedirs(WORK, exist_ok=True)
    gi = os.path.join(OUTD, '.gitignore')
    if not os.path.exists(gi):
        open(gi, 'w').write('# worker files of certsample231.py (published on xfer/231s/*)\n*\n!.gitignore\n')
    path = os.path.join(OUTD, f'res_w{a.index}.jsonl')
    try:                                             # restart: merge our branch's file first
        tr = fetch_trees([f'w{a.index}']) if f'w{a.index}' in ls_remote() else {}
        rl = tr.get(f'w{a.index}', {}).get('res.jsonl.gz')
        if rl:
            have = set(read_lines(path))
            new = [l for l in gzip.decompress(rl).decode().split('\n') if l.strip() and l not in have]
            if new:
                with open(path, 'a') as f:
                    f.write('\n'.join(new) + '\n')
                log(f'merged {len(new)} records from xfer/231s/w{a.index}')
    except (RuntimeError, subprocess.TimeoutExpired) as e:
        log(f'restore failed: {str(e)[:200]}')
    done = {rkey(json.loads(l)) for l in read_lines(path)}
    recs = [r for r in load_list(a.list) if owner(r, a.workers) == a.index and rkey(r) not in done]
    log(f'worker {a.index}/{a.workers}: {len(recs)} records to do ({len(done)} done)')
    up = sorted(recs, key=lambda r: (sort_x(r), rkey(r)))
    down = list(reversed(up))
    taken = set(); lock = threading.Lock()
    t_end = time.time() + a.hours * 3600
    state = {}

    def next_rec(lane):
        with lock:
            src = up if lane == 0 else down
            while src:
                r = src.pop(0)
                if rkey(r) not in taken:
                    taken.add(rkey(r)); return r
        return None

    def worker(lane):
        while time.time() < t_end and not os.path.exists(os.path.join(OUTD, 'STOP')):
            if shutil.disk_usage(WORK).free < a.min_disk_mb * 2 ** 20:
                log('disk low: lane waits'); time.sleep(60); continue
            r = next_rec(lane)
            if r is None:
                return
            left = t_end - time.time()
            lim = min(a.rec_hours * 3600, max(60.0, left))
            t0 = time.time()
            wd = os.path.join(WORK, f'w{a.index}_lane{lane}')
            shutil.rmtree(wd, ignore_errors=True); os.makedirs(wd)
            p = subprocess.Popen(['nice', '-n', '10', sys.executable, os.path.abspath(__file__), 'one', json.dumps(r),
                                  '--fsize-mb', str(a.fsize_mb), '--work', wd], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                 text=True, start_new_session=True)
            try:
                so, se = p.communicate(timeout=lim)
                try:
                    out = json.loads(so.strip().splitlines()[-1])
                except (ValueError, IndexError):
                    out = dict(status='ERROR', error=(se or so)[-400:])
            except subprocess.TimeoutExpired:
                os.killpg(p.pid, signal.SIGKILL)       # our own child's process group
                p.communicate()
                out = dict(status='TIMEOUT', limit_s=round(lim))
            shutil.rmtree(wd, ignore_errors=True)
            res = dict(kind=r['kind'], key=r['key'], level=r.get('level'), source_T=r.get('source_T'),
                       seconds=r.get('seconds'), model_hints=r.get('model_hints'), stratum=r.get('stratum'),
                       **out, wall_s=round(time.time() - t0, 1), host=socket.gethostname(), worker=a.index,
                       version=VERSION)
            with lock:
                with open(path, 'a') as f:
                    f.write(json.dumps(res) + '\n')
            log(f"lane {lane}: {r['kind']} {r['key']} L={r.get('level')} src {r.get('seconds')}s -> "
                f"{res.get('status')} hints {res.get('hints')} est {res.get('est_hints')} {res['wall_s']}s "
                f"rss {res.get('peak_rss_mb')} MB")

    ths = [threading.Thread(target=worker, args=(i,), daemon=True) for i in range(a.procs)]
    for t in ths:
        t.start()
    last = time.time()
    while any(t.is_alive() for t in ths):
        time.sleep(5)
        if time.time() - last > a.publish_min * 60:
            publish(a.index, path, state); last = time.time()
    publish(a.index, path, state)
    log('done')


def status(a):
    tips = ls_remote()
    names = sorted(n for n in tips if n.startswith('w'))
    trees = fetch_trees(names)
    rows = []
    for n in names:
        raw = trees.get(n, {}).get('res.jsonl.gz')
        if raw:
            rows += [json.loads(l) for l in gzip.decompress(raw).decode().split('\n') if l.strip()]
    local = []
    for f in sorted(os.listdir(OUTD)) if os.path.isdir(OUTD) else []:
        if f.startswith('res_w') and f.endswith('.jsonl'):
            local += [json.loads(l) for l in read_lines(os.path.join(OUTD, f))]
    seen = {}
    for r in rows + local:
        seen[rkey(r)] = r
    rows = list(seen.values())
    print(f'{len(names)} branches, {len(rows)} distinct records')
    by = {}
    for r in rows:
        b = by.setdefault((r['kind'], r.get('status')), [0, 0, 0.0])
        b[0] += 1; b[1] += r.get('hints') or 0; b[2] += r.get('wall_s') or 0
    for (k, s), (n, h, w) in sorted(by.items(), key=lambda x: (x[0][0], str(x[0][1]))):
        print(f'  {k:6s} {str(s):10s} {n:5d} records, {h / 1e6:10.1f} M hints, {w / 3600:7.2f} h wall')
    if a.merge:
        out = os.path.join(HERE, 'data', 'certsample231_results.jsonl.gz')
        with gzip.GzipFile(out, 'wb', mtime=0) as g:
            g.write(''.join(json.dumps(r, sort_keys=True) + '\n' for r in sorted(rows, key=rkey)).encode())
        print('wrote', out)


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest='cmd', required=True)
    p = sp.add_parser('run')
    p.add_argument('--index', type=int, required=True); p.add_argument('--workers', type=int, required=True)
    p.add_argument('--hours', type=float, required=True); p.add_argument('--procs', type=int, default=4)
    p.add_argument('--rec-hours', type=float, default=3.0); p.add_argument('--fsize-mb', type=int, default=6000)
    p.add_argument('--min-disk-mb', type=int, default=3000); p.add_argument('--publish-min', type=float, default=10)
    p.add_argument('--list', default=LIST)
    p = sp.add_parser('status'); p.add_argument('--merge', action='store_true')
    p = sp.add_parser('one'); p.add_argument('rec'); p.add_argument('--fsize-mb', type=int, default=6000)
    p.add_argument('--work')
    a = ap.parse_args()
    if a.cmd == 'one':
        print(json.dumps(one(a.rec, a.fsize_mb, work=a.work)), flush=True)
    elif a.cmd == 'run':
        run(a)
    else:
        status(a)


if __name__ == '__main__':
    main()
