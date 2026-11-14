#!/usr/bin/env python3
"""Generate replay sources of the 233 certificates on other machines (cloud sessions) and hand them to
the production machine through short-lived git branches.

Generation (cadical 8 seeds x 5 rounds, trimming, `gen_lean_lrat_v3.py`) is about half of the
remaining cost; the production machine has 4 cores shared by generation and the Lean kernel.  The
sources are deterministic (`cert233.py replay` docstring), and every one is checked again by the Lean
kernel when the production machine builds it, so a source made elsewhere needs no trust.

  gen  (remote machine): for each name in --names (in order), unless branch xfer/233/<name> exists:
       `cert233.py replay` into a scratch directory, gzip -9 the source, split it into parts under
       45 MiB (GitHub's limit is 100 MB), and push one orphan commit holding the parts and the replay
       record (record.json) to refs/heads/xfer/233/<name>.  The cadical binary comes from branch
       xfer/233/cadical (the Lean 4.19.0 toolchain's) when it is not installed.
  pull (production machine, a daemon): every --every seconds, for the xfer/233/<name> branches whose
       certificate has neither source nor .olean in work/final_lean, lowest prod order first, while
       free disk stays above --min-disk-mb plus the source size: fetch that single branch into a
       throwaway bare repository, write the source atomically into work/final_lean/LocalWindowUnsat
       (where prod233.py and pregen233.py look for it), append record.json to data/replay6SB233.jsonl,
       try to delete the remote branch (this session's proxy refuses that; consumed names are kept in
       $CERT233_SCR/xfer_consumed), delete the bare repository.  At most --ahead unbuilt sources are kept.
       A claim file in $CERT233_SCR/pregen_claims is written for every name that has a branch, so
       pregen233.py workers leave those names alone.

  python3 xfer233.py gen --names A B C ...            (CERT233_SCR: scratch directory)
  python3 xfer233.py pull [--every 300] [--ahead 14]
"""
import argparse, gzip, json, os, shutil, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
LEAN = os.path.join(ROOT, 'work', 'final_lean')
DATA = os.path.join(HERE, 'data')
URL = 'https://github.com/hironaka-iori/Snake-in-the-box-in-9'
PFX = 'refs/heads/xfer/233/'
CADICAL = '/home/user/lean-deps/toolchain/lean-4.19.0-linux/bin/cadical'
PART = 45 << 20


def log(**r):
    print(json.dumps({'t': round(time.time()), **r}), flush=True)


def git(*args, cwd=ROOT, check=True, inp=None):
    r = subprocess.run(['git', *args], cwd=cwd, capture_output=True, text=True, input=inp)
    if check and r.returncode != 0:
        raise RuntimeError(f'git {args[0]} failed: {r.stderr[-500:]}')
    return r.stdout


def retry(f, n=5):
    for i in range(n):
        try:
            return f()
        except RuntimeError as e:
            if i == n - 1:
                raise
            log(retry=str(e)[:200])
            time.sleep(5 * 2 ** i)


def remote_names():
    out = retry(lambda: git('ls-remote', URL, PFX + '*'))
    return {line.split('\t')[1][len(PFX):]: line.split('\t')[0] for line in out.splitlines() if '\t' in line}


def bare(tmp):
    git('init', '-q', '--bare', tmp)
    return tmp


def ensure_cadical(scr):
    if os.path.exists(CADICAL):
        return
    b = bare(os.path.join(scr, 'cad.git'))
    retry(lambda: git('fetch', '-q', URL, PFX + 'cadical:refs/x/c', cwd=b))
    os.makedirs(os.path.dirname(CADICAL), exist_ok=True)
    data = subprocess.run(['git', 'cat-file', 'blob', 'refs/x/c:cadical'], cwd=b, capture_output=True).stdout
    open(CADICAL, 'wb').write(data)
    os.chmod(CADICAL, 0o755)
    shutil.rmtree(b)
    log(cadical='installed', bytes=len(data))


def gen(a):
    scr = os.environ.setdefault('CERT233_SCR', os.path.join(os.path.expanduser('~'), 'xfer233scr'))
    os.makedirs(scr, exist_ok=True)
    ensure_cadical(scr)
    out = os.path.join(scr, 'out')
    for name in a.names:
        if name in remote_names():
            log(name=name, skip='branch exists')
            continue
        t0 = time.time()
        r = subprocess.run([sys.executable, os.path.join(HERE, 'cert233.py'), 'replay', '--kinds', 'seed,share',
                            '--min-disk-mb', str(a.min_disk_mb), '--seed-jobs', a.seed_jobs, '--cores', str(a.cores),
                            '--out', out, name], capture_output=True, text=True)
        src = os.path.join(out, 'LocalWindowUnsat', name + '.lean')
        if r.returncode != 0 or not os.path.exists(src):
            log(name=name, failed=r.returncode, stderr=r.stderr[-1500:])
            continue
        rec = [json.loads(line) for line in r.stdout.splitlines() if line.startswith('{"case"')]
        gen_s = round(time.time() - t0)
        b = bare(tempfile.mkdtemp(dir=scr, prefix='push'))
        raw = open(src, 'rb').read()
        z = gzip.compress(raw, 9)
        entries = []
        for i in range(0, len(z), PART):
            p = os.path.join(b, 'part')
            open(p, 'wb').write(z[i:i + PART])
            sha = git('hash-object', '-w', p, cwd=b).strip()
            entries.append(f'100644 blob {sha}\tpart{i // PART:02d}')
        meta = {'name': name, 'bytes': len(raw), 'gz_bytes': len(z), 'parts': len(entries), 'gen_s': gen_s,
                'records': rec}
        p = os.path.join(b, 'part')
        open(p, 'w').write(json.dumps(meta))
        sha = git('hash-object', '-w', p, cwd=b).strip()
        entries.append(f'100644 blob {sha}\trecord.json')
        tree = git('mktree', cwd=b, inp='\n'.join(entries) + '\n').strip()
        commit = subprocess.run(['git', '-c', 'user.name=xfer233', '-c', 'user.email=xfer233@localhost',
                                 'commit-tree', tree, '-m', f'xfer 233 source {name}'], cwd=b, capture_output=True,
                                text=True, check=True).stdout.strip()
        retry(lambda: git('push', '-q', URL, f'{commit}:{PFX}{name}', cwd=b))
        shutil.rmtree(b)
        os.remove(src)
        log(name=name, pushed=commit, gen_s=gen_s, bytes=len(raw), gz=len(z))


def disk_free_mb():
    st = os.statvfs(LEAN)
    return st.f_bavail * st.f_frsize // (1 << 20)


def pull(a):
    scr = os.environ.get('CERT233_SCR', '/home/user/cert233work')
    claims = os.path.join(scr, 'pregen_claims')
    os.makedirs(claims, exist_ok=True)
    sys.path.insert(0, HERE)
    import cert233 as C
    ns = C.argparse.Namespace(keys_from='', plan=C.PLAN, core=C.CORE, names=[])
    olean = lambda n: os.path.exists(os.path.join(LEAN, '.lake/build/lib/lean/LocalWindowUnsat', n + '.olean'))  # noqa
    src = lambda n: os.path.join(LEAN, 'LocalWindowUnsat', n + '.lean')  # noqa
    done_p = os.path.join(scr, 'xfer_consumed')
    done = set(open(done_p).read().split()) if os.path.exists(done_p) else set()

    def consume(n):
        # The session's git proxy refuses branch deletion (HTTP 403), so deletion is best effort and the
        # consumed names are remembered locally; leftover xfer/233/* branches are removed at the end.
        done.add(n)
        with open(done_p, 'a') as f:
            f.write(n + '\n')
        r = subprocess.run(['git', 'push', '-q', 'origin', '--delete', PFX + n], cwd=ROOT, capture_output=True)
        log(name=n, consumed=True, branch_deleted=r.returncode == 0)

    while True:
        order = [it[2] for h, it, m in C.work_items(ns, {'seed', 'share'})]
        left = [n for n in order if not olean(n)]
        if not left:
            log(done='all built')
            return
        try:
            have = remote_names()
        except RuntimeError as e:
            log(error=str(e)[:300])
            time.sleep(a.every)
            continue
        for n in have:
            if n != 'cadical':
                try:
                    os.close(os.open(os.path.join(claims, n), os.O_CREAT | os.O_EXCL | os.O_WRONLY))
                except FileExistsError:
                    pass
        for n in [n for n in order if n in have and n not in done and (olean(n) or os.path.exists(src(n)))]:
            # built or already materialized (prod or pregen got there first): the branch is no longer needed
            consume(n)
        ready = sum(1 for n in left if os.path.exists(src(n)))
        rb = os.path.join(scr, 'remote_build')   # built elsewhere: their .olean files come through opull
        skip = set(open(rb).read().split()) if os.path.exists(rb) else set()
        for n in [n for n in left if n in have and n not in done and n not in skip and not os.path.exists(src(n))]:
            if ready >= a.ahead:
                break
            b = bare(tempfile.mkdtemp(dir=scr, prefix='pull'))
            try:
                retry(lambda: git('fetch', '-q', URL, f'{PFX}{n}:refs/x/s', cwd=b))
                meta = json.loads(subprocess.run(['git', 'cat-file', 'blob', 'refs/x/s:record.json'], cwd=b,
                                                 capture_output=True, check=True).stdout)
                if disk_free_mb() < a.min_disk_mb + (meta['bytes'] >> 20):
                    log(wait='disk', free_mb=disk_free_mb(), need_mb=meta['bytes'] >> 20)
                    break
                z = b''.join(subprocess.run(['git', 'cat-file', 'blob', f'refs/x/s:part{i:02d}'], cwd=b,
                                            capture_output=True, check=True).stdout for i in range(meta['parts']))
                raw = gzip.decompress(z)
                assert len(raw) == meta['bytes'], 'size mismatch'
                if olean(n) or os.path.exists(src(n)):
                    log(name=n, dropped='appeared meanwhile')
                else:
                    tmp = src(n) + '.xfer'
                    open(tmp, 'wb').write(raw)
                    os.replace(tmp, src(n))
                    with open(os.path.join(DATA, 'replay6SB233.jsonl'), 'a') as f:
                        for rec in meta['records']:
                            f.write(json.dumps({**rec, 'generated_on': 'remote'}) + '\n')
                    ready += 1
                    log(name=n, materialized=len(raw), gen_s=meta['gen_s'])
                consume(n)
            except (RuntimeError, subprocess.CalledProcessError, AssertionError, OSError) as e:
                log(name=n, error=str(e)[:300])
            finally:
                shutil.rmtree(b, ignore_errors=True)
        time.sleep(a.every)


OPFX = 'refs/heads/xfer/233o/'
LIB = os.path.join(LEAN, '.lake', 'build', 'lib', 'lean')
GLB = os.path.join(ROOT, 'work', 'guarded_lake_build.py')
LEANBIN = os.path.dirname(CADICAL)
LEAN_COMMIT = '6caaee842e94'   # `lean --version` of the production machine (Lean 4.19.0)


def ls_branches(pfx):
    out = retry(lambda: git('ls-remote', URL, pfx + '*'))
    return {line.split('\t')[1][len(pfx):] for line in out.splitlines() if '\t' in line}


def fetch_blobs(ref, b):
    """Fetch the single branch `ref` into the bare repository `b`; return (record, parts reader)."""
    retry(lambda: git('fetch', '-q', URL, f'{ref}:refs/x/s', cwd=b))
    blob = lambda p: subprocess.run(['git', 'cat-file', 'blob', f'refs/x/s:{p}'], cwd=b,  # noqa
                                    capture_output=True, check=True).stdout
    return json.loads(blob('record.json')), blob


def push_blobs(ref, files, meta, scr, msg):
    """One orphan commit holding gzip -9 parts (< 45 MiB) of each file and record.json."""
    b = bare(tempfile.mkdtemp(dir=scr, prefix='push'))
    entries, p = [], os.path.join(b, 'part')
    for k, data in enumerate(files):
        z = gzip.compress(data, 9)
        meta['files'][k]['parts'] = 0
        for i in range(0, len(z), PART):
            open(p, 'wb').write(z[i:i + PART])
            sha = git('hash-object', '-w', p, cwd=b).strip()
            entries.append(f'100644 blob {sha}\tf{k}part{i // PART:02d}')
            meta['files'][k]['parts'] += 1
    open(p, 'w').write(json.dumps(meta))
    sha = git('hash-object', '-w', p, cwd=b).strip()
    entries.append(f'100644 blob {sha}\trecord.json')
    tree = git('mktree', cwd=b, inp='\n'.join(entries) + '\n').strip()
    commit = subprocess.run(['git', '-c', 'user.name=xfer233', '-c', 'user.email=xfer233@localhost', 'commit-tree',
                             tree, '-m', msg], cwd=b, capture_output=True, text=True, check=True).stdout.strip()
    retry(lambda: git('push', '-q', URL, f'{commit}:{ref}', cwd=b))
    shutil.rmtree(b)
    return commit


def build(a):
    """Remote machine: build LocalWindowCnf.<n> and LocalWindowUnsat.<n> for --names with the production
    machine's exact command (guarded_lake_build --direct, Lean 4.19.0 commit LEAN_COMMIT), push both
    .olean files of each built certificate to xfer/233o/<n>.  Sources come from xfer/233/<n> (replay)
    and `cert233.py cnf` (core).  Modules that fail are retried once with --jobs 1."""
    import hashlib
    scr = os.environ.setdefault('CERT233_SCR', os.path.join(os.path.expanduser('~'), 'xfer233scr'))
    os.makedirs(scr, exist_ok=True)
    ver = subprocess.run([os.path.join(LEANBIN, 'lean'), '--version'], capture_output=True, text=True).stdout
    if LEAN_COMMIT not in ver:
        raise SystemExit(f'need Lean 4.19.0 commit {LEAN_COMMIT} in {LEANBIN}, found: {ver.strip()}')
    done = ls_branches(OPFX)
    todo = [n for n in a.names if n not in done]
    for n in todo:
        s = os.path.join(LEAN, 'LocalWindowUnsat', n + '.lean')
        if os.path.exists(s):
            continue
        b = bare(tempfile.mkdtemp(dir=scr, prefix='src'))
        meta, blob = fetch_blobs(PFX + n, b)
        raw = gzip.decompress(b''.join(blob(f'part{i:02d}') for i in range(meta['parts'])))
        assert len(raw) == meta['bytes'], 'size mismatch'
        open(s + '.xfer', 'wb').write(raw)
        os.replace(s + '.xfer', s)
        shutil.rmtree(b)
        log(name=n, source=len(raw))
    env = dict(os.environ, PATH=LEANBIN + ':' + os.environ['PATH'])
    if todo:
        r = subprocess.run([sys.executable, os.path.join(HERE, 'cert233.py'), 'cnf', '--kinds', 'seed,share', *todo],
                           env=env, capture_output=True, text=True)
        if r.returncode:
            raise SystemExit('cnf failed: ' + r.stderr[-1500:])
    glog = os.path.join(scr, 'guarded_remote.jsonl')
    pushed = set()

    def push_ready():
        st = {}
        if os.path.exists(glog):
            for line in open(glog):
                try:
                    r = json.loads(line)
                except ValueError:
                    continue
                if 'module' in r:
                    st[r['module']] = r
        for n in todo:
            r = st.get('LocalWindowUnsat.' + n)
            if n in pushed or not r or r['status'] != 'ok':
                continue
            paths = [os.path.join(LIB, d, n + '.olean') for d in ('LocalWindowCnf', 'LocalWindowUnsat')]
            data = [open(p, 'rb').read() for p in paths]
            meta = {'name': n, 'lean_version': ver.strip(), 'seconds': r['seconds'], 'peak_rss_gb': r['peak_rss_gb'],
                    'jobs': r.get('jobs'), 'host_cpus': os.cpu_count(),
                    'files': [{'path': os.path.relpath(p, LIB), 'bytes': len(d), 'sha256': hashlib.sha256(d).hexdigest()}
                              for p, d in zip(paths, data)]}
            commit = push_blobs(OPFX + n, data, meta, scr, f'xfer 233 olean {n}')
            pushed.add(n)
            log(name=n, olean_pushed=commit, seconds=r['seconds'], peak_rss_gb=r['peak_rss_gb'])

    for jobs in (a.jobs, 1):
        left = [n for n in todo if n not in pushed]
        if not left:
            break
        p = subprocess.Popen(['nice', '-n', '10', sys.executable, GLB, '--root', LEAN, '--direct', '--trust-mtime',
                              '--no-ilean', '--jobs', str(jobs), '--heavy', r'^LocalWindow(Unsat|Cnf)\.(S|T)',
                              '--heavy-jobs', str(jobs), '--rss-cap-gb', str(a.rss_cap_gb), '--min-free-gb', '3.0',
                              '--min-disk-mb', '800', '--log', glog, *['LocalWindowUnsat.' + n for n in left]],
                             env=env, cwd=LEAN, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        log(build=left, jobs=jobs, pid=p.pid)
        while p.poll() is None:
            push_ready()
            time.sleep(30)
        push_ready()
    failed = [n for n in todo if n not in pushed]
    log(done=sorted(pushed), failed=failed)


def opull(a):
    """Production machine (daemon): install the .olean files of xfer/233o/<n> for the names in
    $CERT233_SCR/remote_build (sha256 and Lean commit checked; LocalWindowCnf first, each written
    atomically), delete the local sources of <n> as prod233's sweep does, log the build record to
    data/remotebuild6SB233.jsonl, remember <n> in $CERT233_SCR/oxfer_consumed."""
    import hashlib
    scr = os.environ.get('CERT233_SCR', '/home/user/cert233work')
    done_p = os.path.join(scr, 'oxfer_consumed')
    done = set(open(done_p).read().split()) if os.path.exists(done_p) else set()
    olean = lambda n: os.path.exists(os.path.join(LIB, 'LocalWindowUnsat', n + '.olean'))  # noqa
    while True:
        names = open(os.path.join(scr, 'remote_build')).read().split()
        left = [n for n in names if not olean(n)]
        if not left:
            log(done='all remote .olean files installed')
            return
        try:
            have = ls_branches(OPFX)
        except RuntimeError as e:
            log(error=str(e)[:300])
            time.sleep(a.every)
            continue
        for n in [n for n in left if n in have]:
            b = bare(tempfile.mkdtemp(dir=scr, prefix='opull'))
            try:
                meta, blob = fetch_blobs(OPFX + n, b)
                assert LEAN_COMMIT in meta['lean_version'], 'Lean version ' + meta['lean_version']
                need = sum(f['bytes'] for f in meta['files']) >> 20
                if disk_free_mb() < a.min_disk_mb + need:
                    log(wait='disk', free_mb=disk_free_mb(), need_mb=need)
                    break
                datas = []
                for k, f in enumerate(meta['files']):
                    d = gzip.decompress(b''.join(blob(f'f{k}part{i:02d}') for i in range(f['parts'])))
                    assert len(d) == f['bytes'] and hashlib.sha256(d).hexdigest() == f['sha256'], 'checksum ' + f['path']
                    datas.append(d)
                for f, d in zip(meta['files'], datas):   # LocalWindowCnf first, LocalWindowUnsat last
                    dst = os.path.join(LIB, f['path'])
                    os.makedirs(os.path.dirname(dst), exist_ok=True)
                    open(dst + '.xfer', 'wb').write(d)
                    os.replace(dst + '.xfer', dst)
                for d in ('LocalWindowCnf', 'LocalWindowUnsat'):
                    s = os.path.join(LEAN, d, n + '.lean')
                    if os.path.exists(s):
                        os.remove(s)
                with open(os.path.join(DATA, 'remotebuild6SB233.jsonl'), 'a') as f:
                    f.write(json.dumps({k: v for k, v in meta.items()}) + '\n')
                if n not in done:
                    done.add(n)
                    with open(done_p, 'a') as f:
                        f.write(n + '\n')
                log(name=n, installed=[f['path'] for f in meta['files']], seconds=meta['seconds'])
            except (RuntimeError, subprocess.CalledProcessError, AssertionError, OSError, ValueError, KeyError) as e:
                log(name=n, error=str(e)[:300])
            finally:
                shutil.rmtree(b, ignore_errors=True)
        time.sleep(a.every)


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest='cmd', required=True)
    bp = sp.add_parser('build')
    bp.add_argument('--names', nargs='+', required=True)
    bp.add_argument('--jobs', type=int, default=3)
    bp.add_argument('--rss-cap-gb', type=float, default=11)
    op = sp.add_parser('opull')
    op.add_argument('--every', type=int, default=300)
    op.add_argument('--min-disk-mb', type=int, default=1500)
    g = sp.add_parser('gen')
    g.add_argument('--names', nargs='+', required=True)
    g.add_argument('--seed-jobs', default='auto')
    g.add_argument('--cores', type=int, default=os.cpu_count() or 4)
    g.add_argument('--min-disk-mb', type=int, default=3000)
    p = sp.add_parser('pull')
    p.add_argument('--every', type=int, default=300)
    p.add_argument('--ahead', type=int, default=14)
    p.add_argument('--min-disk-mb', type=int, default=2300)
    a = ap.parse_args()
    {'gen': gen, 'pull': pull, 'build': build, 'opull': opull}[a.cmd](a)


if __name__ == '__main__':
    main()
