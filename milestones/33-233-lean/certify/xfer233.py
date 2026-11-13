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
       delete the remote branch, delete the bare repository.  At most --ahead unbuilt sources are kept.
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
        for n in [n for n in order if n in have and (olean(n) or os.path.exists(src(n)))]:
            # built or already materialized (prod or pregen got there first): the branch is no longer needed
            retry(lambda: git('push', '-q', 'origin', '--delete', PFX + n))
            log(name=n, deleted='not needed')
        ready = sum(1 for n in left if os.path.exists(src(n)))
        for n in [n for n in left if n in have and not os.path.exists(src(n))]:
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
                retry(lambda: git('push', '-q', 'origin', '--delete', PFX + n))
            except (RuntimeError, subprocess.CalledProcessError, AssertionError, OSError) as e:
                log(name=n, error=str(e)[:300])
            finally:
                shutil.rmtree(b, ignore_errors=True)
        time.sleep(a.every)


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest='cmd', required=True)
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
    gen(a) if a.cmd == 'gen' else pull(a)


if __name__ == '__main__':
    main()
