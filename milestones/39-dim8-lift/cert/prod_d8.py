#!/usr/bin/env python3
"""Distributed production of the level-L cube certificates `Unsat (cubeCnfQ 13 L A k)` (milestone 39).

    prod_d8.py setup --stack DIR                          port + build the module stack (once per machine)
    prod_d8.py run --stack DIR --work DIR --index I[,J|-K] --workers W [--hours H] [--procs 3] [--mem-gb 12]
                   [--L 116] [--max-k 30] [--only A,A,...] [--publish] [--ref-prefix refs/heads/xfer/d8] [--name N]
    prod_d8.py status --work DIR                          counts from the local manifest

Work item: one representative (k, A) of data/q6_29.txt with k >= ceil(L/4). Worker I of W owns the items
with sha1(module) % W == I (module = CubeQ<AHEX>), largest k first; a big machine may own several indices
(--index 0-15 or 0,5,9), so shares can follow machine size. Items with k > --max-k (default 30: the 24
size-31/32 cubes, which go through the split route) are left out. Per item, in its own job directory:
  1. make_cert.py   Lean export, CaDiCaL LRAT, compaction, v3 replay, provenance and renaming chunks
  2. build_cert.sh  builds every module against the stack (peak RSS per module is recorded)
  3. check          compiles `#print axioms unsat` from a clean directory holding only the public
                    .olean of the certificate (lean --setup, importArts), as lean435/tools/audit.py does
  4. record         one manifest line: module, A, k, sha256 of the public .olean, hints, seconds, peak RSS,
                    generator commit, host
Only the public .olean (about 9 KB; the statement `unsat` alone) is kept; the job directory is deleted.

Publication (only with --publish): fast-forward pushes of <ref-prefix>/<name> (default w<first index>) holding the public .olean files
and manifest.jsonl. Without --publish everything stays in --work. A restarted worker skips every module
already in its manifest. STOP: a file STOP in --work; running jobs finish, no new job starts.
Scheduling: at most --procs jobs at once. A job reserves 1.5 GB for generation; once its hint count is
known it reserves pred_gb(hints, vars) (3.1 GB + 0.55 GB per million hints, scaled by
sqrt(vars / 14,000) above 14,000 core variables; measured) and waits until the
reservations fit in --mem-gb (a job that does not fit even alone runs alone). A job whose build fails is recorded as FAILED
with its log tail and is not retried in the same run. A SAT cube (make_cert assertion) stops the worker.
"""
import argparse, hashlib, json, os, shutil, socket, subprocess, sys, threading, time

HERE = os.path.dirname(os.path.abspath(__file__)); M = os.path.abspath(os.path.join(HERE, '..'))
ROOT = os.path.abspath(os.path.join(M, '..', '..')); LEAN = '/opt/lean-4.35.0-linux/bin/lean'
GEN_GB = 4.0        # generation (CaDiCaL, compaction, genv3stream) before the hint count is known;
                    # 1.5 GB let pilot.py be OOM-killed on k = 30 cubes next to 2 other jobs (16 GB sessions)
def pred_gb(hints, nvars):
    # measured peaks (hints, core vars -> GB): 1.0 M, 9 k -> 3.7; 1.3 M, 11 k -> 3.9; 5.3 M, 14 k -> 6.05;
    # 9.75 M, 14 k -> 7.6; 9.65 M, 23 k -> 9.7 (clause masks grow with the variable count)
    return 3.1 + 0.55 * hints / 1e6 * max(1.0, nvars / 14000) ** 0.5
BUDGET = dict(used=0.0, cap=12.0); BLOCK = threading.Condition()


def reserve(old, new):
    """change this job's reservation from old to new GB; waits until it fits (or the job would run alone)"""
    # release the old reservation first, then wait: two jobs that both held GEN_GB and both needed more
    # than the rest waited on each other forever (seen at --procs 2 --mem-gb 12 with two ~11 GB jobs)
    with BLOCK:
        BUDGET['used'] -= old; BLOCK.notify_all()
        while BUDGET['used'] + new > BUDGET['cap'] and BUDGET['used'] > 0:
            BLOCK.wait(10)
        BUDGET['used'] += new; BLOCK.notify_all()


def sh(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def setup(a):
    st = os.path.abspath(a.stack); os.makedirs(st, exist_ok=True)
    r = sh([sys.executable, os.path.join(ROOT, 'lean435', 'tools', 'port.py'), '--out', st,
            'LocalWindowModel', 'LratV3', 'Snake9', 'ProofPack'])
    assert r.returncode == 0, r.stderr
    r = sh([sys.executable, os.path.join(HERE, 'port39.py'), st, 'RenN', 'Split', 'Final'])
    assert r.returncode == 0, r.stderr
    order = ['LocalWindowModel', 'LratV3', 'Snake9', 'ProofPack'] + r.stdout.split()
    os.makedirs(os.path.join(st, 'build'), exist_ok=True)
    for m in order:
        o = os.path.join(st, 'build', m + '.olean')
        if os.path.exists(o): continue
        r = sh([LEAN, '--root=.', '-o', o, m + '.lean'], cwd=st, env=dict(os.environ, LEAN_PATH=os.path.join(st, 'build')))
        print(m, r.returncode, flush=True)
        assert r.returncode == 0, r.stdout[-2000:]
    open(os.path.join(st, 'order.txt'), 'w').write(' '.join(order))
    print('stack built:', st)


def items(L):
    need = -(-L // 4); out = []
    for l in open(os.path.join(M, 'data', 'q6_29.txt')):
        k, _, h = l.split(); k = int(k)
        if k >= need: out.append((k, h))
    return out


def modname(h): return 'CubeQ' + h.upper()


def public_closure(stack):
    """public .olean files the statement of `unsat` needs (CubeCnf and its public imports)."""
    b = os.path.join(stack, 'build'); arts = {}
    todo = ['CubeCnf']
    while todo:
        m = todo.pop()
        if m in arts or m == 'Std': continue
        arts[m] = [[os.path.join(b, m + '.olean')], []]
        for l in open(os.path.join(stack, m + '.lean')):
            if l.startswith('public import '): todo.append(l.split()[2])
    return arts


def check_public(stack, olean, mod, wd):
    d = os.path.join(wd, 'pubcheck'); os.makedirs(d, exist_ok=True)
    shutil.copyfile(olean, os.path.join(d, mod + '.olean'))
    arts = public_closure(stack); arts[mod] = [[os.path.join(d, mod + '.olean')], []]
    ns = 'Snake9.CubeProv.' + mod[4:]
    open(os.path.join(d, 'Chk.lean'), 'w').write('module\n\nimport %s\n\n#check @%s.unsat\n#print axioms %s.unsat\n' % (mod, ns, ns))
    json.dump(dict(name='Chk', isModule=True, importArts=arts, dynlibs=[], plugins=[], options={}), open(os.path.join(d, 'setup.json'), 'w'))
    r = sh([LEAN, '--setup', 'setup.json', 'Chk.lean'], cwd=d, env=dict(os.environ, LEAN_PATH='/nonexistent'))
    out = r.stdout + r.stderr
    ok = (r.returncode == 0 and "depends on axioms: [propext, Classical.choice, Quot.sound]" in out
          and 'cubeCnfQ 13' in out and 'sorry' not in out)
    return ok, out.strip()


def job(a, k, h, res):
    try:
        job1(a, k, h, res)
    finally:
        with BLOCK:
            BUDGET['used'] -= BUDGET_OF.pop(threading.get_ident(), 0); BLOCK.notify_all()


BUDGET_OF = {}


def job1(a, k, h, res):
    me = threading.get_ident(); BUDGET_OF[me] = GEN_GB   # the main loop has added GEN_GB to BUDGET['used']
    mod = modname(h); wd = os.path.join(a.work, 'jobs', mod); shutil.rmtree(wd, ignore_errors=True); os.makedirs(wd)
    t = time.time(); rec = dict(module=mod, A=h, k=k, L=a.L, host=socket.gethostname(), commit=a.commit)
    # solve-time cap: hints <= (mem_gb - 3.1) / 0.55 M fit; at >= 28 k hints per solver second a longer solve cannot fit
    lim = max(300.0, (a.mem_gb - 3.1) / 0.55 * 1e6 / 28000)
    r = sh([sys.executable, os.path.join(HERE, 'make_cert.py'), str(a.L), h, str(k), wd], cwd=HERE,
           env=dict(os.environ, SOLVE_LIMIT=str(round(lim))))
    if r.returncode == 11:   # solve cap reached: too big for this machine, left to a bigger one
        rec.update(status='TOO_BIG', mem_gb=a.mem_gb, solve_limit=round(lim)); res.append(rec); return
    if r.returncode != 0:
        rec.update(status='SAT?' if r.returncode == 10 else 'GEN_FAILED',
                   log=(r.stdout + r.stderr)[-1500:])
        res.append(rec); return
    g = json.loads(r.stdout.strip().splitlines()[-1]); rec.update(gen_s=g['gen_s'], solve_s=g['solve_s'], hints=g['replay']['hints'],
                                                                  core=g['core']['core'], vars=g['core']['vars'])
    pg = pred_gb(g['replay']['hints'], g['core']['vars']); rec['pred_gb'] = round(pg, 1)
    if pg > a.mem_gb:   # cannot build here (k = 30 cubes reach 133 M hints, ~100 GB): left to a bigger machine
        rec.update(status='TOO_BIG', mem_gb=a.mem_gb); res.append(rec); return
    reserve(GEN_GB, pg); BUDGET_OF[me] = pg
    tb = time.time()
    r = sh(['bash', os.path.join(HERE, 'build_cert.sh'), wd, 'Q' + h.upper()], env=dict(os.environ, STACK=os.path.join(a.stack, 'build')))
    rss = [int(x.split()[0]) for x in r.stdout.split(' s ')[1:] if x.split()[0].isdigit()]
    rec.update(build_s=round(time.time() - tb, 1), peak_mb=max(rss) if rss else None)
    olean = os.path.join(wd, 'build', mod + '.olean')
    if 'CERT BUILT' not in r.stdout or not os.path.exists(olean):
        rec.update(status='BUILD_FAILED', log=r.stdout[-1500:]); res.append(rec); return
    ok, out = check_public(a.stack, olean, mod, wd)
    if not ok:
        rec.update(status='CHECK_FAILED', log=out[-1500:]); res.append(rec); return
    dst = os.path.join(a.work, 'olean', mod + '.olean'); os.makedirs(os.path.dirname(dst), exist_ok=True)
    shutil.copyfile(olean, dst)
    rec.update(status='OK', sha256=hashlib.sha256(open(dst, 'rb').read()).hexdigest(), total_s=round(time.time() - t, 1))
    shutil.rmtree(wd, ignore_errors=True)
    res.append(rec)


def publish(a):
    """fast-forward push of olean/ and manifest.jsonl to <ref-prefix>/w<I> (only with --publish)."""
    pub = os.path.join(a.work, 'pub'); ref = '%s/%s' % (a.ref_prefix, a.name)
    if not os.path.exists(os.path.join(pub, '.git')):
        os.makedirs(pub, exist_ok=True); sh(['git', 'init', '-q'], cwd=pub)
        url = sh(['git', 'remote', 'get-url', 'origin'], cwd=ROOT).stdout.strip(); sh(['git', 'remote', 'add', 'origin', url], cwd=pub)
        if sh(['git', 'fetch', '-q', 'origin', ref], cwd=pub).returncode == 0: sh(['git', 'reset', '-q', '--hard', 'FETCH_HEAD'], cwd=pub)
    os.makedirs(os.path.join(a.work, 'olean'), exist_ok=True)   # no certificate yet: publish the manifest alone
    for f in os.listdir(os.path.join(a.work, 'olean')): shutil.copyfile(os.path.join(a.work, 'olean', f), os.path.join(pub, f))
    shutil.copyfile(os.path.join(a.work, 'manifest.jsonl'), os.path.join(pub, 'manifest.jsonl'))
    sh(['git', 'add', '-A'], cwd=pub)
    if sh(['git', 'diff', '--cached', '--quiet'], cwd=pub).returncode == 0: return
    sh(['git', '-c', 'user.name=prod_d8', '-c', 'user.email=prod_d8@localhost', 'commit', '-q', '-m', 'd8 %s: %s' % (a.name, time.ctime())], cwd=pub)
    for i in range(4):
        if sh(['git', 'push', '-q', 'origin', 'HEAD:' + ref], cwd=pub).returncode == 0: return
        time.sleep(2 ** (i + 1))
    print('publish failed (kept locally)', flush=True)


def run(a):
    a.work = os.path.abspath(a.work); a.stack = os.path.abspath(a.stack); os.makedirs(a.work, exist_ok=True)
    a.indices = set()
    for part in a.index.split(','):
        lo, _, hi = part.partition('-'); a.indices.update(range(int(lo), int(hi or lo) + 1))
    assert a.indices and max(a.indices) < a.workers, 'indices must be < --workers'
    a.name = a.name or 'w%d' % min(a.indices)
    a.commit = sh(['git', 'rev-parse', 'HEAD'], cwd=ROOT).stdout.strip()
    man = os.path.join(a.work, 'manifest.jsonl')
    # only certified (or SAT?) items count as done: a failed item is retried by the next run
    done = {r['module'] for r in map(json.loads, open(man)) if r['status'] in ('OK', 'SAT?')
            or (r['status'] == 'TOO_BIG' and r.get('mem_gb', 0) >= a.mem_gb)} if os.path.exists(man) else set()
    its = items(a.L)
    if a.only: its = [x for x in its if x[1] in a.only.split(',')]
    else: its = [x for x in its if x[0] <= a.max_k and int(hashlib.sha1(modname(x[1]).encode()).hexdigest(), 16) % a.workers in a.indices]
    its = [x for x in its if modname(x[1]) not in done]
    its.sort(key=lambda x: (-x[0], x[1]))
    print('worker %s (indices %s of %d): %d items to do, %d done' % (a.name, a.index, a.workers, len(its), len(done)), flush=True)
    BUDGET['cap'] = a.mem_gb
    end = time.time() + a.hours * 3600; res = []; running = []; lock = threading.Lock()
    while its or running:
        running = [t for t in running if t.is_alive()]
        with lock:
            for rec in res:
                open(man, 'a').write(json.dumps(rec) + '\n'); print(json.dumps(rec), flush=True)
                if rec['status'] == 'SAT?':
                    open(os.path.join(a.work, 'STOP'), 'w').write('SAT? ' + rec['module']); its = []
            if res and a.publish: publish(a)
            res.clear()
        stop = os.path.exists(os.path.join(a.work, 'STOP')) or time.time() > end
        if its and not stop and len(running) < a.procs and BUDGET['used'] + GEN_GB <= a.mem_gb:
            k, h = its.pop(0)
            with BLOCK: BUDGET['used'] += GEN_GB
            t = threading.Thread(target=job, args=(a, k, h, res)); t.start(); running.append(t)
            continue
        if stop and not running: break
        time.sleep(5)
    print('worker finished', flush=True)


def status(a):
    man = os.path.join(a.work, 'manifest.jsonl'); c = {}
    for l in open(man):
        r = json.loads(l); c[r['status']] = c.get(r['status'], 0) + 1
    print(c)


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); sp = ap.add_subparsers(dest='cmd', required=True)
    s = sp.add_parser('setup'); s.add_argument('--stack', required=True)
    r = sp.add_parser('run')
    for x, d in (('--stack', None), ('--work', None)): r.add_argument(x, required=True)
    r.add_argument('--index', default='0'); r.add_argument('--name', default=''); r.add_argument('--max-k', type=int, default=30); r.add_argument('--workers', type=int, default=1)
    r.add_argument('--hours', type=float, default=1e6); r.add_argument('--procs', type=int, default=3)
    r.add_argument('--mem-gb', type=float, default=12); r.add_argument('--L', type=int, default=116)
    r.add_argument('--only', default=''); r.add_argument('--publish', action='store_true')
    r.add_argument('--ref-prefix', default='refs/heads/xfer/d8')
    t = sp.add_parser('status'); t.add_argument('--work', required=True)
    a = ap.parse_args()
    {'setup': setup, 'run': run, 'status': status}[a.cmd](a)
