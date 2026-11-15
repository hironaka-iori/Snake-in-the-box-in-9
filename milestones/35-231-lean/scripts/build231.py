"""Scratch build of the generated 6SC chain (and the milestone-35 framework modules) into a build
directory, never into work/final_lean/.lake or work/spectral/.verification (whose .olean files are
only read, through LEAN_PATH, as in build_toy.sh).

  python3 build231.py --src DIR --build DIR [--jobs 2] [--only REGEX] [--lean-bin BIN] [--log FILE]
                      [--rss-cap-gb G] [--min-free-gb 1.0] TARGET...

Builds TARGET and every module it imports that has its source in --src or is one of the framework
modules (FRAMEWORK below), in dependency order, at most --jobs `nice -n 10 lean` processes at a
time.  A module whose .olean is newer than its source and its imported sources is skipped (resumable).
Each module is recorded in --log (jsonl: module, seconds, peak RSS of the lean process, olean bytes,
status).  Fails on an error, on "declaration uses 'sorry'" outside modules named in --allow-sorry, if
free disk falls below --min-free-gb, or if a process exceeds --rss-cap-gb (killed by PID).
"""
import argparse, json, os, re, shutil, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
TOOL = '/home/user/lean-deps/toolchain/lean-4.19.0-linux/bin'
MATHLIB = os.environ.get('MATHLIB', '/home/user/lean-deps/mathlib4')
S = os.path.join(ROOT, 'work', 'spectral', 'stronger')
FRAMEWORK = {
    'LocalWindowShareCtx': os.path.join(ROOT, 'work', 'final_lean', 'LocalWindowShareCtx.lean'),
    'WindowAutomaton6SCDefs': os.path.join(S, 'WindowAutomaton6SCDefs.lean'),
    'WindowAutomaton6SCV2': os.path.join(S, 'WindowAutomaton6SCV2.lean'),
    'DirectionWindowBridge6SC': os.path.join(S, 'DirectionWindowBridge6SC.lean'),
    'AggregateDirection6SCConditional': os.path.join(S, 'AggregateDirection6SCConditional.lean'),
    'DirectionWindowBridge6SCChunks': os.path.join(S, 'DirectionWindowBridge6SCChunks.lean'),
}
LEAN_PATH = [os.path.join(ROOT, 'work', 'final_lean', '.lake', 'build', 'lib', 'lean'),
             os.path.join(ROOT, 'work', 'spectral', '.verification', 'chain')]


def imports_of(path):
    out = []
    for line in open(path, encoding='utf-8'):
        m = re.match(r'\s*import\s+(\S+)', line)
        if m:
            out.append(m.group(1))
    return out


def free_gb(p):
    st = os.statvfs(p)
    return st.f_bavail * st.f_frsize / 2 ** 30


def rss_tree_kb(pid):
    tot = 0
    try:
        kids = [pid]
        for p in os.listdir('/proc'):
            if p.isdigit():
                try:
                    if open(f'/proc/{p}/stat').read().split(') ')[1].split()[1] == str(pid):
                        kids.append(int(p))
                except OSError:
                    pass
        for k in kids:
            for line in open(f'/proc/{k}/status'):
                if line.startswith('VmRSS:'):
                    tot += int(line.split()[1])
    except OSError:
        pass
    return tot


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--src', action='append', default=[])
    ap.add_argument('--build', required=True)
    ap.add_argument('--jobs', type=int, default=2)
    ap.add_argument('--lean-bin', default=os.path.join(TOOL, 'lean'))
    ap.add_argument('--log', default=None)
    ap.add_argument('--rss-cap-gb', type=float, default=6.0)
    ap.add_argument('--min-free-gb', type=float, default=1.0)
    ap.add_argument('--allow-sorry', default=r'Shard\d+_\d+$', help='regex of modules allowed to print sorry')
    ap.add_argument('--delete-source-after', action='store_true', help='delete the build-dir copy of each source')
    ap.add_argument('targets', nargs='+')
    a = ap.parse_args()
    B = os.path.abspath(a.build)
    os.makedirs(B, exist_ok=True)
    log = a.log or os.path.join(B, 'build231.jsonl')
    src = {}
    for d in a.src:
        for f in os.listdir(d):
            if f.endswith('.lean'):
                src[f[:-5]] = os.path.join(d, f)
        for sub in ('LocalWindowCtxCnf', 'LocalWindowCtxUnsat'):
            if os.path.isdir(os.path.join(d, sub)):
                for f in os.listdir(os.path.join(d, sub)):
                    if f.endswith('.lean'):
                        src[f'{sub}.{f[:-5]}'] = os.path.join(d, sub, f)
    for m, p in FRAMEWORK.items():
        src.setdefault(m, p)
    deps, order, seen = {}, [], set()

    def visit(m):
        if m in seen or m not in src:
            return
        seen.add(m)
        deps[m] = [x for x in imports_of(src[m]) if x in src]
        for x in deps[m]:
            visit(x)
        order.append(m)
    for t in a.targets:
        assert t in src, f'no source for {t}'
        visit(t)
    olean = lambda m: os.path.join(B, *m.split('.')) + '.olean'   # noqa: E731
    stale = {}
    for m in order:
        o = olean(m)
        stale[m] = (not os.path.exists(o) or os.path.getmtime(o) < os.path.getmtime(src[m])
                    or any(stale[x] for x in deps[m])
                    or any(os.path.getmtime(olean(x)) > os.path.getmtime(o) for x in deps[m] if os.path.exists(olean(x))))
    todo = [m for m in order if stale[m]]
    print(f'{len(order)} modules, {len(todo)} to build; free disk {free_gb(B):.2f} GB', flush=True)
    env = dict(os.environ)
    env['PATH'] = TOOL + ':' + env['PATH']
    env['LEAN_PATH'] = ':'.join(LEAN_PATH + [B])
    # mathlib's search path as `lake env` sets it (then ours), so that `lean` runs as a direct child
    lp = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=MATHLIB, env=env, capture_output=True,
                        text=True, check=True).stdout.strip()
    env['LEAN_PATH'] = ':'.join(os.path.normpath(os.path.join(MATHLIB, x)) for x in lp.split(':'))
    done = {m for m in order if not stale[m]}
    running = {}
    failed = []
    t_all = time.time()
    while todo or running:
        if free_gb(B) < a.min_free_gb:
            for pid in running:
                os.kill(pid, 9)
            sys.exit(f'free disk below {a.min_free_gb} GB; stopped')
        while len(running) < a.jobs and not failed:
            ready = [m for m in todo if all(x in done for x in deps[m])]
            if not ready:
                break
            m = ready[0]
            todo.remove(m)
            p = os.path.join(B, *m.split('.')) + '.lean'
            os.makedirs(os.path.dirname(p), exist_ok=True)
            shutil.copyfile(src[m], p)
            out = open(p[:-5] + '.out', 'w')
            cmd = ['nice', '-n', '10', a.lean_bin, f'--root={B}', '-o', olean(m), p]
            pr = subprocess.Popen(cmd, cwd=MATHLIB, stdout=out, stderr=subprocess.STDOUT, env=env)
            running[pr.pid] = (m, pr, time.time(), 0, out, p)
        time.sleep(0.5)
        for pid in list(running):
            m, pr, t0, peak, out, p = running[pid]
            r = rss_tree_kb(pid)
            peak = max(peak, r)
            running[pid] = (m, pr, t0, peak, out, p)
            if r > a.rss_cap_gb * 2 ** 20:
                subprocess.run(['pkill', '-9', '-P', str(pid)]); os.kill(pid, 9)
            wpid, wst, ru = os.wait4(pid, os.WNOHANG)
            if wpid == 0:
                continue
            pr.returncode = os.waitstatus_to_exitcode(wst)
            out.close()
            del running[pid]
            txt = open(p[:-5] + '.out').read()
            sec = round(time.time() - t0, 1)
            ok = pr.returncode == 0
            st = 'ok' if ok else f'error {pr.returncode}'
            if ok and "declaration uses 'sorry'" in txt and not re.search(a.allow_sorry, m):
                st = 'sorry'; ok = False
            rec = dict(module=m, status=st, seconds=sec, cpu_s=round(ru.ru_utime + ru.ru_stime, 1),
                       peak_rss_gb=round(ru.ru_maxrss / 2 ** 20, 3), tree_rss_gb=round(peak / 2 ** 20, 3),
                       olean_bytes=os.path.getsize(olean(m)) if os.path.exists(olean(m)) else None,
                       source_bytes=os.path.getsize(src[m]), sorry="declaration uses 'sorry'" in txt,
                       time=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()))
            open(log, 'a').write(json.dumps(rec) + '\n')
            print(json.dumps(rec), flush=True)
            if ok:
                done.add(m)
                if a.delete_source_after:
                    os.remove(p)
            else:
                print(txt[-4000:], flush=True)
                failed.append(m)
                if os.path.exists(olean(m)):
                    os.remove(olean(m))
        if failed and not running:
            break
    print(f'wall {time.time() - t_all:.0f}s; failed {failed}; free disk {free_gb(B):.2f} GB', flush=True)
    sys.exit(1 if failed else 0)


if __name__ == '__main__':
    main()
