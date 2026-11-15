#!/usr/bin/env python3
"""Build Lean 4.35 modules with direct `lean -o` calls, in dependency order.

    python3 lean435/tools/build.py --src DIR --build DIR [--jobs 3] [--rss-gb 4] TARGET...

- Dependencies are read from the module headers under --src (`public`/`meta`/`all` imports);
  imports with no source under --src are looked up on LEAN_PATH (mathlib: --mathlib).
- Each module is built with `nice -n 10 lean -R SRC -o BUILD/M.olean SRC/M.lean`; lean writes
  .olean, .olean.server, .olean.private, .ir, .ir.sig next to it.
- A module is rebuilt when the sha256 of its source or of the stamps of its imports changed
  (stamp file BUILD/M.stamp).
- A watchdog kills a lean whose RssAnon passes --rss-gb (one module may get more with --big M=GB,
  and it then runs alone). The build fails on an error or on `declaration uses 'sorry'`.
- One json line per module goes to BUILD/build-log.jsonl: wall s, CPU s, peak RssAnon and peak
  RSS (GB), output bytes per part.
"""
import argparse, hashlib, json, os, re, subprocess, sys, time

LEAN = '/opt/lean-4.35.0-linux/bin/lean'
HDR_IMPORT = re.compile(r'^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)')
PARTS = ('.olean', '.olean.server', '.olean.private', '.ir', '.ir.sig')


def header_imports(path):
    out, in_block = [], 0
    for line in open(path, encoding='utf-8'):
        s = line.strip()
        if in_block:
            in_block += s.count('/-') - s.count('-/')
            continue
        if not s or s.startswith('--') or s in ('module', 'prelude'):
            continue
        if s.startswith('/-'):
            in_block = s.count('/-') - s.count('-/')
            continue
        m = HDR_IMPORT.match(s)
        if m:
            out.append(m.group(1))
            continue
        break
    return out


def sha(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def rss_of(pid):
    try:
        anon = rss = 0
        for line in open(f'/proc/{pid}/status'):
            if line.startswith('RssAnon:'):
                anon = int(line.split()[1]) * 1024
            elif line.startswith('VmRSS:'):
                rss = int(line.split()[1]) * 1024
        return anon, rss
    except OSError:
        return 0, 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--src', required=True)
    ap.add_argument('--build', required=True)
    ap.add_argument('--mathlib', default=os.path.expanduser('~/l435/mathlib4'))
    ap.add_argument('--jobs', type=int, default=3)
    ap.add_argument('--rss-gb', type=float, default=4.0)
    ap.add_argument('--big', action='append', default=[], help='MODULE=GB: own cap, runs alone')
    ap.add_argument('--min-free-gb', type=float, default=3.0)
    ap.add_argument('-D', action='append', default=[], help='extra lean option name=value')
    ap.add_argument('targets', nargs='+')
    a = ap.parse_args()
    src, bld = os.path.abspath(a.src), os.path.abspath(a.build)
    os.makedirs(bld, exist_ok=True)
    big = {k: float(v) for k, v in (x.split('=') for x in a.big)}
    lp = [bld] + [os.path.join(a.mathlib, '.lake/build/lib/lean')]
    pk = os.path.join(a.mathlib, '.lake/packages')
    if os.path.isdir(pk):
        lp += [os.path.join(pk, p, '.lake/build/lib/lean') for p in sorted(os.listdir(pk))]
    env = dict(os.environ, LEAN_PATH=':'.join(lp))

    # dependency graph over modules with source under --src
    deps, order, seen = {}, [], set()

    def visit(m, stack=()):
        if m in seen:
            return
        p = os.path.join(src, m.replace('.', '/') + '.lean')
        if not os.path.exists(p):
            seen.add(m)
            return  # external (mathlib, core)
        if m in stack:
            raise SystemExit(f'import cycle at {m}')
        ds = [d for d in header_imports(p)]
        for d in ds:
            visit(d, stack + (m,))
        deps[m] = [d for d in ds if d in deps]
        seen.add(m)
        order.append(m)
    for t in a.targets:
        visit(t)

    stamp = {}

    def want_stamp(m):
        p = os.path.join(src, m.replace('.', '/') + '.lean')
        h = hashlib.sha256(sha(p).encode())
        for d in deps[m]:
            h.update(stamp[d].encode())
        return h.hexdigest()

    logf = open(os.path.join(bld, 'build-log.jsonl'), 'a')
    pending = list(order)
    running = {}  # module -> (proc, t0, peak_anon, peak_rss, outfile)
    done, failed = set(), None
    built = skipped = 0
    while running or (pending and failed is None):
        # start what can start
        while pending and failed is None:
            alone = any(m in big for m in running)
            if alone or len(running) >= a.jobs:
                break
            ready = [m for m in pending if all(d in done for d in deps[m])]
            if not ready:
                break
            m = ready[0]
            if m in big and running:
                break
            want = want_stamp(m)
            out = os.path.join(bld, m.replace('.', '/'))
            sf = out + '.stamp'
            if os.path.exists(sf) and open(sf).read().strip() == want and os.path.exists(out + '.olean'):
                stamp[m] = want
                done.add(m)
                pending.remove(m)
                skipped += 1
                continue
            st = os.statvfs(bld)
            if st.f_bavail * st.f_frsize < a.min_free_gb * 2**30:
                raise SystemExit(f'disk floor: less than {a.min_free_gb} GB free')
            os.makedirs(os.path.dirname(out), exist_ok=True)
            for ext in PARTS + ('.stamp',):
                if os.path.exists(out + ext):
                    os.remove(out + ext)
            cmd = ['nice', '-n', '10', LEAN, '-R', src, '-o', out + '.olean']
            for d in a.D:
                cmd += ['-D', d]
            cmd.append(os.path.join(src, m.replace('.', '/') + '.lean'))
            fo = open(out + '.out', 'w')
            pr = subprocess.Popen(cmd, stdout=fo, stderr=subprocess.STDOUT, env=env)
            running[m] = [pr, time.time(), 0, 0, fo, want]
            pending.remove(m)
            if m in big:
                break
        if not running and pending and failed is None and not any(all(d in done for d in deps[m]) for m in pending):
            raise SystemExit('nothing can start')
        # poll
        time.sleep(0.2)
        for m in list(running):
            pr, t0, pa, prss, fo, want = running[m]
            # nice wraps lean: find the child
            anon, rss = 0, 0
            try:
                kids = open(f'/proc/{pr.pid}/task/{pr.pid}/children').read().split()
            except OSError:
                kids = []
            for k in [pr.pid] + [int(x) for x in kids]:
                x, y = rss_of(k)
                anon, rss = max(anon, x), max(rss, y)
            running[m][2], running[m][3] = max(pa, anon), max(prss, rss)
            cap = big.get(m, a.rss_gb)
            if anon > cap * 2**30:
                for k in [int(x) for x in kids]:
                    try:
                        os.kill(k, 9)
                    except OSError:
                        pass
                pr.kill()
                fo.write(f'\nKILLED: RssAnon above {cap} GB\n')
            r = os.wait4(pr.pid, os.WNOHANG)
            if r[0] == 0:
                continue
            code = os.waitstatus_to_exitcode(r[1])
            ru = r[2]
            fo.close()
            out = os.path.join(bld, m.replace('.', '/'))
            txt = open(out + '.out').read()
            sizes = {e: os.path.getsize(out + e) for e in PARTS if os.path.exists(out + e)}
            rec = dict(module=m, exit=code, wall=round(time.time() - t0, 2),
                       cpu=round(ru.ru_utime + ru.ru_stime, 2), anon_gb=round(running[m][2] / 2**30, 3),
                       rss_gb=round(max(running[m][3], ru.ru_maxrss * 1024) / 2**30, 3), bytes=sizes,
                       sorry="declaration uses 'sorry'" in txt, t=time.strftime('%H:%M:%S'))
            logf.write(json.dumps(rec) + '\n')
            logf.flush()
            del running[m]
            if code != 0 or rec['sorry'] or 'error:' in txt:
                print(f'FAILED {m} (exit {code}, {rec["wall"]} s, {rec["anon_gb"]} GB)\n{txt[-4000:]}', flush=True)
                failed = m
                continue
            with open(out + '.stamp', 'w') as f:
                f.write(want + '\n')
            stamp[m] = want
            done.add(m)
            built += 1
            print(f'ok {m}: {rec["wall"]} s, cpu {rec["cpu"]} s, anon {rec["anon_gb"]} GB', flush=True)
    print(f'built {built}, up to date {skipped}, of {len(order)}' + (f'; FAILED at {failed}' if failed else ''))
    sys.exit(1 if failed else 0)


if __name__ == '__main__':
    main()
