"""Compile modules one at a time with `lean -o` into a scratch directory and measure them.

  python measure.py --src ROOT --out OLEANDIR [--axioms] [--tag T] [--log FILE] MODULE[:THEOREM] ...

MODULE is a dotted module name with its source at ROOT/<path>.lean (e.g.
`LocalWindowUnsat.K012340A26336`).  `LEAN_PATH` is OLEANDIR first, then the production
`work/final_lean/.lake/build/lib/lean` (so a module compiled here shadows a production module
of the same name; see the pitfall in ../README.md).  Every `lean` runs under `nice -n 15` and
is killed above 2.9 GB of RSS.  One JSON line per module: source and `.olean` bytes, CPU
seconds (`wait4`), wall seconds and peak RSS.  With `--axioms` and `MODULE:THEOREM`, a second
`lean` prints the axioms of THEOREM (fully qualified) and the line records them.
"""
import argparse, json, os, re, subprocess, sys, tempfile, threading, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
LIB = os.path.join(ROOT, 'work', 'final_lean', '.lake', 'build', 'lib', 'lean')
LEAN = os.environ.get('LEAN', os.path.expanduser('~/.elan/toolchains/leanprover--lean4---v4.19.0/bin/lean'))
CAP_KB = 2.9e6


def run_lean(args, env):
    p = subprocess.Popen(['nice', '-n', '15', LEAN, *args], env=env, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT)
    killed = []

    def guard():
        while True:
            try:
                rss = int([l for l in open('/proc/%d/status' % p.pid) if l.startswith('VmRSS')][0].split()[1])
            except Exception:
                return
            if rss > CAP_KB:
                os.kill(p.pid, 9)
                killed.append(rss)
                return
            time.sleep(0.3)
    threading.Thread(target=guard, daemon=True).start()
    t = time.time()
    out = p.stdout.read()
    _, st, ru = os.wait4(p.pid, 0)
    return st, out.decode(errors='replace'), ru, time.time() - t, killed


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--src', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--axioms', action='store_true')
    ap.add_argument('--tag', default='')
    ap.add_argument('--log')
    ap.add_argument('modules', nargs='+')
    a = ap.parse_args()
    src, out = os.path.abspath(a.src), os.path.abspath(a.out)
    env = dict(os.environ, LEAN_PATH=out + ':' + LIB)
    for spec in a.modules:
        mod, _, thm = spec.partition(':')
        rel = mod.replace('.', '/')
        f, o = os.path.join(src, rel + '.lean'), os.path.join(out, rel + '.olean')
        os.makedirs(os.path.dirname(o), exist_ok=True)
        st, txt, ru, wall, killed = run_lean(['--root=' + src, '-o', o, f], env)
        rec = dict(tag=a.tag, module=mod, src=os.path.getsize(f), ok=st == 0 and not killed,
                   cpu=round(ru.ru_utime + ru.ru_stime, 2), wall=round(wall, 2), rss_gb=round(ru.ru_maxrss / 1e6, 3))
        if killed:
            rec['killed_rss_kb'] = killed[0]
        if st == 0:
            rec['olean'] = os.path.getsize(o)
        else:
            rec['error'] = txt[-1500:]
        if rec['ok'] and a.axioms and thm:
            with tempfile.NamedTemporaryFile('w', suffix='.lean', dir=out, delete=False) as g:
                g.write('import %s\n#print axioms %s\n' % (mod, thm))
            st2, txt2, _, _, _ = run_lean([g.name], env)
            os.remove(g.name)
            m = re.search(r"depends on axioms: \[(.*?)\]", txt2, re.S)
            rec['axioms'] = [x.strip() for x in m.group(1).split(',')] if m else txt2.strip()[-500:]
        print(json.dumps(rec), flush=True)
        if a.log:
            with open(a.log, 'a') as g:
                g.write(json.dumps(rec) + '\n')
        if not rec['ok']:
            sys.exit(1)


if __name__ == '__main__':
    main()
