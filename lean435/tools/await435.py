#!/usr/bin/env python3
"""Wait for a chain's certificates and assemble it as soon as they are all published (milestone 36).

    await435.py --tag T --chain DIR --bound B --work W [--every 1200] [--pfx ...] [--floors-src FS --floors-build FB]

DIR is a chain work directory of chain435.sh (src, build, glue with glue-needs.json). Every --every s:
  1. prod435.py merge of the branch families (default: xfer/c435, c435help, c435free, c435freehelp)
     into W/iface;
  2. the glue chunks whose certificates are all present and not built yet are built
     (assemble435.py --chunks, interfaces only);
  3. once no certificate is missing: assemble435.py in full (the remaining chunks, the top module and
     the final audit of upper_<B>_435), then exit with its exit code. W/final-audit.txt holds the audit.
Progress goes to W/await.log.
"""
import argparse, json, os, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
FAMS = ['refs/heads/xfer/c435/', 'refs/heads/xfer/c435help/', 'refs/heads/xfer/c435free/',
        'refs/heads/xfer/c435freehelp/']


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--tag', required=True)
    ap.add_argument('--chain', required=True)
    ap.add_argument('--bound', type=int, required=True)
    ap.add_argument('--work', required=True)
    ap.add_argument('--every', type=float, default=1200)
    ap.add_argument('--pfx', nargs='+', default=FAMS)
    ap.add_argument('--floors-src', default=os.path.expanduser('~/l435/floors/src'))
    ap.add_argument('--floors-build', default=os.path.expanduser('~/l435/floors/build'))
    ap.add_argument('--jobs', type=int, default=3)
    a = ap.parse_args()
    T, C, W = a.tag, os.path.abspath(a.chain), os.path.abspath(a.work)
    os.makedirs(W, exist_ok=True)
    logf = open(os.path.join(W, 'await.log'), 'a')

    def log(m):
        line = time.strftime('%Y-%m-%dT%H:%M:%SZ ', time.gmtime()) + m
        print(line, flush=True)
        logf.write(line + '\n'); logf.flush()

    iface = os.path.join(W, 'iface')
    asm = [sys.executable, os.path.join(HERE, 'assemble435.py'), '--tag', T, '--chain-src', os.path.join(C, 'src'),
           '--chain-build', os.path.join(C, 'build'), '--glue', os.path.join(C, 'glue'), '--iface', iface,
           '--manifest', os.path.join(iface, 'manifest.jsonl'), '--floors-src', a.floors_src,
           '--floors-build', a.floors_build, '--bound', str(a.bound), '--jobs', str(a.jobs), '--work', os.path.join(W, 'asm')]
    need = json.load(open(os.path.join(C, 'glue', 'glue-needs.json')))
    gb = os.path.join(W, 'asm', 'glue-build')
    while True:
        r = subprocess.run([sys.executable, os.path.join(HERE, 'prod435.py'), 'merge', '--out', iface, '--pfx', *a.pfx],
                           capture_output=True, text=True)
        log('merge: ' + (r.stdout.strip().splitlines() or ['?'])[-1] + (f' (exit {r.returncode})' if r.returncode else ''))
        if r.returncode != 0:
            log(r.stderr[-1500:])
            time.sleep(a.every)
            continue
        have = {json.loads(l)['module'] for l in open(os.path.join(iface, 'manifest.jsonl')) if l.strip()}
        allc = {c for v in need.values() for c in v}
        miss = sorted(allc - have)
        new = [m for m, v in need.items() if all(c in have for c in v)
               and not os.path.exists(os.path.join(gb, m + '.olean'))]
        log(f'{len(allc) - len(miss)} of {len(allc)} certificates present, {len(miss)} missing; '
            f'{sum(1 for m in need if os.path.exists(os.path.join(gb, m + ".olean")))} of {len(need)} chunks built, '
            f'{len(new)} new ready')
        if not miss:
            log('all certificates present: full assembly')
            r = subprocess.run(asm, capture_output=True, text=True)
            open(os.path.join(W, 'assemble-final.log'), 'w').write(r.stdout + r.stderr)
            log(f'assembly exit {r.returncode}: ' + (r.stdout.strip().splitlines() or ['?'])[-1])
            sys.exit(r.returncode)
        if new:
            sfx = [m[len(f'Glue6SC{T}'):] for m in new]
            r = subprocess.run(asm + ['--chunks', ','.join(sfx)], capture_output=True, text=True)
            log(f'chunks: exit {r.returncode}, ' + next((l for l in r.stdout.splitlines() if l.startswith('glue chunks:')), '?'))
            if r.returncode != 0:
                log((r.stdout + r.stderr)[-2500:])
        open(os.path.join(W, 'missing.txt'), 'w').write('\n'.join(miss) + '\n')
        time.sleep(a.every)


if __name__ == '__main__':
    main()
