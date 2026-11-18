#!/usr/bin/env python3
"""Wait for the 230 certificates and assemble the bound as soon as they are all published (milestone 37).

    await230.py --spec-src S --spec-build B --glue G --arch231 A --work W [--every 1200] [--jobs 3]

S, B: the spec layer (c230chain.sh: WORKDIR/src, WORKDIR/build; plus the core stack, passed first by
default: ~/l435/prod/core-src, ~/l435/prod/core). G: c230gen.py's glue directory (with ../glue-needs.json).
A: the extracted archive branch research/c435-interfaces-231 (LocalWindowCert/…, manifest.jsonl).
Every --every s:
  1. prod435.py merge of xfer/c230 and xfer/c230help (owners, helpers, split finals, share helpers) into
     W/iface230, then W/iface = hard links of W/iface230 and A, W/iface/manifest.jsonl = both manifests
     (a module in both must have the same .olean sha256);
  2. the glue chunks whose certificates are all present and not built yet are built
     (assemble230.py --chunks, interfaces only);
  3. once nothing is missing: assemble230.py in full (G230 and the final audit of upper_230_435), then
     exit with its exit code. W/asm/final-audit.txt holds the audit.
Progress: W/await.log; missing modules: W/missing.txt.
"""
import argparse, json, os, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
FAMS = ['refs/heads/xfer/c230/', 'refs/heads/xfer/c230help/']


def link_tree(src, dst):
    for root, _, files in os.walk(src):
        for f in files:
            if not f.endswith('.olean'):
                continue
            p = os.path.join(root, f)
            q = os.path.join(dst, os.path.relpath(p, src))
            if not os.path.exists(q):
                os.makedirs(os.path.dirname(q), exist_ok=True)
                os.link(p, q)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--spec-src', action='append', default=None)
    ap.add_argument('--spec-build', action='append', default=None)
    ap.add_argument('--glue', required=True)
    ap.add_argument('--arch231', required=True)
    ap.add_argument('--work', required=True)
    ap.add_argument('--every', type=float, default=1200)
    ap.add_argument('--jobs', type=int, default=3)
    ap.add_argument('--once', action='store_true', help='one round (tests)')
    a = ap.parse_args()
    core = [os.path.expanduser('~/l435/prod/core-src')], [os.path.expanduser('~/l435/prod/core')]
    ss = core[0] + (a.spec_src or [])
    sb = core[1] + (a.spec_build or [])
    W = os.path.abspath(a.work)
    os.makedirs(W, exist_ok=True)
    logf = open(os.path.join(W, 'await.log'), 'a')

    def log(m):
        line = time.strftime('%Y-%m-%dT%H:%M:%SZ ', time.gmtime()) + m
        print(line, flush=True)
        logf.write(line + '\n'); logf.flush()

    i230, iface = os.path.join(W, 'iface230'), os.path.join(W, 'iface')
    asm = [sys.executable, os.path.join(HERE, 'assemble230.py')]
    for s, b in zip(ss, sb):
        asm += ['--spec-src', s, '--spec-build', b]
    asm += ['--glue', os.path.abspath(a.glue), '--iface', iface, '--manifest', os.path.join(iface, 'manifest.jsonl'),
            '--jobs', str(a.jobs), '--work', os.path.join(W, 'asm')]
    need = json.load(open(os.path.join(os.path.dirname(os.path.abspath(a.glue)), 'glue-needs.json')))
    gb = os.path.join(W, 'asm', 'glue-build')
    arch_lines = {}
    for l in open(os.path.join(a.arch231, 'manifest.jsonl')):
        if l.strip():
            arch_lines[json.loads(l)['module']] = l.rstrip('\n')
    while True:
        env = dict(os.environ, PROD435_PFX=FAMS[0])
        r = subprocess.run([sys.executable, os.path.join(HERE, 'prod435.py'), 'merge', '--out', i230, '--pfx', *FAMS],
                           capture_output=True, text=True, env=env)
        log('merge: ' + (r.stdout.strip().splitlines() or ['?'])[-1] + (f' (exit {r.returncode})' if r.returncode else ''))
        if r.returncode != 0:
            log(r.stderr[-1500:])
            if a.once:
                sys.exit(1)
            time.sleep(a.every)
            continue
        lines = dict(arch_lines)
        bad = []
        for l in open(os.path.join(i230, 'manifest.jsonl')):
            if not l.strip():
                continue
            m = json.loads(l)['module']
            if m in lines and json.loads(lines[m])['parts']['.olean'] != json.loads(l)['parts']['.olean']:
                bad.append(m)
                continue
            lines[m] = l.rstrip('\n')
        if bad:
            log(f'{len(bad)} modules differ between the 230 families and the 231 archive: {bad[:5]}')
        os.makedirs(iface, exist_ok=True)
        link_tree(a.arch231, iface)
        link_tree(i230, iface)
        tmp = os.path.join(iface, 'manifest.jsonl.tmp')
        open(tmp, 'w').write('\n'.join(lines[m] for m in sorted(lines)) + '\n')
        os.replace(tmp, os.path.join(iface, 'manifest.jsonl'))
        have = set(lines)
        allc = {c for v in need.values() for c in v}
        miss = sorted(allc - have)
        new = [m for m, v in need.items() if all(c in have for c in v)
               and not os.path.exists(os.path.join(gb, m + '.olean'))]
        log(f'{len(allc) - len(miss)} of {len(allc)} certificates present, {len(miss)} missing; '
            f'{sum(1 for m in need if os.path.exists(os.path.join(gb, m + ".olean")))} of {len(need)} glue modules built, '
            f'{len(new)} new ready')
        open(os.path.join(W, 'missing.txt'), 'w').write('\n'.join(miss) + '\n')
        if not miss and not bad:
            log('all certificates present: full assembly')
            r = subprocess.run(asm, capture_output=True, text=True)
            open(os.path.join(W, 'assemble-final.log'), 'w').write(r.stdout + r.stderr)
            log(f'assembly exit {r.returncode}: ' + (r.stdout.strip().splitlines() or ['?'])[-1])
            sys.exit(r.returncode)
        if new:
            r = subprocess.run(asm + ['--chunks', ','.join(new)], capture_output=True, text=True)
            log(f'chunks: exit {r.returncode}, ' + next((l for l in r.stdout.splitlines() if l.startswith('glue chunks:')), '?'))
            if r.returncode != 0:
                log((r.stdout + r.stderr)[-2500:])
        if a.once:
            sys.exit(0)
        time.sleep(a.every)


if __name__ == '__main__':
    main()
