#!/usr/bin/env python3
"""Final assembly and audit of a 4.35 chain from certificate interfaces (milestone 36).

    assemble435.py --tag T --chain-src S --chain-build B --glue G --iface I --manifest M [--manifest ...]
                   [--floors-src FS --floors-build FB] [--bound 232] [--chunks D0,S3,...] [--jobs 3] --work W

Inputs:
  S, B   the chain's ported sources and their local build (port.py --extra-root GEN; build.py): the
         spec layer that every public statement mentions (core, chain, mathlib);
  G      glue435.py output (chunk modules and the top module Glue6SC<T>);
  I, M   the certificate interfaces and their manifests (prod435.py merge / collect: public .olean only);
  FS, FB the floors (lean435/floors: Floors233Port), rebuilt locally.
Steps:
  1. every glue chunk module is compiled from the interfaces alone (audit.py final --out-olean: --setup
     with the public .olean of its certificates, LEAN_PATH=/nonexistent; strace checks that no
     .olean.private/.olean.server of a certificate is opened); up to --jobs at a time;
  2. the top module Glue6SC<T> is compiled the same way (it imports only glue chunks);
  3. the final module
         public theorem upper_<bound>_435 : ∀ {m : Nat}, Snake m → m ≤ <bound> :=
           upper_<bound>_of_refuted6SC<T> allRefuted6S<T> allRefutedShare6S<T> allRefutedCtx6SC<T>
             Floors233Port.floors233
     is compiled with `audit.py final` (hash checks of every interface against the manifests, spec
     layer and floors from local rebuilds, clean directory, --setup, strace) and its `#print axioms`
     must be within [propext, Classical.choice, Quot.sound].
With --chunks only those glue chunks are built and a test final file prints their axioms (step 3 is
replaced): this is how the assembly is tested before all certificates exist.
"""
import argparse, os, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))


def audit_final(a, final, name, out_olean, theorems, work, extra_pairs=()):
    cmd = [sys.executable, os.path.join(HERE, 'audit.py'), 'final',
           '--src', a.chain_src, '--spec-build', a.chain_build,
           '--src', a.glue, '--spec-build', a.glue_build]
    for s, b in extra_pairs:
        cmd += ['--src', s, '--spec-build', b]
    cmd += ['--iface', a.iface, '--final', final, '--module-name', name, '--work', work]
    for m in a.manifest:
        cmd += ['--manifest', m]
    if out_olean:
        cmd += ['--out-olean', out_olean]
    for t in theorems:
        cmd += ['--theorem', t]
    if a.require_spec_manifest:
        cmd.append('--require-spec-manifest')
    t0 = time.time()
    r = subprocess.run(cmd, capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr, time.time() - t0


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--tag', required=True)
    ap.add_argument('--chain-src', required=True)
    ap.add_argument('--chain-build', required=True)
    ap.add_argument('--glue', required=True)
    ap.add_argument('--glue-build', default=None)
    ap.add_argument('--iface', required=True)
    ap.add_argument('--manifest', action='append', required=True)
    ap.add_argument('--floors-src', default=None)
    ap.add_argument('--floors-build', default=None)
    ap.add_argument('--bound', type=int, default=232)
    ap.add_argument('--chunks', default=None)
    ap.add_argument('--jobs', type=int, default=3)
    ap.add_argument('--require-spec-manifest', action='store_true')
    ap.add_argument('--work', required=True)
    a = ap.parse_args()
    for k in ('chain_src', 'chain_build', 'glue', 'iface', 'work'):
        setattr(a, k, os.path.abspath(getattr(a, k)))
    a.glue_build = os.path.abspath(a.glue_build or os.path.join(a.work, 'glue-build'))
    T = a.tag
    os.makedirs(a.work, exist_ok=True)
    mods = sorted(f[:-5] for f in os.listdir(a.glue) if f.endswith('.lean') and f.startswith(f'Glue6SC{T}')
                  and f != f'Glue6SC{T}.lean')
    if a.chunks:
        want = {f'Glue6SC{T}{c}' for c in a.chunks.split(',')}
        mods = [m for m in mods if m in want]
    log = open(os.path.join(a.work, 'assemble.log'), 'a')

    def one(m):
        out = os.path.join(a.glue_build, m + '.olean')
        if os.path.exists(out):
            return m, 0, 'up to date', 0.0
        code, txt, secs = audit_final(a, os.path.join(a.glue, m + '.lean'), m, out, [], os.path.join(a.work, 'w', m))
        return m, code, txt, secs
    t0 = time.time()
    fails = []
    m, code, txt, secs = one('Glue435')                 # the lemma module (imports only the spec layer)
    if code != 0:
        print(f'FAILED Glue435:\n{txt[-2500:]}')
        sys.exit(1)
    with ThreadPoolExecutor(a.jobs) as ex:
        for m, code, txt, secs in ex.map(one, mods):
            log.write(f'== {m} exit {code} {secs:.1f} s\n{txt}\n')
            if code != 0:
                fails.append(m)
                print(f'FAILED {m}:\n{txt[-2500:]}', flush=True)
            else:
                print(f'ok {m} ({secs:.1f} s)', flush=True)
    print(f'glue chunks: {len(mods) - len(fails)} of {len(mods)} built in {time.time() - t0:.0f} s')
    if fails:
        sys.exit(1)
    pairs = [(a.floors_src, a.floors_build)] if a.floors_src else []
    if a.chunks:
        fin = os.path.join(a.work, f'GlueTest{T}.lean')
        names = []
        for m in mods:
            nm = open(os.path.join(a.glue, m + '.lean')).read().split('public theorem ')[1].split(' :')[0]
            names.append('Snake9.LocalWindow.' + nm)
        open(fin, 'w').write('module\n' + ''.join(f'import {m}\n' for m in mods) +
                             ''.join(f'#print axioms {n}\n' for n in names))
        code, txt, secs = audit_final(a, fin, f'GlueTest{T}', None, names, os.path.join(a.work, 'w', 'test'))
        print(txt)
        sys.exit(code)
    top = f'Glue6SC{T}'
    out = os.path.join(a.glue_build, top + '.olean')
    if not os.path.exists(out):
        code, txt, secs = audit_final(a, os.path.join(a.glue, top + '.lean'), top, out, [], os.path.join(a.work, 'w', top))
        log.write(f'== {top} exit {code} {secs:.1f} s\n{txt}\n')
        if code != 0:
            print(f'FAILED {top}:\n{txt[-2500:]}')
            sys.exit(1)
        print(f'ok {top} ({secs:.1f} s)')
    B = a.bound
    fin = os.path.join(a.work, f'UpperBound{B}_435.lean')
    thm = f'Snake9.upper_{B}_435'
    open(fin, 'w').write('\n'.join([
        'module', '', f'import AggregateDirection6SC{T}', f'import {top}', 'import Floors233Port', '',
        f'/-! The bound {B} in Lean 4.35, assembled from certificate interfaces (lean435/tools/assemble435.py). -/',
        '', 'namespace Snake9', '',
        f'public theorem upper_{B}_435 : ∀ {{m : Nat}}, Snake m → m ≤ {B} :=',
        f'  upper_{B}_of_refuted6SC{T} LocalWindow.allRefuted6S{T} LocalWindow.allRefutedShare6S{T}',
        f'    LocalWindow.allRefutedCtx6SC{T} Floors233Port.floors233', '',
        'end Snake9', '', f'#print axioms {thm}', '']))
    code, txt, secs = audit_final(a, fin, f'UpperBound{B}_435', None, [thm], os.path.join(a.work, 'w', 'final'), pairs)
    print(txt)
    open(os.path.join(a.work, 'final-audit.txt'), 'w').write(txt)
    sys.exit(code)


if __name__ == '__main__':
    main()
