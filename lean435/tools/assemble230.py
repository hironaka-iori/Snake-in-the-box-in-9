#!/usr/bin/env python3
"""Final assembly and audit of the bound 230 (K7 route, milestone 37) from certificate interfaces.

    assemble230.py --spec-src S --spec-build B --glue G --iface I --manifest M [--manifest ...]
                   --work W [--jobs 3] [--chunks G230_0_0,G230S,...] [--conditional]

Inputs:
  S, B   the spec layer, ported/copied sources and their local build (c230chain.sh: core stack, the
         ported K7 chain, the main-line modules it needs, lean435/c230/*.lean and the generated spec
         modules of c230gen.py: keys, row checks, shape covers);
  G      c230gen.py's glue directory (G230_<i>_<k>, G230S, G230);
  I, M   certificate interfaces and their manifests (prod435.py merge: public .olean only), i.e. the
         230 families (xfer/c230, c230help, c230split finals) and the 231 families for the 10,086
         reused 231 certificates (archive branch research/c435-interfaces-231).
Steps (as assemble435.py):
  1. every glue chunk (G230_*, G230S) is compiled from the interfaces alone (audit.py final
     --out-olean: --setup with the public .olean of its certificates only, LEAN_PATH=/nonexistent,
     strace: no .olean.private/.olean.server of a certificate is opened, every interface hash-checked);
  2. the top glue module G230 is compiled the same way (it imports only glue chunks);
  3. the final module UpperBound230_435:
         public theorem upper_230_435 : ∀ {m : Nat}, Snake m → m ≤ 230 :=
           upper_230_of_refutedK7 LocalWindow.allTab230 LocalWindow.allShare230
     is compiled with `audit.py final` and `#print axioms Snake9.upper_230_435` must be within
     [propext, Classical.choice, Quot.sound].
Test modes (before all certificates exist):
  --chunks M1,M2,...   only these glue modules, then a test file printing their axioms;
  --conditional        no glue at all: the final-audit machinery on the spec layer, with the theorem
                       `upper_230_of_refutedK7 : AllTab tab230 → AllShareL shares230 → ∀ m, Snake m → m ≤ 230`
                       (the two premises are what the glue proves).
"""
import argparse, os, subprocess, sys, time, json
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
WL = 'AUDIT PASSED'


def audit_final(a, final, name, out_olean, theorems, work):
    cmd = [sys.executable, os.path.join(HERE, 'audit.py'), 'final']
    for s, b in zip(a.spec_src, a.spec_build):
        cmd += ['--src', s, '--spec-build', b]
    cmd += ['--src', a.glue, '--spec-build', a.glue_build,
            '--iface', a.iface, '--final', final, '--module-name', name, '--work', work]
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
    ap.add_argument('--spec-src', action='append', required=True)
    ap.add_argument('--spec-build', action='append', required=True)
    ap.add_argument('--glue', required=True)
    ap.add_argument('--glue-build', default=None)
    ap.add_argument('--iface', required=True)
    ap.add_argument('--manifest', action='append', required=True)
    ap.add_argument('--chunks', default=None)
    ap.add_argument('--conditional', action='store_true')
    ap.add_argument('--jobs', type=int, default=3)
    ap.add_argument('--require-spec-manifest', action='store_true')
    ap.add_argument('--work', required=True)
    a = ap.parse_args()
    a.spec_src = [os.path.abspath(x) for x in a.spec_src]
    a.spec_build = [os.path.abspath(x) for x in a.spec_build]
    for k in ('glue', 'iface', 'work'):
        setattr(a, k, os.path.abspath(getattr(a, k)))
    a.glue_build = os.path.abspath(a.glue_build or os.path.join(a.work, 'glue-build'))
    os.makedirs(a.work, exist_ok=True)
    os.makedirs(a.glue_build, exist_ok=True)
    log = open(os.path.join(a.work, 'assemble.log'), 'a')
    if a.conditional:
        fin = os.path.join(a.work, 'Conditional230_435.lean')
        thm = 'Snake9.upper_230_of_refutedK7'
        open(fin, 'w').write('\n'.join([
            'module', '', 'public import C230Final', '',
            '/-! The 230 theorem with its two certificate premises (lean435/tools/assemble230.py --conditional). -/', '',
            f'#print axioms {thm}', '#print axioms Snake9.C230.walk230', '#print axioms Snake9.C230.window_share', '']))
        code, txt, secs = audit_final(a, fin, 'Conditional230_435', None,
                                      [thm, 'Snake9.C230.walk230', 'Snake9.C230.window_share'], os.path.join(a.work, 'w', 'cond'))
        print(txt)
        open(os.path.join(a.work, 'conditional-audit.txt'), 'w').write(txt)
        sys.exit(code)
    mods = sorted(f[:-5] for f in os.listdir(a.glue) if f.endswith('.lean') and f.startswith('G230')
                  and f != 'G230.lean')
    if a.chunks:
        want = set(a.chunks.split(','))
        mods = [m for m in mods if m in want]

    def one(m):
        out = os.path.join(a.glue_build, m + '.olean')
        if os.path.exists(out):
            return m, 0, 'up to date', 0.0
        code, txt, secs = audit_final(a, os.path.join(a.glue, m + '.lean'), m, out, [], os.path.join(a.work, 'w', m))
        if code != 0 and os.path.exists(out):
            os.remove(out)
        return m, code, txt, secs
    t0 = time.time()
    fails = []
    with ThreadPoolExecutor(a.jobs) as ex:
        for m, code, txt, secs in ex.map(one, mods):
            log.write(f'== {m} exit {code} {secs:.1f} s\n{txt}\n')
            log.flush()
            if code != 0:
                fails.append(m)
                print(f'FAILED {m}:\n{txt[-2500:]}', flush=True)
            else:
                print(f'ok {m} ({secs:.1f} s)', flush=True)
    print(f'glue chunks: {len(mods) - len(fails)} of {len(mods)} built in {time.time() - t0:.0f} s', flush=True)
    if fails:
        sys.exit(1)
    if a.chunks:
        fin = os.path.join(a.work, 'GlueTest230.lean')
        names = []
        for m in mods:
            nm = open(os.path.join(a.glue, m + '.lean')).read().split('public theorem ')[1].split(' :')[0]
            names.append('Snake9.LocalWindow.' + nm)
        open(fin, 'w').write('module\n' + ''.join(f'import {m}\n' for m in mods) +
                             ''.join(f'#print axioms {n}\n' for n in names))
        code, txt, secs = audit_final(a, fin, 'GlueTest230', None, names, os.path.join(a.work, 'w', 'test'))
        print(txt)
        sys.exit(code)
    top = 'G230'
    out = os.path.join(a.glue_build, top + '.olean')
    if not os.path.exists(out):
        code, txt, secs = audit_final(a, os.path.join(a.glue, top + '.lean'), top, out, [], os.path.join(a.work, 'w', top))
        log.write(f'== {top} exit {code} {secs:.1f} s\n{txt}\n')
        if code != 0:
            if os.path.exists(out):
                os.remove(out)
            print(f'FAILED {top}:\n{txt[-2500:]}')
            sys.exit(1)
        print(f'ok {top} ({secs:.1f} s)')
    fin = os.path.join(a.work, 'UpperBound230_435.lean')
    thm = 'Snake9.upper_230_435'
    open(fin, 'w').write('\n'.join([
        # the statement mentions `Snake`: Snake9 is a public import; the rest is used in the proof only
        'module', '', 'public import Snake9', 'import C230Final', f'import {top}', '',
        '/-! The bound 230 in Lean 4.35 (K7 route), assembled from certificate interfaces (lean435/tools/assemble230.py). -/',
        '', 'namespace Snake9', '',
        'public theorem upper_230_435 : ∀ {m : Nat}, Snake m → m ≤ 230 :=',
        '  upper_230_of_refutedK7 LocalWindow.allTab230 LocalWindow.allShare230', '',
        'end Snake9', '', f'#print axioms {thm}', '']))
    code, txt, secs = audit_final(a, fin, 'UpperBound230_435', None, [thm], os.path.join(a.work, 'w', 'final'))
    print(txt)
    open(os.path.join(a.work, 'final-audit.txt'), 'w').write(txt)
    sys.exit(code)


if __name__ == '__main__':
    main()
