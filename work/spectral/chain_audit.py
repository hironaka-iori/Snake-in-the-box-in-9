"""Compile the mathlib-side chain up to one target module and print the axioms of the
given theorems, against the ALREADY BUILT core in work/final_lean/.lake.

This is the cheap counterpart of verify_strengthened.py (which copies and rebuilds the
whole core from scratch): one Lean process at a time, the same `lake env lean --root
-o` invocation, no solver output enters the build.  Used for the 241 and 239 audits
(outputs/upper-bound-24*-audit-linux.log).

  python3 work/spectral/chain_audit.py --mathlib-dir ~/lean-deps/mathlib4 \
      --target UpperBound239 --log outputs/upper-bound-239-audit-linux.log \
      --axioms Snake9.upper_bound_239 Snake9.verified_interval_191_239
"""
import argparse, os, re, resource, shutil, subprocess, sys, time
from pathlib import Path

SPECTRAL = Path(__file__).resolve().parent
CORE = SPECTRAL.parent / 'final_lean'
PIN = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def src(mod):
    for p in (SPECTRAL / 'stronger' / (mod + '.lean'), SPECTRAL / (mod + '.lean')):
        if p.exists():
            return p
    return None


def order(target):
    """Chain modules in dependency order (core and Mathlib imports are leaves)."""
    seen, out = set(), []

    def visit(m):
        if m in seen:
            return
        seen.add(m)
        p = src(m)
        if p is None:
            if not (CORE / (m.replace('.', '/') + '.lean')).exists() \
                    and not m.startswith(('Mathlib', 'Std', 'Lean', 'Init')):
                raise SystemExit(f'unknown module {m}')
            return
        for d in re.findall(r'^import\s+(\S+)', p.read_text(), re.M):
            visit(d)
        out.append(m)
    visit(target)
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--mathlib-dir', required=True, type=Path)
    ap.add_argument('--target', required=True)
    ap.add_argument('--axioms', nargs='+', required=True)
    ap.add_argument('--log', required=True)
    ap.add_argument('--build-dir', default=str(SPECTRAL / '.verification' / 'chain'),
                    help='where the chain .olean files go')
    ap.add_argument('--reuse', action='store_true',
                    help='skip modules whose .olean in the build dir is newer than their source '
                         '(development only; a clean audit recompiles everything)')
    a = ap.parse_args()
    mathlib = a.mathlib_dir.resolve()
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=mathlib, text=True).strip()
    if head != PIN:
        raise SystemExit(f'expected mathlib {PIN}, found {head}')
    lake = shutil.which('lake')
    if lake is None:
        raise SystemExit('lake not on PATH')
    build = Path(a.build_dir).resolve()
    build.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join([str(CORE / '.lake/build/lib/lean'), str(build)])
    log = open(a.log, 'a')

    def out(s):
        print(s, flush=True); log.write(s + '\n'); log.flush()
    mods = order(a.target)
    version = subprocess.check_output([lake, 'env', 'lean', '--version'], cwd=mathlib, text=True).strip()
    out(f'# chain to {a.target}: {len(mods)} modules; {version}; mathlib {head}')
    t0 = time.time()
    for m in mods:
        shutil.copy2(src(m), build / (m + '.lean'))
        olean = build / (m + '.olean')
        if a.reuse and olean.exists() and olean.stat().st_mtime > src(m).stat().st_mtime:
            out(f'{m}: reused')
            continue
        t = time.time()
        r = subprocess.run([lake, 'env', 'lean', f'--root={build}', '-o', str(build / (m + '.olean')),
                            str(build / (m + '.lean'))], cwd=mathlib, env=env, capture_output=True, text=True)
        rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
        rss = rss / 2**20 if sys.platform != 'darwin' else rss / 2**30
        bad = r.returncode or "declaration uses 'sorry'" in r.stdout
        out(f'{m}: {"FAILED" if bad else "ok"} {time.time() - t:.0f}s (max child RSS so far {rss:.2f} GB)')
        if bad:
            out(r.stdout[-5000:] + r.stderr[-2000:])
            sys.exit(1)
    audit = build / ('Audit_' + a.target + '.lean')
    audit.write_text(f'import {a.target}\n' + ''.join(f'#print axioms {x}\n' for x in a.axioms))
    r = subprocess.run([lake, 'env', 'lean', f'--root={build}', str(audit)], cwd=mathlib, env=env,
                       capture_output=True, text=True)
    out((r.stdout + r.stderr).strip())
    out(f'# chain wall time {time.time() - t0:.0f}s; exit {r.returncode}')
    found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", r.stdout)
    ok = r.returncode == 0 and len(found) == len(a.axioms) and all(
        {x.strip() for x in raw.split(',')} <= ALLOWED for _, raw in found)
    out('# AXIOM AUDIT ' + ('PASSED' if ok else 'FAILED'))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
