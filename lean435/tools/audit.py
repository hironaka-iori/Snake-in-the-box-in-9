#!/usr/bin/env python3
"""Interface-only final audit for Lean 4.35 module builds (procedure of
milestones/35-231-lean/MODULE-SPIKE.md, "Smallest audit procedure").

Worker side (the machine that kernel-checks a certificate):

    audit.py manifest --src S --build B --out M.jsonl MODULE...
        one json line per module: source sha256 and the sha256 of every output part
        (.olean, .olean.server, .olean.private, .ir, .ir.sig).
    audit.py publish --build B --manifest M.jsonl --iface DIR MODULE...
        copies only the public .olean of each MODULE to DIR (this is what goes through git).

Audit side:

    audit.py final --src S --spec-build B2 --iface DIR --manifest M.jsonl [--manifest ...]
                   --final FILE.lean --theorem NAME... [--work W]
      1. the spec/support layer (every module the final file loads that is not in DIR) must have been
         rebuilt from source into B2 (build.py); its public .olean must have the sha256 the worker
         manifests give (determinism check: closes the stale-specification hazard);
      2. every interface .olean in DIR must have the sha256 of its manifest line;
      3. a clean directory W/olean is made with hard links of exactly the public .olean files the
         final file loads (followed through exported imports only) and nothing else;
      4. FILE.lean is compiled with LEAN_PATH=/nonexistent and a --setup JSON whose importArts lists
         those files (olean only, no .olean.server/.olean.private/.ir), under strace when available,
         which records every file the process opened;
      5. `#print axioms` of each NAME must be a subset of [propext, Classical.choice, Quot.sound].
      Exit 0 only if all checks pass; prints AUDIT PASSED / AUDIT FAILED with the reasons.
"""
import argparse, hashlib, json, os, re, shutil, subprocess, sys, time

LEAN = '/opt/lean-4.35.0-linux/bin/lean'
PARTS = ('.olean', '.olean.server', '.olean.private', '.ir', '.ir.sig')
WHITELIST = {'propext', 'Classical.choice', 'Quot.sound'}
IMP = re.compile(r'^(public\s+)?(meta\s+)?import\s+(all\s+)?([\w.]+)')


def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def header(path):
    """[(module, exported, meta, all)] of a source header."""
    out, blk = [], 0
    for line in open(path, encoding='utf-8'):
        s = line.strip()
        if blk:
            blk += s.count('/-') - s.count('-/')
            continue
        if not s or s.startswith('--') or s in ('module', 'prelude'):
            continue
        if s.startswith('/-'):
            blk = s.count('/-') - s.count('-/')
            continue
        m = IMP.match(s)
        if not m:
            break
        out.append((m.group(4), bool(m.group(1)), bool(m.group(2)), bool(m.group(3))))
    return out


def rel(m):
    return m.replace('.', '/')


def mathlib_roots(mathlib):
    roots = [(mathlib, os.path.join(mathlib, '.lake/build/lib/lean'))]
    pk = os.path.join(mathlib, '.lake/packages')
    for p in sorted(os.listdir(pk)) if os.path.isdir(pk) else []:
        roots.append((os.path.join(pk, p), os.path.join(pk, p, '.lake/build/lib/lean')))
    return roots


class Resolver:
    """Where the source and the build outputs of a module are."""

    def __init__(self, src, spec_build, iface, mathlib):
        self.src, self.spec, self.iface = src, spec_build, iface
        self.ml = mathlib_roots(mathlib)
        self.core = os.path.join(os.path.dirname(os.path.dirname(LEAN)), 'lib', 'lean')

    def locate(self, m):
        """-> (kind, source or None, olean path)"""
        if self.iface and os.path.exists(os.path.join(self.iface, rel(m) + '.olean')):
            s = os.path.join(self.src, rel(m) + '.lean')
            return 'iface', (s if os.path.exists(s) else None), os.path.join(self.iface, rel(m) + '.olean')
        s = os.path.join(self.src, rel(m) + '.lean')
        if os.path.exists(s):
            return 'spec', s, os.path.join(self.spec, rel(m) + '.olean')
        for sroot, broot in self.ml:
            s = os.path.join(sroot, rel(m) + '.lean')
            if os.path.exists(s):
                return 'mathlib', s, os.path.join(broot, rel(m) + '.olean')
        o = os.path.join(self.core, rel(m) + '.olean')
        if os.path.exists(o):
            return 'core', None, o
        raise SystemExit(f'audit: cannot locate module {m}')


def loaded_closure(res, root_imports):
    """Modules the loader visits: the root's imports, then exported imports transitively.
    For an interface module with no source here, its imports are read from the manifest."""
    seen, order = {}, []
    stack = [m for (m, *_r) in root_imports]
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        kind, s, o = res.locate(m)
        seen[m] = (kind, o)
        order.append(m)
        if kind == 'core':
            continue  # core (Init/Std/Lean) is read from the toolchain itself
        if s is None:
            imps = res.manifest_imports.get(m)
            if imps is None:
                raise SystemExit(f'audit: no source and no manifest header for {m}')
        else:
            imps = header(s)
        for (i, exported, _meta, _all) in imps:
            if exported:
                stack.append(i)
    return order, seen


def cmd_manifest(a):
    with open(a.out, 'a') as f:
        for m in a.modules:
            s = os.path.join(a.src, rel(m) + '.lean')
            o = os.path.join(a.build, rel(m))
            rec = dict(module=m, source_sha256=sha(s),
                       parts={e: sha(o + e) for e in PARTS if os.path.exists(o + e)},
                       sizes={e: os.path.getsize(o + e) for e in PARTS if os.path.exists(o + e)},
                       imports=header(s), lean=subprocess.run([LEAN, '--version'], capture_output=True,
                                                              text=True).stdout.strip())
            f.write(json.dumps(rec) + '\n')
    print(f'manifest: {len(a.modules)} lines -> {a.out}')


def cmd_publish(a):
    man = load_manifests(a.manifest)
    for m in a.modules:
        src = os.path.join(a.build, rel(m) + '.olean')
        if sha(src) != man[m]['parts']['.olean']:
            raise SystemExit(f'publish: {m}.olean differs from its manifest line')
        dst = os.path.join(a.iface, rel(m) + '.olean')
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        shutil.copyfile(src, dst)
    print(f'published {len(a.modules)} interface files to {a.iface}')


def load_manifests(paths):
    man = {}
    for p in paths:
        for line in open(p):
            r = json.loads(line)
            man[r['module']] = r  # later lines win (rebuilds)
    return man


def cmd_final(a):
    t0 = time.time()
    fails = []
    man = load_manifests(a.manifest)
    res = Resolver(os.path.abspath(a.src), os.path.abspath(a.spec_build), os.path.abspath(a.iface),
                   os.path.abspath(a.mathlib))
    res.manifest_imports = {m: [tuple(x) for x in r['imports']] for m, r in man.items()}
    order, seen = loaded_closure(res, header(a.final))
    kinds = {}
    for m in order:
        kinds.setdefault(seen[m][0], []).append(m)
    print('loaded modules: ' + ', '.join(f'{k} {len(v)}' for k, v in sorted(kinds.items())))
    # 1-2: hashes
    nspec = nif = 0
    for m in order:
        kind, o = seen[m]
        if kind == 'iface':
            nif += 1
            if m not in man:
                fails.append(f'interface {m} has no manifest line')
            elif sha(o) != man[m]['parts']['.olean']:
                fails.append(f'interface {m}.olean: sha256 differs from manifest')
        elif kind == 'spec':
            if not os.path.exists(o):
                fails.append(f'spec module {m} was not rebuilt into {a.spec_build}')
                continue
            nspec += 1
            if m in man and sha(o) != man[m]['parts']['.olean']:
                fails.append(f'spec module {m}: local rebuild .olean differs from worker manifest')
            elif m not in man and a.require_spec_manifest:
                fails.append(f'spec module {m}: no worker manifest line to compare with')
    print(f'hash checks: {nif} interface files, {nspec} locally rebuilt spec modules')
    # 3: clean directory of public .olean files only
    w = os.path.abspath(a.work)
    od = os.path.join(w, 'olean')
    if os.path.exists(od):
        shutil.rmtree(od)
    arts = {}
    nbytes = 0
    for m in order:
        kind, o = seen[m]
        if kind == 'core':
            continue
        d = os.path.join(od, rel(m) + '.olean')
        os.makedirs(os.path.dirname(d), exist_ok=True)
        try:
            os.link(o, d)
        except OSError:
            shutil.copyfile(o, d)
        nbytes += os.path.getsize(d)
        arts[m] = [[d], []]
    # core modules: the toolchain's own files (lake lists them the same way)
    for m in order:
        kind, o = seen[m]
        if kind == 'core':
            arts[m] = [[o], []]
    leftovers = [f for r, _, fs in os.walk(od) for f in fs if not f.endswith('.olean')]
    assert not leftovers
    name = os.path.splitext(os.path.basename(a.final))[0]
    setup = dict(name=name, isModule=True, importArts=arts)
    sp = os.path.join(w, 'setup.json')
    json.dump(setup, open(sp, 'w'))
    print(f'setup: {len(arts)} import artifacts, {sum(1 for m in arts if seen[m][0] != "core")} public .olean '
          f'files outside the toolchain ({nbytes / 1e6:.1f} MB)')
    # 4: compile
    env = dict(os.environ, LEAN_PATH='/nonexistent')
    cmd = [LEAN, '--setup', sp, a.final]
    tr = os.path.join(w, 'strace.txt')
    if shutil.which('strace') and not a.no_strace:
        cmd = ['strace', '-f', '-qq', '-e', 'trace=openat,open', '-o', tr] + cmd
    t1 = time.time()
    p = subprocess.run(cmd, capture_output=True, text=True, env=env, cwd=w)
    wall = time.time() - t1
    out = p.stdout + p.stderr
    open(os.path.join(w, 'final.out'), 'w').write(out)
    print(out.strip())
    if p.returncode != 0:
        fails.append(f'final module failed (exit {p.returncode})')
    if os.path.exists(tr) and not a.no_strace:
        opened = set()
        for line in open(tr):
            mm = re.search(r'open(?:at)?\(.*?"([^"]+)"', line)
            if mm and '= -1' not in line and mm.group(1).endswith(PARTS):
                opened.add(os.path.realpath(mm.group(1)))
        outside = sorted(f for f in opened if not f.startswith(os.path.realpath(od) + '/')
                         and not f.startswith(os.path.realpath(res.core) + '/'))
        bad_parts = sorted(f for f in opened if not f.endswith('.olean'))
        print(f'strace: {len(opened)} Lean data files opened; outside the clean directory and the '
              f'toolchain: {len(outside)}; non-.olean parts: {len(bad_parts)}')
        if outside:
            fails.append('opened files outside the clean directory: ' + ', '.join(outside[:5]))
        if bad_parts:
            fails.append('opened non-public parts: ' + ', '.join(bad_parts[:5]))
    # 5: axioms
    for t in a.theorem:
        mm = re.search(r"'" + re.escape(t) + r"' (does not depend on any axioms|depends on axioms: \[(.*?)\])",
                       out, re.S)
        if not mm:
            fails.append(f'no `#print axioms` output for {t}')
            continue
        ax = set() if mm.group(2) is None else {x.strip() for x in mm.group(2).replace('\n', ' ').split(',')}
        extra = sorted(ax - WHITELIST)
        print(f'axioms of {t}: {sorted(ax)}' + (f'  NOT IN WHITELIST: {extra}' if extra else '  (whitelist ok)'))
        if extra:
            fails.append(f'{t} depends on axioms outside the whitelist: {extra}')
    print(f'final compile {wall:.1f} s; audit {time.time() - t0:.1f} s')
    if fails:
        print('AUDIT FAILED:\n  ' + '\n  '.join(fails))
        sys.exit(1)
    print('AUDIT PASSED')


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    p = sub.add_parser('manifest')
    p.add_argument('--src', required=True)
    p.add_argument('--build', required=True)
    p.add_argument('--out', required=True)
    p.add_argument('modules', nargs='+')
    p = sub.add_parser('publish')
    p.add_argument('--build', required=True)
    p.add_argument('--manifest', action='append', required=True)
    p.add_argument('--iface', required=True)
    p.add_argument('modules', nargs='+')
    p = sub.add_parser('final')
    p.add_argument('--src', required=True)
    p.add_argument('--spec-build', required=True)
    p.add_argument('--iface', required=True)
    p.add_argument('--manifest', action='append', required=True)
    p.add_argument('--mathlib', default=os.path.expanduser('~/l435/mathlib4'))
    p.add_argument('--final', required=True)
    p.add_argument('--theorem', action='append', required=True)
    p.add_argument('--work', required=True)
    p.add_argument('--require-spec-manifest', action='store_true')
    p.add_argument('--no-strace', action='store_true')
    a = ap.parse_args()
    {'manifest': cmd_manifest, 'publish': cmd_publish, 'final': cmd_final}[a.cmd](a)


if __name__ == '__main__':
    main()
