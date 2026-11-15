#!/usr/bin/env python3
"""Port the floor closure (FLOORS.md) to Lean 4.35 `module` files.

    python3 -I lean435/floors/tools/port_floors.py ORIG SRC

ORIG is the output of fetch.py (4.19 sources, verified by git blob sha). SRC gets:
- the 19 branch modules and the closure of `Floors233Bridge` (23 modules, no certificate):
  ported by the port lead's lean435/tools/port.py (rules R1/R2, its fix table), run with --out SRC;
  the 19 branch sources it reads are checked to be byte-identical to ORIG;
- the 1,042 main modules: rule F1 below plus the fix table fixes_floors.py;
- `Floors233Port` from lean435/floors/src (hand-written bridge).
Rule F1 (main modules): `module` on the first line, every `import X` -> `public import X`, and
`@[expose] public section` after the header. Inside the floor closure every definition is
exported with its body, because the kernel checks (`decide +kernel`, `rfl`) of later modules
unfold data defined in earlier ones, as in 4.19. The data boundary is `Floors233Port`: it imports
the five floor modules privately (`import`), so a module that imports `Floors233Port` loads none
of the 1,042 floor modules, only the statement of `floors233`.
Writes SRC/FLOORS-PORT-MANIFEST.tsv (module, kind, sha256 of original, sha256 of port).
"""
import hashlib, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, os.path.join(REPO, 'lean435', 'tools'))
import port as PL   # the port lead's rewriter, used as a library (split_header, find)

orig, out = os.path.abspath(sys.argv[1]), os.path.abspath(sys.argv[2])
ns = {}
exec(open(os.path.join(HERE, 'fixes_floors.py')).read(), ns)
FIXES = ns['FIXES']
rel = lambda m: m.replace('.', '/') + '.lean'
sha = lambda b: hashlib.sha256(b).hexdigest()

rows = [l.split('\t') for l in open(os.path.join(orig, 'FETCH-MANIFEST.tsv')).read().splitlines()[1:]]
branch = [r[0] for r in rows if not r[1].startswith('main:')]
main = [r[0] for r in rows if r[1].startswith('main:')]
assert len(branch) == 19 and len(main) == 1042, (len(branch), len(main))

# 1. branch modules + Floors233Bridge closure: the port lead's port.py
subprocess.run([sys.executable, '-I', os.path.join(REPO, 'lean435/tools/port.py'), '--out', out,
                'Floors233Bridge'] + branch, check=True)
man = []
for m in branch:
    p = PL.find(m)
    assert open(p, 'rb').read() == open(os.path.join(orig, rel(m)), 'rb').read(), m
for l in open(os.path.join(out, 'PORT-MANIFEST.tsv')).read().splitlines()[1:]:
    m, _o, so, sp = l.split('\t')
    man.append((m, 'port.py', so, sp))

# 2. main modules: rule F1 + fixes
used = {}
for m in main:
    text = open(os.path.join(orig, rel(m)), encoding='utf-8').read().replace('\r\n', '\n')
    for (fm, old, new, count, _why) in FIXES:
        if fm == m:
            n = text.count(old)
            if n != count:
                raise SystemExit(f'fix for {m}: expected {count} match(es), found {n}: {old[:60]!r}')
            text = text.replace(old, new)
            used[(fm, old)] = n
    lines, hend, imports = PL.split_header(text)
    hdr = ['module', '']
    for ln in lines[:hend]:
        mm = PL.IMPORT_RX.match(ln.strip())
        if mm:
            hdr += ['public import ' + i for i in mm.group(1).split('--')[0].split()]
        else:
            hdr.append(ln)
    new = '\n'.join(hdr) + '\n\n@[expose] public section\n\n' + '\n'.join(lines[hend:])
    q = os.path.join(out, rel(m))
    os.makedirs(os.path.dirname(q), exist_ok=True)
    b = new.encode()
    if not (os.path.exists(q) and open(q, 'rb').read() == b):
        open(q, 'wb').write(b)
    man.append((m, 'F1' + ('+fix' if any(f[0] == m for f in FIXES) else ''),
                sha(open(os.path.join(orig, rel(m)), 'rb').read()), sha(b)))
missing = [f for f in FIXES if (f[0], f[1]) not in used]
assert not missing, missing

# 3. hand-written modules of lean435/floors/src
for f in sorted(os.listdir(os.path.join(REPO, 'lean435/floors/src'))):
    if f.endswith('.lean'):
        b = open(os.path.join(REPO, 'lean435/floors/src', f), 'rb').read()
        open(os.path.join(out, f), 'wb').write(b)
        man.append((f[:-5], 'hand-written', sha(b), sha(b)))
with open(os.path.join(out, 'FLOORS-PORT-MANIFEST.tsv'), 'w') as f:
    f.write('module\tkind\tsha256_original\tsha256_port\n')
    for r in sorted(man):
        f.write('\t'.join(r) + '\n')
print(f'{len(man)} modules in {out}: {sum(1 for r in man if r[1] == "port.py")} by port.py, '
      f'{len(main)} by rule F1, {len(used)} fixes applied')
