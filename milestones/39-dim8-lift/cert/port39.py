#!/usr/bin/env python3
"""Port the milestone-39 Lean files to Lean 4.35 `module` files (the rules of lean435/tools/port.py).

    python3 cert/port39.py OUT TARGET...     # ports TARGET and its import closure into OUT, prints build order

Rules: R1 `module` on the first line; R2 `import X` -> `public import X` and `@[expose] public section`
after the header, so every definition is exported with its body and every theorem with its statement.
`import Snake9Core` becomes `import Snake9` (the audited definition). LocalWindowModel, LratV3 and Snake9 are taken from lean435/tools/port.py (run into OUT first). Generated
certificate modules are written in module form by make_cert.py and are not handled here.
"""
import os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__)); LEAN = os.path.join(HERE, '..', 'lean')
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
out = sys.argv[1]; targets = sys.argv[2:]
EXTERNAL = {'Std', 'LocalWindowModel', 'LratV3', 'Snake9'}
# the audited definitions: Snake9Core is the verbatim definition block of work/final_lean/Snake9.lean
RENAME = {'Snake9Core': 'Snake9'}
os.makedirs(out, exist_ok=True)
order, seen = [], set()
def src(m):
    for d in (LEAN, os.path.join(LEAN, 'gen')):
        p = os.path.join(d, m.replace('.', '/') + '.lean')
        if os.path.exists(p): return p
    raise SystemExit('no source for ' + m)
def visit(m):
    m = RENAME.get(m, m)
    if m in seen or m in EXTERNAL: return
    seen.add(m); t = open(src(m)).read()
    imps = re.findall(r'^import\s+(\S+)', t, re.M)
    for i in imps: visit(i)
    lines = t.split('\n'); k = 0
    while k < len(lines) and (lines[k].startswith('import ') or not lines[k].strip()): k += 1
    hdr = ['public import ' + RENAME.get(l.split()[1], l.split()[1]) for l in lines[:k] if l.startswith('import ')]
    body = '\n'.join(lines[k:])
    p = os.path.join(out, m.replace('.', '/') + '.lean'); os.makedirs(os.path.dirname(p), exist_ok=True)
    open(p, 'w').write('module\n\n' + '\n'.join(hdr) + '\n\n@[expose] public section\n\n' + body)
    order.append(m)
for t in targets: visit(t)
print(' '.join(order))
