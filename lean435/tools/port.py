#!/usr/bin/env python3
"""Port 4.19 Lean sources of this repository to Lean 4.35 `module` files.

The originals are only read (work/final_lean, work/spectral[/stronger], milestones/35-231-lean/lean);
the rewritten copies go to --out (default lean435/src, not committed).

    python3 lean435/tools/port.py [--out DIR] TARGET...      # ports TARGET and its import closure

Rules (all mechanical, applied to every file):
  R1  `module` is put on the first line.
  R2  support/chain files: `import X` -> `public import X`, except certificate modules (R5), and
      `@[expose] public section` is inserted after the header, so every definition is exported with
      its body (the kernel of an importer must unfold them) and every theorem with its statement.
  R3  Cnf modules (`LocalWindowCnf.*`, `LocalWindowCtxCnf.*`): `module` only. Imports and
      declarations stay private; only the replay module sees them (`import all`).
  R4  replay modules (`LocalWindowUnsat.*`, `LocalWindowCtxUnsat.*`): `module`; the import of its Cnf
      module becomes `import all`, other imports private, plus `public import LocalWindowShareCtx`
      (ctx) and one public theorem `refuted` whose statement has literal parameters read from the
      Cnf module (`window`, `bounds`, `first`, `resolution`, `cap`).
  R5  in support/chain files, imports of certificate modules stay private (`import`), so that a
      module importing the chain never loads certificate files; and the term
      `TagsSW.refutedShareFrom_of_sat N.sat N.unsat` becomes `N.refuted`.
Manual fixes (proof repairs for 4.35 core changes) are the table FIXES below, each applied exactly
`count` times or the port fails. A manifest (sha256 of every original and every port) is written to
OUT/PORT-MANIFEST.tsv.
"""
import argparse, hashlib, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
SRC_ROOTS = ['milestones/35-231-lean/lean', 'work/final_lean', 'work/spectral/stronger', 'work/spectral']
CERT_CNF = ('LocalWindowCnf.', 'LocalWindowCtxCnf.')
CERT_REPLAY = ('LocalWindowUnsat.', 'LocalWindowCtxUnsat.')
CERT = CERT_CNF + CERT_REPLAY

# (module, old, new, count, reason)
FIXES = [
    ('LratV3', 'rw [Option.mem_toList, Option.mem_def, Option.some.injEq] at hy',
     'simp only [Option.mem_toList, Option.mem_def, Option.some.injEq] at hy', 1,
     '`Option.mem_toList` now rewrites further, so the `rw` chain no longer matches'),
    ('LocalWindowTags', 'subst this; rw [Nat.log2.eq_1]; rfl', 'subst this; rw [Nat.log2_def]; rfl', 1,
     '`Nat.log2` is now defined by fuel recursion: `Nat.log2.eq_1` has another shape'),
    ('LocalWindowTags', 'rw [Nat.log2.eq_1, lg]', 'rw [Nat.log2_def, lg]', 1,
     'same'),
    ('LocalWindowTags', '  congr 1\n  apply List.countP_congr; intro x _; simp\n',
     '  congr 1\n  try (apply List.countP_congr; intro x _; simp)\n', 1,
     '`congr 1` now closes the goal ("No goals to be solved")'),
    ('LocalWindowTagsW', '  congr 1\n  apply List.countP_congr; intro x _; simp\n',
     '  congr 1\n  try (apply List.countP_congr; intro x _; simp)\n', 1,
     'same'),
]
EXTRA_FIXES_FILE = os.path.join(HERE, 'fixes_extra.py')   # more (module, old, new, count, reason)
if os.path.exists(EXTRA_FIXES_FILE):
    _ns = {}
    exec(open(EXTRA_FIXES_FILE).read(), _ns)
    FIXES += _ns['FIXES']

# R6: renames of mathlib/core lemmas between the 4.19 mathlib and v4.35.0, applied by regex to every
# support/chain file (pattern, replacement, reason). Counts per rule are printed and kept in the manifest.
RENAMES = [
    (r'Finset\.card_sdiff (?=[\w(])', 'Finset.card_sdiff_of_subset ',
     '`Finset.card_sdiff` lost its subset hypothesis; the old statement is `card_sdiff_of_subset`'),
]
EXTRA_RENAMES_FILE = os.path.join(HERE, 'renames_extra.py')
if os.path.exists(EXTRA_RENAMES_FILE):
    _ns = {}
    exec(open(EXTRA_RENAMES_FILE).read(), _ns)
    RENAMES += _ns['RENAMES']
RENAME_COUNTS = {}

IMPORT_RX = re.compile(r'^import\s+(.*)$')


def find(m):
    rel = m.replace('.', '/') + '.lean'
    for r in SRC_ROOTS:
        p = os.path.join(ROOT, r, rel)
        if os.path.exists(p):
            return p
    return None


def split_header(text):
    """Return (lines, header_end, imports): header_end = index of the first line after the header."""
    lines = text.split('\n')
    imports, i, in_block, last_imp = [], 0, 0, -1
    while i < len(lines):
        s = lines[i].strip()
        if in_block:
            in_block += s.count('/-') - s.count('-/')
            i += 1
            continue
        if not s or s.startswith('--'):
            i += 1
            continue
        if s.startswith('/-'):
            in_block = s.count('/-') - s.count('-/')
            i += 1
            continue
        m = IMPORT_RX.match(s)
        if m:
            imports += m.group(1).split('--')[0].split()
            last_imp = i
            i += 1
            continue
        break
    return lines, last_imp + 1, imports


def closure(targets):
    seen, order, ext = {}, [], set()

    def go(m):
        if m in seen:
            return
        p = find(m)
        seen[m] = p
        if p is None:
            ext.add(m)
            return
        for i in split_header(open(p, encoding='utf-8').read())[2]:
            go(i)
        order.append(m)
    for t in targets:
        go(t)
    return order, seen, ext


def lit_def(text, name):
    m = re.search(r'^noncomputable def ' + name + r' : [^\n]*?:= (.*)$', text, re.M)
    if not m:
        raise SystemExit(f'port: no `def {name}` in Cnf module')
    return m.group(1).strip()


def apply_fixes(mod, text, used):
    for (fm, old, new, count, _why) in FIXES:
        if fm != mod:
            continue
        n = text.count(old)
        if n != count:
            raise SystemExit(f'port: fix for {mod} expected {count} match(es), found {n}: {old[:60]!r}')
        text = text.replace(old, new)
        used.append((fm, _why))
    return text


def refuted_decl(cnf_text):
    """Statement (literal parameters) and proof of the public `refuted` theorem of a certificate,
    from the parameter definitions of its Cnf part: ctx (`first`), share (`cap`), or plain."""
    has = lambda n: re.search(r'^noncomputable def ' + n + r' : ', cnf_text, re.M) is not None
    w, b = lit_def(cnf_text, 'window'), lit_def(cnf_text, 'bounds')
    if has('first'):
        return (f'RefutedShareFrom ({w}) ({b}) {lit_def(cnf_text, "resolution")} {lit_def(cnf_text, "cap")} '
                f'{lit_def(cnf_text, "first")}', 'TagsSW.refutedShareFrom_of_sat sat unsat')
    if has('cap'):
        return (f'RefutedShare ({w}) ({b}) {lit_def(cnf_text, "resolution")} {lit_def(cnf_text, "cap")}',
                'Tags.refutedShare_of_sat sat unsat')
    return f'Refuted ({w}) ({b})', 'Tags.refuted_of_sat sat unsat'


def port_support(mod, text):
    lines, hend, imports = split_header(text)
    out = ['module', '']
    for ln in lines[:hend]:
        m = IMPORT_RX.match(ln.strip())
        if m:
            for imp in m.group(1).split('--')[0].split():
                out.append(('import ' if imp.startswith(CERT) else 'public import ') + imp)
        else:
            out.append(ln)
    out += ['', '@[expose] public section', '']
    body = '\n'.join(lines[hend:])
    for (pat, rep, _why) in RENAMES:
        body, n = re.subn(pat, rep, body)
        if n:
            RENAME_COUNTS[pat] = RENAME_COUNTS.get(pat, 0) + n
    body = re.sub(r'TagsSW\.refutedShareFrom_of_sat ([\w.]+)\.sat \1\.unsat', r'\1.refuted', body)
    return '\n'.join(out) + body


def port_cnf(mod, text):
    return 'module\n\n' + text


def port_replay(mod, text, cnf_text):
    lines, hend, imports = split_header(text)
    cnf = [i for i in imports if i.startswith(CERT_CNF)]
    if len(cnf) != 1:
        raise SystemExit(f'port: {mod} imports {len(cnf)} Cnf modules')
    out = ['module', '']
    ctx = mod.startswith('LocalWindowCtxUnsat.')
    out.append('public import LocalWindowShareCtx')  # RefutedShareFrom, RefutedShare, Refuted, winOf
    for imp in imports:
        out.append(('import all ' if imp == cnf[0] else 'import ') + imp)
    body = '\n'.join(lines[hend:])
    ns = re.search(r'^namespace (\S+)\s*$', body, re.M).group(1)
    stmt, proof = refuted_decl(cnf_text)
    tail = (f'\n/-- The certificate, stated with literal parameters (lean435/tools/port.py, rule R4). -/\n'
            f'public theorem refuted : {stmt} :=\n  {proof}\n\n')
    endl = f'end {ns}'
    k = body.rstrip().rfind(endl)
    if k < 0 or body.rstrip()[k:] != endl:
        raise SystemExit(f'port: {mod} does not end with `{endl}`')
    body = body[:k] + tail.lstrip('\n') + body[k:]
    return '\n'.join(out) + '\n' + body


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', default=os.path.join(ROOT, 'lean435', 'src'))
    ap.add_argument('targets', nargs='+')
    a = ap.parse_args()
    order, seen, ext = closure(a.targets)
    bad = [e for e in ext if not e.split('.')[0] in ('Mathlib', 'Std', 'Init', 'Lean')]
    if bad:
        raise SystemExit(f'port: modules without source: {bad}')
    used, man = [], []
    for mod in order:
        p = seen[mod]
        text = open(p, encoding='utf-8').read()
        text = apply_fixes(mod, text, used)
        if mod.startswith(CERT_CNF):
            new = port_cnf(mod, text)
        elif mod.startswith(CERT_REPLAY):
            cnfmod = [i for i in split_header(text)[2] if i.startswith(CERT_CNF)][0]
            new = port_replay(mod, text, open(seen[cnfmod], encoding='utf-8').read())
        else:
            new = port_support(mod, text)
        q = os.path.join(a.out, mod.replace('.', '/') + '.lean')
        os.makedirs(os.path.dirname(q), exist_ok=True)
        if not (os.path.exists(q) and open(q, encoding='utf-8').read() == new):
            with open(q, 'w', encoding='utf-8') as f:
                f.write(new)
        man.append((mod, os.path.relpath(p, ROOT), hashlib.sha256(open(p, 'rb').read()).hexdigest(),
                    hashlib.sha256(new.encode()).hexdigest()))
    with open(os.path.join(a.out, 'PORT-MANIFEST.tsv'), 'w') as f:
        f.write('module\toriginal\tsha256_original\tsha256_port\n')
        for r in man:
            f.write('\t'.join(r) + '\n')
    print(f'ported {len(order)} modules to {a.out}; fixes applied: {len(used)}; renames: {RENAME_COUNTS}; external: {sorted(ext)}')


if __name__ == '__main__':
    main()
