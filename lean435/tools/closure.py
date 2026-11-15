#!/usr/bin/env python3
"""Import closure of Lean modules over the repository's source roots (4.19 sources).
Usage: closure.py MODULE... ; prints 'module<TAB>path' for every repo module, and mathlib/other imports."""
import os, re, sys
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))
ROOTS = [os.path.join(ROOT, d) for d in ('milestones/35-231-lean/lean', 'work/final_lean', 'work/spectral/stronger', 'work/spectral')]
IMP = re.compile(r'^\s*import\s+(.+)$')
def find(m):
    rel = m.replace('.', '/') + '.lean'
    for r in ROOTS:
        p = os.path.join(r, rel)
        if os.path.exists(p): return p
    return None
def imports(p):
    out = []
    for line in open(p, encoding='utf-8'):
        s = line.strip()
        if s.startswith('--') or not s: continue
        mm = IMP.match(line)
        if mm: out += mm.group(1).split('--')[0].split()
        elif not s.startswith('import') and not s.startswith('/-') and s not in ('-/',):
            if s.startswith(('namespace','open','set_option','def','theorem','section','variable','noncomputable','@[','private','abbrev','structure','inductive','lemma','universe','/--','#')): break
    return out
def closure(targets):
    seen, ext, order = {}, set(), []
    def go(m):
        if m in seen: return
        p = find(m)
        if p is None: ext.add(m); seen[m] = None; return
        seen[m] = p
        for i in imports(p): go(i)
        order.append(m)
    for t in targets: go(t)
    return order, seen, ext
if __name__ == '__main__':
    order, seen, ext = closure(sys.argv[1:])
    for m in order: print(f'{m}\t{os.path.relpath(seen[m], ROOT)}')
    for e in sorted(ext): print(f'EXT\t{e}')
