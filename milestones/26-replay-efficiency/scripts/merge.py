"""Merge the Data, Check and main modules of one generated replay into a single module.

  python merge.py ROOT MOD

Writes ROOT/LocalWindowUnsat/MOD.lean (the theorem `unsat` unchanged) and removes the
sub-directory MOD/.  Definitions, kernel checks and the main theorem are the same; only
the module boundaries go.
"""
import os, re, shutil, sys

root, mod = sys.argv[1], sys.argv[2]
d = os.path.join(root, 'LocalWindowUnsat', mod)
main_p = os.path.join(root, 'LocalWindowUnsat', mod + '.lean')


def order(f):
    m = re.match(r'(Data|Check)(\d+)\.lean$', f)
    return ({'Data': 0, 'Check': 1}[m.group(1)], int(m.group(2)))


files = sorted([f for f in os.listdir(d) if f.endswith('.lean')], key=order) 
imports, opens, body = [], [], []
for f in [os.path.join(d, x) for x in files] + [main_p]:
    t = re.sub(r'/-!.*?-/\n', '', open(f).read(), flags=re.S)
    for line in t.split('\n'):
        if line.startswith('import '):
            if 'LocalWindowUnsat.' not in line and line not in imports:
                imports.append(line)
        elif line.startswith('open '):
            if line not in opens:
                opens.append(line)
        elif line.startswith(('namespace ', 'end Snake9', 'set_option')):
            continue
        else:
            body.append(line)
ns = 'Snake9.LocalWindow.' + mod
out = imports + ['', '/-! LRAT replay of `%s`, data, kernel checks and main theorem in one module (merged). -/' % mod, '',
                 'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', 'set_option Elab.async false', '',
                 'namespace ' + ns] + opens + body + ['end ' + ns, '']
shutil.rmtree(d)
open(main_p, 'w').write(re.sub(r'\n{3,}', '\n\n', '\n'.join(out)))
