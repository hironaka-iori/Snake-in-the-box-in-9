"""Switch long segments of already generated LratFast2 replays to check2f (LratFast2F).

check2 leaves the lemma tree unevaluated between lookups; in segments with thousands of
lemmas the pending insertions exceeded the kernel's recursion depth (observed at 3684).
gen_lean_lrat.py --split now emits check2f for segments with more than --force-lemmas
lemmas; this script applies the same change to replays generated before, without
regenerating their LRAT: in each check module not yet built (no .olean newer than its
source) whose segments include one with more than N lemmas, `check2` becomes `check2f`
(and the module imports LratFast2F_*), and the root theorem uses the *2f soundness lemmas
for those segments.  Files are only rewritten when they change.

  python patch_forced.py [--lemmas 2000] [--prefix Q R]
"""
import argparse, os, re

LEAN = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..', 'work', 'final_lean'))
UNSAT = os.path.join(LEAN, 'LocalWindowUnsat')
LIB = os.path.join(LEAN, '.lake', 'build', 'lib', 'lean', 'LocalWindowUnsat')


def built(mod, f):
    o = os.path.join(LIB, mod, f[:-5] + '.olean')
    return os.path.exists(o) and os.path.getmtime(o) >= os.path.getmtime(os.path.join(UNSAT, mod, f))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lemmas', type=int, default=2000)
    ap.add_argument('--prefix', nargs='+', default=['Q', 'R'])
    a = ap.parse_args()
    for mod in sorted(os.listdir(UNSAT)):
        sub = os.path.join(UNSAT, mod)
        if not os.path.isdir(sub) or mod[0] not in a.prefix:
            continue
        head = open(os.path.join(sub, 'Data0.lean')).readline().split()[1]
        if not head.startswith('LratFast2'):
            continue
        f2f = head.replace('LratFast2', 'LratFast2F', 1)
        big = set()
        for f in os.listdir(sub):
            if f.startswith('Data') and f != 'Data0.lean':
                for m in re.finditer(r'def proof(\d+) : List Nat := (.*?)(?:\n\n|\Z)', open(os.path.join(sub, f)).read(), re.S):
                    if m.group(2).count('nat_lit') > a.lemmas:
                        big.add(int(m.group(1)))
        if not big:
            continue
        switched = set()
        for f in os.listdir(sub):
            if not f.startswith('Check'):
                continue
            path = os.path.join(sub, f)
            src = open(path).read()
            ks = {int(k) for k in re.findall(r'theorem ok(\d+) ', src)} & big
            if not ks:
                continue
            if built(mod, f) and 'check2f' not in src:
                continue   # already checked with check2
            new = src
            for k in ks:
                new = new.replace('check2 start%d ' % k, 'check2f start%d ' % k)
            if 'import ' + f2f not in new:
                lines = new.split('\n')
                i = max(j for j, l in enumerate(lines) if l.startswith('import '))
                lines.insert(i + 1, 'import ' + f2f)
                new = '\n'.join(lines)
            if 'open Snake9.' + f2f not in new:
                new = new.replace('\nopen Snake9.' + head + '\n', '\nopen Snake9.%s\nopen Snake9.%s\n' % (head, f2f), 1)
            switched |= ks
            if new != src:
                open(path, 'w').write(new)
        if not switched:
            continue
        root = os.path.join(UNSAT, mod + '.lean')
        src = open(root).read()
        new = src
        for k in switched:
            for thm in ('replay_true2', 'cpz_true2', 'final_false2'):
                new = re.sub(r'\b%s \((s|t) := start%d\)' % (thm, k), r'%sf (\1 := start%d)' % (thm, k), new)
        if 'import ' + f2f not in new:
            lines = new.split('\n')
            i = max(j for j, l in enumerate(lines) if l.startswith('import '))
            lines.insert(i + 1, 'import ' + f2f)
            new = '\n'.join(lines)
        if 'open Snake9.' + f2f not in new:
            new = new.replace('\nopen Snake9.' + head + '\n', '\nopen Snake9.%s\nopen Snake9.%s\n' % (head, f2f), 1)
        if new != src:
            open(root, 'w').write(new)
        print(mod, 'segments', sorted(switched))


if __name__ == '__main__':
    main()
