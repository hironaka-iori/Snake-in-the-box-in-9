"""Generate the OFF = 5000 variants of the kernel LRAT checkers (six-centre window CNFs).

Six-centre radius-4 window CNFs have up to 4,040 variables, just past the `O4k` checkers
(`OFF = 4000`, at most 3,999 variables).  This script writes the same files with the
literal offset OFF = 5000 (at most 4,999 variables), next to the existing variants in
`work/final_lean`:

  LratCheckO5k                         base (trees, clause semantics, soundness)
  LratFastO5k{14,15,16,17}             fast checker
  LratFast2_O5k{14,15,16,17}           cached start database (flag bit 2^(bits-1))
  LratFast2F_O5k{14,15,16,17}          check2 with the lemma tree forced

There is no 13-bit fast variant: a literal word is `bit + 1` with `bit < 2 OFF = 10000`,
which needs 14 bits (13-bit words stop at 8191, enough only for OFF <= 4095).  The base
module keeps the 13-bit `check` of `LratCheck` (it is only imported for its trees and
soundness lemmas, exactly as `LratCheckO4k` is by the 14- to 17-bit O4k variants).

The substitution rules are those of
`milestones/10-window-aggregate/scripts/gen_checker_variants.py` (imported, not
modified).  NatPack (checkpoint chunks) stores each chunk with its own field width, so it
needs no variant.  Existing files are only rewritten when their content changes.

  python gen_checker_variants_o5k.py [--check]   # --check: fail if a file would change
"""
import argparse, importlib.util, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
LEAN = os.path.join(ROOT, 'work', 'final_lean')
K5 = os.path.join(ROOT, 'milestones', '10-window-aggregate', 'scripts', 'gen_checker_variants.py')

spec = importlib.util.spec_from_file_location('gcv5', K5)
gcv5 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gcv5)

OFF = 5000
BASE_MOD, BASE_NS = 'LratCheckO5k', 'LratO5k'
WIDTHS = (14, 15, 16, 17)
ME = 'milestones/23-k6-lean/scripts/gen_checker_variants_o5k.py'


def header(kind, bits):
    h = gcv5.header(kind, bits, OFF)
    return h.replace('milestones/10-window-aggregate/scripts/gen_checker_variants.py', ME)


def texts():
    base = open(os.path.join(LEAN, 'LratCheck.lean')).read()
    fast = open(os.path.join(LEAN, 'LratFast.lean')).read()
    fast2 = open(os.path.join(LEAN, 'LratFast2.lean')).read()
    fast2f = open(os.path.join(LEAN, 'LratFast2F.lean')).read()
    for s in (base, fast, fast2, fast2f):
        assert '5000' not in s and '10000' not in s and '9600' not in s
    assert (1 << 13) - 1 < 2 * OFF <= (1 << min(WIDTHS)) - 1
    out = {}
    t = base.replace('import LocalWindowModel\n', 'import LocalWindowModel\n\n' + header('LratCheck', 13), 1)
    out[BASE_MOD] = gcv5.variant(t, 13, OFF, BASE_NS, 'LratFast', 'LocalWindowModel')
    for bits in WIDTHS:
        sfx = 'O5k%d' % bits
        fmod = 'LratFast' + sfx
        t = fast.replace('import LratCheck\n', 'import LratCheck\n\n' + header('LratFast', bits), 1)
        out[fmod] = gcv5.variant(t, bits, OFF, BASE_NS, fmod, BASE_MOD)
        # LratFast2 (same rules as gen_checker_variants.py)
        t = fast2.replace('import LratFast\n', 'import LratFast%s\n\n%s' % (sfx, header('LratFast2', bits)), 1)
        t = t.replace('4096', str(1 << (bits - 1)))
        t = t.replace('4800', str(2 * OFF)).replace('2400', str(OFF))
        t = re.sub(r'\b13\b', str(bits), t.replace('8191', str((1 << bits) - 1)))
        t = t.replace('Snake9.LratFast2', '@@F2@@').replace('Snake9.LratFast', 'Snake9.LratFast' + sfx)
        t = t.replace('Snake9.Lrat ', 'Snake9.%s ' % BASE_NS).replace('Snake9.Lrat.', 'Snake9.%s.' % BASE_NS)
        t = t.replace('@@F2@@', 'Snake9.LratFast2_' + sfx)
        out['LratFast2_' + sfx] = t
        # LratFast2F
        t = fast2f.replace('import LratFast2\n', 'import LratFast2_%s\n\n%s' % (sfx, header('LratFast2F', bits)), 1)
        t = (t.replace('Snake9.LratFast2F', '@@F2F@@').replace('Snake9.LratFast2', '@@F2@@')
             .replace('Snake9.LratFast', 'Snake9.LratFast' + sfx)
             .replace('Snake9.Lrat ', 'Snake9.%s ' % BASE_NS).replace('Snake9.Lrat.', 'Snake9.%s.' % BASE_NS)
             .replace('@@F2F@@', 'Snake9.LratFast2F_' + sfx).replace('@@F2@@', 'Snake9.LratFast2_' + sfx))
        out['LratFast2F_' + sfx] = t
    for mod, t in out.items():
        # no constant of the 2400 / 4000 checkers may survive
        assert not re.search(r'\b(2400|4800|4000|8000)\b', t), mod
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--check', action='store_true')
    a = ap.parse_args()
    changed = []
    for mod, t in texts().items():
        path = os.path.join(LEAN, mod + '.lean')
        same = os.path.exists(path) and open(path).read() == t
        if not same:
            changed.append(mod)
            if not a.check:
                open(path, 'w').write(t)
        print(mod, 'unchanged' if same else ('DIFFERS' if a.check else 'written'))
    if a.check and changed:
        sys.exit(1)


if __name__ == '__main__':
    main()
