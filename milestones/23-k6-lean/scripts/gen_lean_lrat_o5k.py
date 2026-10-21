"""`gen_lean_lrat.py` with the literal offset OFF = 5000 (six-centre window CNFs).

Runs `milestones/10-window-aggregate/scripts/gen_lean_lrat.py` unchanged, except that
`set_width` also accepts `--off 5000`, which selects the checkers written by
`gen_checker_variants_o5k.py` (`LratFastO5k<bits>`, `LratFast2_O5k<bits>`,
`LratFast2F_O5k<bits>`).  OFF = 5000 needs `--fast` and 14- to 17-bit words: a literal
word is `bit + 1 <= 10000 > 8191`.  All other offsets are passed through.

  python gen_lean_lrat_o5k.py --off 5000 --wbits 14 --fast --split --check --work DIR NAME ...

`--selftest` builds a four-clause CNF over the variables 4500 and 4999 (beyond the O4k
range), its LRAT refutation and core JSON in a scratch directory, and runs the export with
`--check` there (the Python simulation of the kernel checker); compile the emitted modules
with `lean` to replay it in the kernel.
"""
import importlib.util, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
SRC = os.path.join(ROOT, 'milestones', '10-window-aggregate', 'scripts', 'gen_lean_lrat.py')

spec = importlib.util.spec_from_file_location('gen_lean_lrat', SRC)
g = importlib.util.module_from_spec(spec)
spec.loader.exec_module(g)
_orig_set_width = g.set_width


def set_width(bits, fast=False, off=2400, split=False):
    if off != 5000:
        return _orig_set_width(bits, fast, off, split)
    assert bits in (14, 15, 16, 17), 'OFF = 5000 needs 14- to 17-bit words'
    assert fast, 'OFF = 5000 has only the fast checkers'
    g.W, g.M, g.FAST, g.OFF, g.SPLIT, g.FLAG = bits, (1 << bits) - 1, True, off, split, 1 << (bits - 1)
    sfx = 'O5k%d' % bits
    g.BASE_NS = 'Snake9.LratO5k'
    if split:
        g.F2F = 'LratFast2F_' + sfx
        f2 = 'LratFast2_' + sfx
        g.CHECKER_IMPORT = 'import ' + f2
        g.CHECKER_OPEN = 'open Snake9.LratFast%s\nopen Snake9.%s\nopen %s (Tree TreeTrue andB)' % (
            sfx, f2, g.BASE_NS)
    else:
        g.CHECKER_IMPORT = 'import LratFast' + sfx
        g.CHECKER_OPEN = 'open Snake9.LratFast%s\nopen %s (Tree TreeTrue andB)' % (sfx, g.BASE_NS)


g.set_width = set_width


def selftest(out):
    """A CNF over variables 4500 (a) and 4999 (b): (a|b) (-a|b) (a|-b) (-a|-b)."""
    a, b = 4500, 4999
    cls = [[a, b], [-a, b], [a, -b], [-a, -b]]
    work = os.path.join(out, 'work')
    data = os.path.join(out, 'data')
    cnfdir = os.path.join(out, 'LocalWindowCnf')
    for d in (work, data, cnfdir):
        os.makedirs(d, exist_ok=True)
    name = 'T5kSmoke'
    with open(os.path.join(work, name + '.cnf'), 'w') as f:
        f.write('p cnf %d %d\n' % (b, len(cls)))
        for c in cls:
            f.write(' '.join(map(str, c)) + ' 0\n')
    with open(os.path.join(work, name + '.lrat'), 'w') as f:
        f.write('5 %d 0 1 3 0\n' % a)      # a: from -a, (a|b) gives b, (a|-b) conflicts
        f.write('6 0 5 2 4 0\n')           # empty: a, (-a|b) gives b, (-a|-b) conflicts
    json.dump({'module': 'LocalWindowCnf.' + name, 'core_ids': [1, 2, 3, 4]},
              open(os.path.join(data, name + '.json'), 'w'))
    enc = lambda l: 2 * l if l > 0 else 2 * (-l) + 1
    raw = ',\n'.join('  [%s]' % ', '.join(str(enc(l)) for l in c) for c in cls)
    open(os.path.join(cnfdir, name + '.lean'), 'w').write(
        'import LocalWindowModel\n\n/-! Self-test CNF of `gen_lean_lrat_o5k.py` (variables 4500 and 4999). -/\n\n'
        'namespace Snake9.LocalWindow.%s\n\n/-- Literals coded by `decodeLit`. -/\n'
        'def raw : List (List Nat) := [\n%s]\n\ndef cnf : List (List Int) := raw.map (·.map decodeLit)\n\n'
        'end Snake9.LocalWindow.%s\n' % (name, raw, name))
    return ['--work', work, '--data', data, '--out', out, '--off', '5000', '--wbits', '14',
            '--fast', '--split', '--check', '--seg', '2', '--cp', '1', '--group', '1', name]


if __name__ == '__main__':
    if len(sys.argv) == 3 and sys.argv[1] == '--selftest':
        sys.argv = [sys.argv[0]] + selftest(os.path.abspath(sys.argv[2]))
    g.main()
