"""Emit Lean proofs that every UNSAT-core clause follows from the snake axioms.

For each of the 22 window certificates this script rebuilds the CNF encoding of
`wincert.Encoding` while recording, for every clause, a *tag* (its clause family
and parameters) and, for every variable, its *meaning*:

  primary variable of ball vertex v   ->  `.p v`   (value `S v`)
  endpoint flag of ball vertex v      ->  `.e v`   (value `E v`)
  Sinz register s[i][j] of counter c  ->  `.r c i j`
                                          (value: at least j+1 of lits[0..i] hold)

It checks that the rebuilt clauses coincide with `wincert.Encoding(...).clauses`
and with the prefix of the committed CNF, that the remaining committed clauses are
cycle cuts, and that the Lean core equals the committed clauses at `core_ids`.
It then writes

  work/final_lean/LocalWindowSat/<Module>.lean
      meaning tree, counter table, tag list, and the theorem `sat`, discharged by
      the generic soundness theorem of `LocalWindowTags` and one kernel `decide`.

The generic module `work/final_lean/LocalWindowTags.lean` is hand-written.

  python3 gen_lean_sat.py            # all 22 certificates
  python3 gen_lean_sat.py --check    # only the Python-side checks
  python3 gen_lean_sat.py --set direction   # the 145 direction certificates

With `--set direction` the cores come from `data/lean_core_direction/` (written by
`gen_lean_core.py --set direction`) and the CNFs from `certificates/direction/`; the
script also writes `work/final_lean/LocalWindowDirSat.lean`, which turns the 145 core
refutations into `AllRefuted239`.
"""
import argparse, gzip, json, os, re, sys, types
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
CERTS = os.path.join(HERE, '..', 'certificates')
CORE = os.path.join(HERE, '..', 'data', 'lean_core')
LEAN = os.path.join(ROOT, 'work', 'final_lean')

if 'pysat' not in sys.modules:  # wincert imports a SAT solver that the encoding does not need
    try:
        import pysat.solvers  # noqa: F401
    except ImportError:
        pysat = types.ModuleType('pysat'); solvers = types.ModuleType('pysat.solvers')
        solvers.Cadical153 = None; pysat.solvers = solvers
        sys.modules['pysat'] = pysat; sys.modules['pysat.solvers'] = solvers
import wincert  # noqa: E402


def code(l):
    return 2 * l if l > 0 else -2 * l + 1


class TaggedEncoding:
    """Mirror of `wincert.Encoding.build` that records tags and variable meanings."""

    def __init__(self, window, alpha, radius=3, ends=2):
        self.window, self.alpha, self.ends = list(window), list(alpha), ends
        centers = window[1:-1]
        self.ball = [v for v in range(512) if min((v ^ c).bit_count() for c in centers) <= radius]
        self.B = set(self.ball)
        self.var = {v: i + 1 for i, v in enumerate(self.ball)}
        self.meaning = {i + 1: ('p', v) for i, v in enumerate(self.ball)}
        self.nv = len(self.ball)
        self.clauses, self.tags, self.ctrs = [], [], []
        self.build()

    def fresh(self, m):
        self.nv += 1
        self.meaning[self.nv] = m
        return self.nv

    def add(self, c, tag):
        self.clauses.append(list(c)); self.tags.append(tag)

    def build(self):
        X, B = self.var, self.B
        for v in self.window:
            self.add([X[v]], ('window',))
        endvars = []
        for v in self.ball:
            ns = [X[v ^ 1 << k] for k in range(9) if v ^ 1 << k in B]
            for a, b, c in combinations(ns, 3):
                self.add([-X[v], -a, -b, -c], ('deg2',))
            if len(ns) == 9:
                e = self.fresh(('e', v)); endvars.append(e)
                self.add([-X[v]] + ns, ('degPos',))
                self.add([-e, X[v]], ('endSel',))
                for t, w in enumerate(ns):
                    self.add([-X[v], e] + [u for u in ns if u != w], ('lowEnd', t))
                for a, b in combinations(ns, 2):
                    self.add([-e, -a, -b], ('endLow',))
        self.atmost(endvars, self.ends, ('ends',))
        centers = self.window[1:-1]
        for i, c in enumerate(centers, 1):
            used = {(c ^ self.window[i - 1]).bit_length() - 1, (c ^ self.window[i + 1]).bit_length() - 1}
            corners = [X[c ^ 1 << a ^ 1 << b] for a, b in combinations(range(9), 2)
                       if a not in used and b not in used]
            assert len(corners) == 21
            k = self.alpha[i - 1]
            if k is None:
                continue
            lo, hi = k if isinstance(k, (tuple, list)) else (k, k)
            if hi < 21:
                self.atmost([-c2 for c2 in corners], hi, ('hi', i - 1))
            if lo > 0:
                self.atmost(corners, 21 - lo, ('lo', i - 1))
        for v in self.ball:
            for a, b in combinations(range(9), 2):
                if v >> a & 1 or v >> b & 1:
                    continue
                sq = [v, v | 1 << a, v | 1 << b, v | 1 << a | 1 << b]
                if all(w in B for w in sq):
                    self.add([-X[w] for w in sq], ('cut',))
            for t in combinations(range(9), 3):
                if any(v >> k & 1 for k in t):
                    continue
                cube = [v ^ sum(1 << t[j] for j in range(3) if r >> j & 1) for r in range(8)]
                if all(w in B for w in cube):
                    for r in range(4):
                        self.add([-X[cube[s]] for s in range(8) if s not in (r, 7 - r)], ('cut',))

    def atmost(self, lits, k, kind):
        n = len(lits)
        if k >= n:
            return
        assert k >= 1, 'k = 0 counters are not supported by LocalWindowTags'
        ci = len(self.ctrs)
        self.ctrs.append((list(lits), k, kind))
        s = [[self.fresh(('r', ci, i, j)) for j in range(k)] for i in range(n)]
        self.add([-lits[0], s[0][0]], ('first', ci, 0))
        for j in range(1, k):
            self.add([-s[0][j]], ('zero', ci, j))
        for i in range(1, n):
            self.add([-lits[i], s[i][0]], ('first', ci, i))
            self.add([-s[i - 1][0], s[i][0]], ('mono', ci, i - 1, 0))
            for j in range(1, k):
                self.add([-lits[i], -s[i - 1][j - 1], s[i][j]], ('step', ci, i - 1, j - 1))
                self.add([-s[i - 1][j], s[i][j]], ('mono', ci, i - 1, j))
            self.add([-lits[i], -s[i - 1][k - 1]], ('over', ci, i - 1))


def read_cnf(path):
    out, header = [], None
    with gzip.open(path, 'rt') as f:
        for line in f:
            if line.startswith('p'):
                header = line.split()
                continue
            if line.startswith('c') or not line.strip():
                continue
            lits = [int(x) for x in line.split()]
            assert lits[-1] == 0
            out.append(lits[:-1])
    return int(header[2]), out


def module_name(name):
    c, orient, shape = name.split('_')
    return 'C' + c + orient.capitalize() + shape.capitalize()


def read_lean_raw(module):
    src = open(os.path.join(LEAN, 'LocalWindowCnf', module + '.lean')).read()
    body = src.split('def raw : List (List Nat) := [', 1)[1].split('\n\ndef cnf', 1)[0]
    return [[int(x) for x in m.split(',') if x.strip()] for m in re.findall(r'\[([0-9, ]*)\]', body)]


def is_cycle_set(vs):
    s = set(vs)
    return len(vs) > 0 and len(s) == len(vs) and all(
        sum(1 for k in range(9) if v ^ 1 << k in s) >= 2 for v in vs)


def lean_tree_terms(meaning, nv):
    """`MT` term: at a node, bit 0 of the remaining index picks the side (even: left)."""
    def leaf(x):
        m = meaning.get(x)
        if m is None:
            return '.z'
        if m[0] == 'p':
            return f'(.p {m[1]})'
        if m[0] == 'e':
            return f'(.e {m[1]})'
        return f'(.r {m[1]} {m[2]} {m[3]})'

    def build(r, s):
        if r + s > nv:
            return leaf(r)
        return f'(.n {build(r, 2 * s)} {build(r + s, 2 * s)})'
    return build(0, 1)


def lean_tag(t):
    if len(t) == 1:
        return '.' + t[0]
    return '(.' + t[0] + ' ' + ' '.join(map(str, t[1:])) + ')'


def process(name, emit, certs=CERTS, core_dir=CORE):
    meta = json.load(open(os.path.join(core_dir, name + '.json')))
    window, bounds = meta['window'], [tuple(b) for b in meta['bounds']]
    if 'dirs' in meta:  # direction certificate: the window is `winOf dirs`
        assert window == wincert.window_from_dirs(meta['dirs']), name
    alpha = [b[0] if b[0] == b[1] else b for b in bounds]
    radius = meta.get('radius', 3)
    enc = TaggedEncoding(window, alpha, radius=radius)
    ref = wincert.Encoding(window, alpha, radius=radius)
    assert ref.clauses == enc.clauses and ref.nv == enc.nv, name
    nv, committed = read_cnf(os.path.join(certs, name + '.cnf.gz'))
    assert nv == enc.nv, (name, nv, enc.nv)
    npre = len(enc.clauses)
    assert committed[:npre] == enc.clauses, name
    inv = {i: v for v, i in enc.var.items()}
    for c in committed[npre:]:
        assert all(l < 0 and -l in inv for l in c), name
        assert is_cycle_set([inv[-l] for l in c]), name
    ids = meta['core_ids']
    assert len(meta['window']) and meta['cnf_clauses'] == len(committed)
    core = [committed[i - 1] for i in ids]
    module = meta['module'].split('.', 1)[1]
    assert 'dirs' in meta or module == module_name(name), name
    raw = read_lean_raw(module)
    assert raw == [[code(l) for l in c] for c in core], name
    tags = [enc.tags[i - 1] if i <= npre else ('cut',) for i in ids]
    fam = {}
    for t in tags:
        fam[t[0]] = fam.get(t[0], 0) + 1
    if emit:
        write_module(name, module, meta, enc, tags)
    return module, len(core), fam, len(committed) - npre


def write_module(name, module, meta, enc, tags):
    ctr_terms = []
    for lits, k, kind in enc.ctrs:
        kt = '.ends' if kind[0] == 'ends' else f'(.{kind[0]} {kind[1]})'
        ctr_terms.append(f'⟨[{", ".join(str(code(l)) for l in lits)}], {k}, {kt}⟩')
    tag_body = ',\n  '.join(', '.join(lean_tag(t) for t in tags[i:i + 8]) for i in range(0, len(tags), 8))
    src = f'''import LocalWindowTags
import {meta["module"]}

/-! Every clause of the UNSAT core `{meta["module"]}.cnf` (certificate `{name}`)
follows from the snake axioms (generated by
`milestones/10-window-aggregate/scripts/gen_lean_sat.py`).  `meaning` gives each
variable its value under the assignment `Tags.tau`, `ctrs` lists the sequential
counters, and `tags` names the clause family of each core clause.  The theorem
`sat` checks all tags by one kernel evaluation. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.{module}

open Snake9.LocalWindow.Tags

def meaning : MT :=
  {lean_tree_terms(enc.meaning, enc.nv)}

def ctrs : List Ctr := [
  {(','+chr(10)+'  ').join(ctr_terms)}]

def tags : List Tag := [
  {tag_body}]

theorem check : checkAll meaning ctrs window bounds tags raw = true := by decide +kernel

theorem sat : ∀ S E : Nat → Bool,
    Axioms S E window (centresOf window bounds) → ∃ τ, cnfTrue τ cnf = true :=
  fun S E h => ⟨tau S E meaning ctrs, sound meaning ctrs window bounds tags raw check S E h⟩

end Snake9.LocalWindow.{module}
'''
    os.makedirs(os.path.join(LEAN, 'LocalWindowSat'), exist_ok=True)
    open(os.path.join(LEAN, 'LocalWindowSat', module + '.lean'), 'w').write(src)


DCERTS = os.path.join(CERTS, 'direction')
DCORE = os.path.join(HERE, '..', 'data', 'lean_core_direction')
DCORE5 = os.path.join(HERE, '..', 'data', 'lean_core_direction5')

# per certificate set: keys module, key list, number of keys, aggregate module, premise, bound
DIR_SETS = {'direction': ('LocalWindowDirKeys', 'dirKeys', 145, 'LocalWindowDirSat', 'AllRefuted239', 239),
            'direction5': ('LocalWindowDirKeys5', 'dirKeys5', 325, 'LocalWindowDirSat5', 'AllRefuted238', 238),
            'r4': ('LocalWindowDirKeysR4', 'dirKeysR4', None, 'LocalWindowDirSatR4', 'AllRefuted236', 236)}
DIR_DIRS = {'direction': (DCERTS, DCORE), 'direction5': (DCERTS, DCORE5),
            'r4': (os.path.join(HERE, '..', 'certificates', 'direction_r4'),
                   os.path.join(HERE, '..', 'data', 'lean_core_direction_r4'))}


def dir_key_order(metas, dset='direction'):
    """Module names in the order of the key list (LocalWindowDirKeys[5].lean)."""
    keys_mod, _, n, _, _, _ = DIR_SETS[dset]
    src = open(os.path.join(LEAN, keys_mod + '.lean')).read()
    keys = [([int(x) for x in d.split(',')], [int(x) for x in s.split(',')])
            for d, s in re.findall(r'\(\[([0-9, ]*)\], \[([0-9, ]*)\]\)', src)]
    by_key = {(tuple(m['dirs']), tuple(m['syms'])): m['module'].split('.', 1)[1] for m in metas}
    assert len(keys) == len(by_key) and (n is None or n == len(keys)), (len(keys), len(by_key), n)
    assert {(tuple(d), tuple(s)) for d, s in keys} == set(by_key)
    return [by_key[(tuple(d), tuple(s))] for d, s in keys]


def write_dir_aggregate(order, dset='direction'):
    keys_mod, keys, n, agg, premise, bound = DIR_SETS[dset]
    n = len(order)
    imports = ''.join(f'import LocalWindowSat.{m}\n' for m in sorted(order))
    unsat = ' ∧\n  '.join(f'Unsat {m}.cnf' for m in order)
    hs = ', '.join(f'h{i}' for i in range(len(order)))
    terms = ''.join(f'\n    (And.intro (Tags.refuted_of_sat {m}.sat h{i})' for i, m in enumerate(order))
    what = {'direction': 'direction', 'direction5': 'five-centre', 'r4': 'radius-4'}[dset]
    src = f'''import {keys_mod}
import LocalWindowTags
{imports}
/-!
# The {n} {what} certificates from their core refutations

Generated by `milestones/10-window-aggregate/scripts/gen_lean_sat.py --set {dset}`.
Each module `LocalWindowSat.D…` proves that its UNSAT core follows from the snake
axioms (`sat`).  Hence the {n} refutations `Unsat D….cnf` (listed in the order of
`{keys}`) give `{premise}`, the only hypothesis of `upper_{bound}_of_refuted`.
-/

set_option maxRecDepth 100000

namespace Snake9.LocalWindow

/-- Refutations of the {n} {what} cores, in the order of `{keys}`. -/
def AllUnsat{bound} : Prop :=
  {unsat}

theorem allRefuted{bound}_of_unsat (h : AllUnsat{bound}) : {premise} := by
  obtain ⟨{hs}⟩ := h
  exact{terms} trivial{")" * len(order)}

end Snake9.LocalWindow
'''
    open(os.path.join(LEAN, agg + '.lean'), 'w').write(src)


def write_dir_unsat(order, dset='direction'):
    """LocalWindowDirUnsat[5].lean: the replays `LocalWindowUnsat.D*` (generated, not
    committed) combined with the `sat` theorems into the premise of the bound."""
    keys_mod, keys, n, agg, premise, bound = DIR_SETS[dset]
    n = len(order)
    what = {'direction': 'direction-window', 'direction5': 'five-centre-window', 'r4': 'radius-4-window'}[dset]
    unsat_mod = 'LocalWindowDirUnsat' + {'direction': '', 'direction5': '5', 'r4': 'R4'}[dset]
    imports = ''.join(f'import LocalWindowUnsat.{m}\n' for m in order)
    terms = ',\n   '.join(f'{m}.unsat' for m in order)
    src = f'''import {agg}
{imports}
/-!
# The {n} {what} refutations

Combines the kernel-checked LRAT refutations `LocalWindowUnsat.D*` (generated by
`milestones/10-window-aggregate/scripts/run_direction_replays.py`, not committed) with the
`sat` theorems into `{premise}`, the premise of `upper_{bound}_of_refuted`.
-/

namespace Snake9.LocalWindow

theorem allUnsat{bound} : AllUnsat{bound} :=
  ⟨{terms}⟩

theorem allRefuted{bound} : {premise} := allRefuted{bound}_of_unsat allUnsat{bound}

end Snake9.LocalWindow

#print axioms Snake9.LocalWindow.allRefuted{bound}
'''
    open(os.path.join(LEAN, unsat_mod + '.lean'), 'w').write(src)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--check', action='store_true', help='run the checks without writing Lean files')
    ap.add_argument('--set', choices=['window', 'direction', 'direction5', 'r4'], default='window')
    ap.add_argument('names', nargs='*')
    a = ap.parse_args()
    certs, core_dir = (CERTS, CORE) if a.set == 'window' else DIR_DIRS[a.set]
    names = a.names or sorted(f[:-5] for f in os.listdir(core_dir)
                              if f.endswith('.json') and not f.startswith('_'))
    mods = []
    for name in names:
        module, ncore, fam, ncuts = process(name, not a.check, certs, core_dir)
        mods.append(module)
        print(f'{name:18s} {module:18s} core {ncore:5d}  cuts(all) {ncuts:4d}  ' +
              ' '.join(f'{k}:{v}' for k, v in sorted(fam.items())))
    if not a.check and not a.names:
        if a.set == 'window':
            agg = 'import LocalWindowSat.' + '\nimport LocalWindowSat.'.join(sorted(mods)) + '\n'
            open(os.path.join(LEAN, 'LocalWindowSat.lean'), 'w').write(agg)
        else:
            metas = [json.load(open(os.path.join(core_dir, n + '.json'))) for n in names]
            order = dir_key_order(metas, a.set)
            write_dir_aggregate(order, a.set)
            write_dir_unsat(order, a.set)


if __name__ == '__main__':
    main()
