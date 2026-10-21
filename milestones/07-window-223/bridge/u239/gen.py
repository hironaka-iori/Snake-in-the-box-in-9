"""Generate the Lean modules (G2 refutation + G1 tables/checks) for the 145 direction windows of
the 239 automaton (adapted from ../u242/gen.py).  Normally driven by regen.py.

Inputs (in WORK, see regen.py): data/<tag>.cnf, the committed
milestones/10-window-aggregate/certificates/direction CNF (sha256 in cases.json), and either
data/<tag>.lrat (drat-trim -L output of the committed DRUP proof) or, for the 55 symmetry-broken
windows, sym/<tag>.{cnf,lrat,json} (symsolve.py).
The wincert.Encoding of each case is rebuilt (with a recording `atmost`) and must reproduce the
certified CNF up to the trailing cycle cuts.  Everything emitted is untrusted: the Lean kernel
re-checks every RUP step (G2) and every clause against the G1 checker.

usage: python3 -I gen.py WORK OUTDIR TAG...   (TAG from cases.json; default all but `reuse`)
Writes OUTDIR/<Mod>Inputs.lean, <Mod>S00..lean, <Mod>Main.lean, <Mod>G1.lean, <Mod>G1C<k>.lean.
"""
import sys, json, hashlib, os, re

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.normpath(os.path.join(HERE, '..', '..', '..', '..'))
sys.path.insert(0, os.path.join(REPO, 'milestones', '10-window-aggregate', 'scripts'))
from wincert import Encoding, window_from_dirs

sys.path.insert(0, HERE)
DATA = SYM = None          # set by regen.py or __main__: WORK/data, WORK/sym
CASES_JSON = json.load(open(os.path.join(HERE, 'cases.json')))
# windows whose certified CNF is identical (same sha256) to one refuted for the 241 bound
REUSE = {c['tag']: c['reuse'] for c in CASES_JSON if c['kind'] == 'reuse'}


def modname(tag):
    d, a = tag[1:].split('_a')
    return 'DV' + d + '_' + a.replace('6-21', 'L')


def load_cases():
    out = {}
    for c in CASES_JSON:
        al = [lo if lo == hi else (lo, hi) for lo, hi in c['alpha']]
        out[c['tag']] = (modname(c['tag']), c['dirs'], al, c, None)
    return out
CH0 = 48         # input clauses per chunk; with more than 46 chunks the projection chains
                 # `h.2.2...1.2...1` (up to ~106 deep) overflow the stack and are split at `a{k}`
CHK = 8          # chunks per G1 check module
PER, HB = 100000, 100000   # RUP steps / hints per step module


class Rec(Encoding):
    def atmost(self, lits, k, kind):
        if not hasattr(self, 'blocks'):
            self.blocks = []
        base = self.nv + 1
        super().atmost(lits, k, kind)
        if 0 < k < len(lits):
            assert self.nv == base - 1 + len(lits) * k
            self.blocks.append((base, k, list(lits), kind))


def legacy(s, lex):
    """The 80 non-symmetry-broken windows were generated (and their objects checked) before the
    data definitions became `noncomputable def`; emit them as plain `def` there so the regenerated
    sources are byte-identical to the checked ones (the kernel treats both alike)."""
    return s if lex else re.sub(r'(?m)^noncomputable def ', 'def ', s)


def L(xs): return '[' + ', '.join(map(str, xs)) + ']'
def lit(l): return f'pos {l}' if l > 0 else f'neg {-l}'


def mask(c):
    p = n = 0
    for l in c:
        if l > 0: p |= 1 << l
        else: n |= 1 << -l
    return p, n


def run(tag, out):
    mod, dirs, alpha, cert, cert5 = CASES[tag]
    lex = cert['kind'] == 'sym'
    if lex:   # symmetry-broken certificate (symsolve.py): committed CNF + lex-leader clauses
        sym = json.load(open(os.path.join(SYM, f'{tag}.json')))
        cnfp, lratp = (os.path.join(SYM, f'{tag}.{e}') for e in ('cnf', 'lrat'))
        base_raw = open(os.path.join(DATA, f'{tag}.cnf'), 'rb').read()
        bsha = hashlib.sha256(base_raw).hexdigest()
        assert bsha == cert['cnf_sha256'], tag
        base_cl = [l for l in base_raw.decode().splitlines() if l and l[0] not in 'pc']
    else:
        cnfp, lratp = (os.path.join(DATA, f'{tag}.{e}') for e in ('cnf', 'lrat'))
    raw = open(cnfp, 'rb').read()
    sha = hashlib.sha256(raw).hexdigest()
    if not lex:
        assert sha == cert['cnf_sha256'], tag
    clauses = [list(map(int, l.split()))[:-1] for l in raw.decode().splitlines() if l and l[0] not in 'pc']
    enc = Rec(window_from_dirs(dirs), alpha, 3)
    assert [[a, a] if isinstance(a, int) else list(a) for a in alpha] == cert['alpha']
    assert clauses[:len(enc.clauses)] == enc.clauses, tag
    if lex:
        nbase = sym['nbase']
        assert [' '.join(map(str, c)) + ' 0' for c in clauses[:nbase]] == [l.strip() for l in base_cl]
        from symsolve import lex_clauses, lexgens
        lexc, linfo, _ = lex_clauses(enc, lexgens(dirs), sym['vb'])
        assert clauses[nbase:] == lexc and [list(x) for x in linfo] == sym['gens'] and sym['vb'] == enc.nv + 1
        kinds = list(enc.kinds) + ['cycle_cut'] * (nbase - len(enc.clauses)) + ['lex'] * len(lexc)
    else:
        kinds = list(enc.kinds) + ['cycle_cut'] * (len(clauses) - len(enc.clauses))
    nb = len(enc.ball)
    ends = [v for v in enc.ball if all(v ^ 1 << k in enc.B for k in range(9))]
    ne = len(ends)
    assert enc.blocks[0][3] == 'endpoint_budget' and enc.blocks[0][2] == list(range(nb + 1, nb + ne + 1))
    ncl = len(clauses)
    steps = []
    for line in open(lratp):
        t = line.split()
        if t[1] == 'd': continue
        xs = list(map(int, t)); z = xs.index(0, 1)
        sid, c, hs = xs[0], xs[1:z], xs[z + 1:-1]
        assert sid > ncl and all(h > 0 for h in hs), 'RAT/odd step'
        steps.append((sid, c, hs))
    assert steps[-1][1] == [], 'last step must be the empty clause'
    used = sorted({h for _, _, hs in steps for h in hs if h <= ncl})
    files = []
    # ---------------- G2 inputs
    CH = max(CH0, -(-len(used) // 60))
    chunks = [used[i:i + CH] for i in range(0, len(used), CH)]
    usha = hashlib.sha256(''.join(' '.join(map(str, clauses[i - 1])) + ' 0\n' for i in used).encode()).hexdigest()
    s = f'import WinRup\nset_option maxRecDepth 100000\nset_option Elab.async false\nnamespace {mod}\nopen WinCNF WinRup\n'
    s += f'/-! Input clauses of `{tag}`: the {len(used)} clauses (of {ncl}) of the certified wincert CNF\n'
    s += f'`milestones/10-window-aggregate/certificates/direction/{tag}.cnf.gz` (sha256 {sha}) that the trimmed LRAT proof uses,\n'
    s += f'sha256 of these clauses as DIMACS lines `l1 l2 ... 0` (one per line, this order): {usha};\n'
    s += f'in their original order and DIMACS numbering (window {enc.window}, alpha {cert["alpha"]}, radius 3). -/\n'
    for k, ch in enumerate(chunks):
        s += f'/-- original clause indices {ch[0]}..{ch[-1]} -/\n'
        s += f'noncomputable def G{k} : CNF := [' + ', '.join('[' + ', '.join(lit(l) for l in clauses[i - 1]) + ']' for i in ch) + ']\n'
    s += '/-- The used clauses (original 1-based indices in `idx`). -/\nnoncomputable def F : CNF := ' + ' ++ ('.join(f'G{k}' for k in range(len(chunks))) + ')' * (len(chunks) - 1) + '\n'
    s += 'noncomputable def idx : List Nat := [' + ', '.join(map(str, used)) + ']\n'
    s += 'noncomputable def kinds : List String := [' + ', '.join('"%s"' % kinds[i - 1] for i in used) + ']\n'
    s += 'noncomputable section\n'
    for k, ch in enumerate(chunks):
        for i in ch:
            p, n = mask(clauses[i - 1]); s += f'noncomputable def c{i} : Mask := ({p}, {n})\n'
        s += f'noncomputable def M{k} : List Mask := [' + ', '.join(f'c{i}' for i in ch) + ']\n'
        s += f'theorem eM{k} : G{k}.map toMask = M{k} := by decide +kernel\n'
    s += 'end\n'
    s += 'def Inp (τ : Nat → Bool) : Prop := ' + ' ∧ '.join(f'AllSat τ M{k}' for k in range(len(chunks))) + ' ∧ True\n'
    q = len(chunks) - 1
    parts = []
    for k in range(q + 1):
        e = 'h'
        for _ in range(k): e = f'(forall_append {e}).2'
        if k < q: e = f'(forall_append {e}).1'
        parts.append(f'eM{k} ▸ allSat_map τ _ {e}')
    s += 'theorem inp_of (τ : Nat → Bool) (h : ∀ c ∈ F, clauseSat τ c) : Inp τ :=\n  ⟨' + ',\n   '.join(parts) + ', trivial⟩\n'
    if len(chunks) <= 50:
        for k, ch in enumerate(chunks):
            for r, i in enumerate(ch):
                s += f'theorem d{i} (τ : Nat → Bool) (h : Inp τ) : msat τ c{i} := h' + '.2' * k + '.1' + '.2' * r + '.1\n'
        s += f'end {mod}\n'
        open(f'{out}/{mod}Inputs.lean', 'w').write(legacy(s, lex)); files.append(f'{mod}Inputs')
        prev = f'{mod}Inputs'
    else:  # big case: the `d` lemmas go to two further modules (one module overflows the stack)
        s += f'end {mod}\n'
        open(f'{out}/{mod}Inputs.lean', 'w').write(legacy(s, lex)); files.append(f'{mod}Inputs')
        prev = f'{mod}Inputs'
        half = (len(chunks) + 1) // 2
        for j, ks in enumerate([range(0, half), range(half, len(chunks))]):
            s = f'import {prev}\nset_option maxRecDepth 100000\nset_option Elab.async false\nnamespace {mod}\nopen WinCNF WinRup\n'
            for k in ks:
                s += f'theorem a{k} (τ : Nat → Bool) (h : Inp τ) : AllSat τ M{k} := h' + '.2' * k + '.1\n'
                for r, i in enumerate(chunks[k]):
                    s += f'theorem d{i} (τ : Nat → Bool) (h : Inp τ) : msat τ c{i} := (a{k} τ h)' + '.2' * r + '.1\n'
            s += f'end {mod}\n'
            open(f'{out}/{mod}InputsD{j}.lean', 'w').write(s); files.append(f'{mod}InputsD{j}')
            prev = f'{mod}InputsD{j}'
    # ---------------- G2 steps
    H = 0
    groups, cur, chh = [], [], 0
    for st in steps:
        cur.append(st); chh += len(st[2])
        if chh >= HB or len(cur) >= PER: groups.append(cur); cur, chh = [], 0
    if cur: groups.append(cur)
    for m, grp in enumerate(groups):
        name = f'{mod}S{m:02d}'
        s = f'import {prev}\nimport WinRupImp\nset_option Elab.async false\nnamespace {mod}\n'
        s += f'-- LRAT steps {grp[0][0]}..{grp[-1][0]}: rup_imp_step id posMask negMask [hint ids]\n'
        for sid, c, hs in grp:
            p, n = mask(c); H += len(hs)
            s += f'rup_imp_step {sid} {p} {n} [' + ' '.join(map(str, hs)) + ']\n'
        s += f'end {mod}\n'
        open(f'{out}/{name}.lean', 'w').write(s); files.append(name)
        prev = name
    last = steps[-1][0]
    s = f'import {prev}\nopen WinCNF WinRup\n'
    s += (f'/-- The used-clause CNF `{mod}.F` of `{tag}` (window {enc.window}, alpha {cert["alpha"]}, radius 3)\n'
          f'is unsatisfiable: {len(steps)} RUP steps, {H} hints, each checked by the kernel. -/\n'
          f'theorem {mod}.unsatF : unsat {mod}.F :=\n  fun τ hF => msat_empty ({mod}.d{last} τ ({mod}.inp_of τ hF))\n')
    open(f'{out}/{mod}Main.lean', 'w').write(s); files.append(f'{mod}Main')
    # ---------------- G1 tables
    s = f'import WinG1Gen\nimport {mod}Inputs\n'
    s += f'/-! G1 decoding tables of `{tag}` (window {enc.window}, alpha {cert["alpha"]}), generated from\n'
    s += 'wincert.Encoding by scripts/gen.py.  Untrusted hints, validated by the kernel checker. -/\n'
    s += f'namespace {mod}\nopen WinCNF W223G1\nset_option maxRecDepth 100000\n'
    s += f'noncomputable def ballL : List Nat := {L(enc.ball)}\n'
    s += f'noncomputable def endsL : List Nat := {L(ends)}\n'
    for t, (b, k, l, kd) in enumerate(enc.blocks):
        s += f'/-- {kd} -/\n'
        s += f'noncomputable def B{t} : Block := ⟨{b}, {k}, {len(l)}, [' + ', '.join(lit(x) for x in l) + ']⟩\n'
    s += 'noncomputable def blocks : List Block := [' + ', '.join(f'B{t}' for t in range(len(enc.blocks))) + ']\n'
    s += f'noncomputable def T : Tables := ⟨{nb}, {ne}, ballL, endsL, {L(enc.window)}, blocks⟩\n'
    s += 'theorem blocksOK_T : blocksOK T = true := by decide +kernel\n'
    if lex:
        from symsolve import swapN
        s = s.replace('import WinG1Gen\n', 'import D239LexG1\n')
        s += 'open D239\n'
        for g, (a, b, base, npairs) in enumerate(linfo):
            pr = [(v, swapN(a, b, v)) for v in enc.ball if swapN(a, b, v) != v]
            assert len(pr) == npairs
            s += f'/-- lex-leader generator: coordinates {a} {b} -/\n'
            s += f'noncomputable def X{g} : LexT := ⟨[' + ', '.join(f'({v}, {w})' for v, w in pr) + f'], {base}⟩\n'
        s += 'noncomputable def X : List LexT := [' + ', '.join(f'X{g}' for g in range(len(linfo))) + ']\n'
        s += f'abbrev VB : Nat := {sym["vb"]}\n'
        s += 'theorem lexX : X.map LexT.pairs = (adjP (freeC ' + L(dirs) + ')).map (fun g => movedPairs T.ball g.1.val g.2.val) := by decide +kernel\n'
    s += f'end {mod}\n'
    open(f'{out}/{mod}G1.lean', 'w').write(legacy(s, lex)); files.append(f'{mod}G1')
    # ---------------- G1 checks, CHK chunks per module
    cm = [list(range(i, min(i + CHK, len(chunks)))) for i in range(0, len(chunks), CHK)]
    for j, ks in enumerate(cm):
        s = f'import {mod}G1\nnamespace {mod}\nopen WinCNF W223G1\nset_option maxRecDepth 100000\n'
        for k in ks:
            s += f'theorem chk{k} : G{k}.all ({"D239.check2 T X VB" if lex else "check T"}) = true := by decide +kernel\n'
        s += f'end {mod}\n'
        open(f'{out}/{mod}G1C{j}.lean', 'w').write(s); files.append(f'{mod}G1C{j}')
    s = ''.join(f'import {mod}G1C{j}\n' for j in range(len(cm)))
    s += f'import {mod}Main\nnamespace {mod}\nopen WinCNF W223G1\n'
    s += f'theorem check_T : F.all ({"D239.check2 T X VB" if lex else "check T"}) = true := by\n  simp only [F, List.all_append, ' + ', '.join(f'chk{k}' for k in range(len(chunks))) + ', Bool.and_self]\n'
    rng = ' '.join(f'{a} {a}' if isinstance(a, int) else f'{a[0]} {a[1]}' for a in alpha)
    if lex:
        s = s.replace(f'import {mod}Main\n', f'import {mod}Main\nimport D239Defs\n')
        F3 = f'(SquareIncidence.flip {dirs[3]} 7).val' if len(alpha) > 2 else ''
        if len(alpha) == 2:
            win, sp = '[0, 1, 3, 7]', f'D239.sp2 {rng}'
        elif len(alpha) == 3:
            win, sp = f'[0, 1, 3, 7, {F3}]', f'D239.sp3 {dirs[3]} {rng}'
        else:
            win = f'[0, 1, 3, 7, {F3}, (SquareIncidence.flip {dirs[4]} (SquareIncidence.flip {dirs[3]} 7)).val]'
            sp = f'D239.sp4 {dirs[3]} {dirs[4]} {rng}'
        s += f'open Snake9 in\ntheorem refutedL : D239.RefutedL {win} ({sp}) {L(dirs)} :=\n'
        s += '  ⟨T, F, X, VB, unsatF, blocksOK_T, check_T, by decide +kernel, by decide, lexX⟩\n'
        s += f'end {mod}\n'
        open(f'{out}/{mod}G1Check.lean', 'w').write(s); files.append(f'{mod}G1Check')
        print(' '.join(files))
        return files
    if len(alpha) == 2:
        s = s.replace(f'import {mod}Main\n', f'import {mod}Main\nimport D239Ref2\n')
        s += f'theorem refuted : D239.Refuted2 {rng} :=\n'
    elif len(alpha) == 3:
        s += f'theorem refuted : WinG1.Refuted3 {dirs[3]} {rng} :=\n'
    else:
        s += f'theorem refuted : WinG1.Refuted4 {dirs[3]} {dirs[4]} {rng} :=\n'
    s += '  ⟨T, F, unsatF, blocksOK_T, check_T, by decide +kernel, by decide⟩\n'
    s += f'end {mod}\n'
    open(f'{out}/{mod}G1Check.lean', 'w').write(s); files.append(f'{mod}G1Check')
    info = dict(tag=tag, mod=mod, cnf_sha256=sha, used_sha256=usha, used=len(used), clauses=ncl, steps=len(steps),
                hints=H, step_modules=len(groups), chunks=len(chunks), nb=nb, ne=ne,
                blocks=[(b, k, len(l), kd) for b, k, l, kd in enc.blocks], cycle_cuts=ncl - len(enc.clauses))
    json.dump(info, open(os.path.join(DATA, f'{tag}.info.json'), 'w'))
    print(json.dumps({k: v for k, v in info.items() if k != 'blocks'}))
    print(' '.join(files))
    return files


CASES = load_cases()

if __name__ == '__main__':
    work, out = sys.argv[1], sys.argv[2]
    DATA, SYM = os.path.join(work, 'data'), os.path.join(work, 'sym')
    for t in sys.argv[3:] or [t for t in CASES if t not in REUSE]:
        run(t, out)
