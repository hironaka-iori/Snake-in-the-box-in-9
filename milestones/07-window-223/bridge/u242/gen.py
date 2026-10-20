"""Generate the Lean modules (G2 refutation + G1 tables/checks) for the 242/241 window CNFs.

Inputs: data/<tag>.cnf, data/<tag>.drup (the committed milestones/10-window-aggregate certificates,
sha256-checked against data/certificates.json) and data/<tag>.lrat (drat-trim -L output).
The wincert.Encoding of each case is rebuilt (with a recording `atmost`) and must reproduce the
certified CNF up to the trailing cycle cuts.  Everything emitted is untrusted: the Lean kernel
re-checks every RUP step (G2) and every clause against the G1 checker.

usage: python3 -I gen.py OUTDIR TAG...   (TAG from CASES; default all)
Writes OUTDIR/<Mod>Inputs.lean, <Mod>S00..lean, <Mod>Main.lean, <Mod>G1.lean, <Mod>G1C<k>.lean.
"""
import sys, json, hashlib, os
sys.path.insert(0, '/home/user/Snake-in-the-box-in-9/milestones/10-window-aggregate/scripts')
from wincert import Encoding, window_from_dirs

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, '..', 'data')
CERT = '/home/user/Snake-in-the-box-in-9/milestones/10-window-aggregate/data/certificates.json'
CASES = {
    '224_fwd_repeated': ('W224Rep', [0, 1, 2, 0], [2, 2, 4]),
    '224_fwd_distinct': ('W224Dis', [0, 1, 2, 3], [2, 2, 4]),
    '232_fwd_repeated': ('W232Rep', [0, 1, 2, 0], [2, 3, 2]),
    '232_fwd_distinct': ('W232Dis', [0, 1, 2, 3], [2, 3, 2]),
    '323_fwd_repeated': ('W323Rep', [0, 1, 2, 0], [3, 2, 3]),
    '323_fwd_distinct': ('W323Dis', [0, 1, 2, 3], [3, 2, 3]),
    '41c_fwd_repeated': ('W41cRep', [0, 1, 2, 0], [4, 1, (4, 6)]),
    '41c_fwd_distinct': ('W41cDis', [0, 1, 2, 3], [4, 1, (4, 6)]),
    '2423_fwd_s01203': ('W2423A', [0, 1, 2, 0, 3], [2, 4, 2, 3]),
    '2423_fwd_s01230': ('W2423B', [0, 1, 2, 3, 0], [2, 4, 2, 3]),
    '2423_fwd_s01234': ('W2423C', [0, 1, 2, 3, 4], [2, 4, 2, 3]),
    '2423_rev_s01203': ('W3242A', [0, 1, 2, 0, 3], [3, 2, 4, 2]),
}
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


def L(xs): return '[' + ', '.join(map(str, xs)) + ']'
def lit(l): return f'pos {l}' if l > 0 else f'neg {-l}'


def mask(c):
    p = n = 0
    for l in c:
        if l > 0: p |= 1 << l
        else: n |= 1 << -l
    return p, n


def run(tag, out):
    mod, dirs, alpha = CASES[tag]
    cert = {c['case']: c for c in json.load(open(CERT))['cases']}[tag]
    cnfp, prfp, lratp = (os.path.join(DATA, f'{tag}.{e}') for e in ('cnf', 'drup', 'lrat'))
    raw = open(cnfp, 'rb').read()
    sha = hashlib.sha256(raw).hexdigest()
    assert sha == cert['cnf_sha256'], tag
    assert hashlib.sha256(open(prfp, 'rb').read()).hexdigest() == cert['drup_sha256'], tag
    clauses = [list(map(int, l.split()))[:-1] for l in raw.decode().splitlines() if l and l[0] not in 'pc']
    enc = Rec(window_from_dirs(dirs), alpha, 3)
    assert enc.window == cert['window'] and [list(a) if isinstance(a, tuple) else a for a in alpha] == cert['alpha']
    assert clauses[:len(enc.clauses)] == enc.clauses, tag
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
    CH = CH0
    chunks = [used[i:i + CH] for i in range(0, len(used), CH)]
    usha = hashlib.sha256(''.join(' '.join(map(str, clauses[i - 1])) + ' 0\n' for i in used).encode()).hexdigest()
    s = f'import WinRup\nset_option maxRecDepth 100000\nset_option Elab.async false\nnamespace {mod}\nopen WinCNF WinRup\n'
    s += f'/-! Input clauses of `{tag}`: the {len(used)} clauses (of {ncl}) of the certified wincert CNF\n'
    s += f'`milestones/10-window-aggregate/certificates/{tag}.cnf.gz` (sha256 {sha}) that the trimmed LRAT proof uses,\n'
    s += f'sha256 of these clauses as DIMACS lines `l1 l2 ... 0` (one per line, this order): {usha};\n'
    s += f'in their original order and DIMACS numbering (window {enc.window}, alpha {cert["alpha"]}, radius 3). -/\n'
    for k, ch in enumerate(chunks):
        s += f'/-- original clause indices {ch[0]}..{ch[-1]} -/\n'
        s += f'def G{k} : CNF := [' + ', '.join('[' + ', '.join(lit(l) for l in clauses[i - 1]) + ']' for i in ch) + ']\n'
    s += '/-- The used clauses (original 1-based indices in `idx`). -/\ndef F : CNF := ' + ' ++ ('.join(f'G{k}' for k in range(len(chunks))) + ')' * (len(chunks) - 1) + '\n'
    s += 'def idx : List Nat := [' + ', '.join(map(str, used)) + ']\n'
    s += 'def kinds : List String := [' + ', '.join('"%s"' % kinds[i - 1] for i in used) + ']\n'
    s += 'noncomputable section\n'
    for k, ch in enumerate(chunks):
        for i in ch:
            p, n = mask(clauses[i - 1]); s += f'def c{i} : Mask := ({p}, {n})\n'
        s += f'def M{k} : List Mask := [' + ', '.join(f'c{i}' for i in ch) + ']\n'
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
        open(f'{out}/{mod}Inputs.lean', 'w').write(s); files.append(f'{mod}Inputs')
        prev = f'{mod}Inputs'
    else:  # big case: the `d` lemmas go to two further modules (one module overflows the stack)
        s += f'end {mod}\n'
        open(f'{out}/{mod}Inputs.lean', 'w').write(s); files.append(f'{mod}Inputs')
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
    s += f'def ballL : List Nat := {L(enc.ball)}\n'
    s += f'def endsL : List Nat := {L(ends)}\n'
    for t, (b, k, l, kd) in enumerate(enc.blocks):
        s += f'/-- {kd} -/\n'
        s += f'def B{t} : Block := ⟨{b}, {k}, {len(l)}, [' + ', '.join(lit(x) for x in l) + ']⟩\n'
    s += 'def blocks : List Block := [' + ', '.join(f'B{t}' for t in range(len(enc.blocks))) + ']\n'
    s += f'def T : Tables := ⟨{nb}, {ne}, ballL, endsL, {L(enc.window)}, blocks⟩\n'
    s += 'theorem blocksOK_T : blocksOK T = true := by decide +kernel\n'
    s += f'end {mod}\n'
    open(f'{out}/{mod}G1.lean', 'w').write(s); files.append(f'{mod}G1')
    # ---------------- G1 checks, CHK chunks per module
    cm = [list(range(i, min(i + CHK, len(chunks)))) for i in range(0, len(chunks), CHK)]
    for j, ks in enumerate(cm):
        s = f'import {mod}G1\nnamespace {mod}\nopen WinCNF W223G1\nset_option maxRecDepth 100000\n'
        for k in ks:
            s += f'theorem chk{k} : G{k}.all (check T) = true := by decide +kernel\n'
        s += f'end {mod}\n'
        open(f'{out}/{mod}G1C{j}.lean', 'w').write(s); files.append(f'{mod}G1C{j}')
    s = ''.join(f'import {mod}G1C{j}\n' for j in range(len(cm)))
    s += f'import {mod}Main\nnamespace {mod}\nopen WinCNF W223G1\n'
    s += 'theorem check_T : F.all (check T) = true := by\n  simp only [F, List.all_append, ' + ', '.join(f'chk{k}' for k in range(len(chunks))) + ', Bool.and_self]\n'
    rng = ' '.join(f'{a} {a}' if isinstance(a, int) else f'{a[0]} {a[1]}' for a in alpha)
    if len(alpha) == 3:
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


if __name__ == '__main__':
    out = sys.argv[1]
    order = []
    for t in sys.argv[2:] or CASES:
        order += run(t, out)
    open(os.path.join(out, 'order_' + ('_'.join(sys.argv[2:]) if sys.argv[2:] else 'all') + '.txt'), 'w').write('\n'.join(order) + '\n')
