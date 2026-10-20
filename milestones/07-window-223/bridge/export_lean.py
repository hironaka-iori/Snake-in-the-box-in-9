"""Export data/<tag>.cnf + data/<tag>.lrat (drat-trim -L output) to Lean modules <Mod>/*.lean.
Untrusted: every emitted step is re-checked by the Lean kernel.
usage: export_lean.py tag Mod steps_per_module"""
import sys, json, hashlib, os
tag, mod, per = sys.argv[1], sys.argv[2], int(sys.argv[3])
CH = 48  # input clauses per chunk
cnfp, lratp = f'data/{tag}.cnf', f'data/{tag}.lrat'
sha = hashlib.sha256(open(cnfp, 'rb').read()).hexdigest()
clauses = [list(map(int, l.split()))[:-1] for l in open(cnfp) if l[0] not in 'pc']
ncl = len(clauses)
steps = []
for line in open(lratp):
    t = line.split()
    if t[1] == 'd': continue
    xs = list(map(int, t)); z = xs.index(0, 1)
    sid, c, hs = xs[0], xs[1:z], xs[z+1:-1]
    assert sid > ncl and all(h > 0 for h in hs), 'RAT/odd step'
    steps.append((sid, c, hs))
assert steps[-1][1] == [], 'last step must be the empty clause'
used = sorted({h for _, _, hs in steps for h in hs if h <= ncl})
meta = json.load(open(f'data/{tag}.meta.json'))
def mask(c):
    p = n = 0
    for l in c:
        if l > 0: p |= 1 << l
        else: n |= 1 << -l
    return p, n
os.makedirs(mod, exist_ok=True)
hdr = f'import WinRup\nset_option maxRecDepth 100000\nset_option Elab.async false\nset_option maxHeartbeats 0\nnamespace {mod}\nopen WinCNF WinRup\n'
# ---- inputs
chunks = [used[i:i+CH] for i in range(0, len(used), CH)]
s = f'import WinRup\nset_option maxRecDepth 100000\nset_option Elab.async false\nnamespace {mod}\nopen WinCNF WinRup\n'
s += f'/-! Input clauses of `{tag}`: the {len(used)} clauses (of {ncl}) of the wincert CNF\n'
s += f'`data/{tag}.cnf` (sha256 {sha}) that the trimmed LRAT proof uses,\n'
usha = hashlib.sha256(''.join(' '.join(map(str, clauses[i-1])) + ' 0\n' for i in used).encode()).hexdigest()
s += f'sha256 of these clauses as DIMACS lines `l1 l2 ... 0` (one per line, this order): {usha};\n'
s += f'in their original order and DIMACS numbering (window {meta["window"]}, alpha {meta["alpha"]}, radius 3). -/\n'
for k, ch in enumerate(chunks):
    s += f'/-- original clause indices {ch[0]}..{ch[-1]} -/\n'
    s += f'def G{k} : CNF := [' + ', '.join('[' + ', '.join(f'pos {l}' if l > 0 else f'neg {-l}' for l in clauses[i-1]) + ']' for i in ch) + ']\n'
s += f'/-- The used clauses (original 1-based indices in `idx`). -/\ndef F : CNF := ' + ' ++ ('.join(f'G{k}' for k in range(len(chunks))) + ')' * (len(chunks) - 1) + '\n'
s += 'def idx : List Nat := [' + ', '.join(map(str, used)) + ']\n'
s += 'def kinds : List String := [' + ', '.join('"%s"' % meta['kinds'][i-1] for i in used) + ']\n'
s += 'noncomputable section\n'
for k, ch in enumerate(chunks):
    for i in ch:
        p, n = mask(clauses[i-1]); s += f'def c{i} : Mask := ({p}, {n})\n'
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
for k, ch in enumerate(chunks):
    for r, i in enumerate(ch):
        s += f'theorem d{i} (τ : Nat → Bool) (h : Inp τ) : msat τ c{i} := h' + '.2' * k + '.1' + '.2' * r + '.1\n'
s += f'end {mod}\n'
open(f'{mod}/Inputs.lean', 'w').write(s)
# ---- steps (one `rup_step` command per LRAT step, modules cut at ~HB hints)
HB = int(sys.argv[4]) if len(sys.argv) > 4 else 100000
mods = []
prev = f'{mod}.Inputs'
H = 0
groups, cur, ch = [], [], 0
for st in steps:
    cur.append(st); ch += len(st[2])
    if ch >= HB or len(cur) >= per: groups.append(cur); cur, ch = [], 0
if cur: groups.append(cur)
for m, grp in enumerate(groups):
    name = f'S{m:02d}'; mods.append(name)
    s = f'import {prev}\nimport WinRupCmd\nset_option Elab.async false\nnamespace {mod}\n'
    s += f'-- LRAT steps {grp[0][0]}..{grp[-1][0]}: rup_step id posMask negMask [hint ids]\n'
    for sid, c, hs in grp:
        p, n = mask(c); H += len(hs)
        s += f'rup_step {sid} {p} {n} [' + ' '.join(map(str, hs)) + ']\n'
    s += f'end {mod}\n'
    open(f'{mod}/{name}.lean', 'w').write(s)
    prev = f'{mod}.{name}'
last = steps[-1][0]
s = f'import {prev}\nopen WinCNF WinRup\n'
s += (f'/-- The used-clause CNF `{mod}.F` of `{tag}` (window {meta["window"]}, alpha (2,2,3), radius 3)\n'
      f'is unsatisfiable: {len(steps)} RUP steps, {H} hints, each checked by the kernel. -/\n'
      f'theorem {tag}_unsat : unsat {mod}.F :=\n  fun τ hF => msat_empty ({mod}.d{last} τ ({mod}.inp_of τ hF))\n')
open(f'{mod}/Main.lean', 'w').write(s)
json.dump(dict(tag=tag, cnf_sha256=sha, used=[dict(index=i, kind=meta['kinds'][i-1], lits=clauses[i-1]) for i in used]),
          open(f'data/{tag}.used.json', 'w'))
print(tag, 'inputs', len(used), 'chunks', len(chunks), 'steps', len(steps), 'hints', H, 'modules', len(mods))
print(' '.join([f'{mod}/Inputs.lean'] + [f'{mod}/{x}.lean' for x in mods] + [f'{mod}/Main.lean']))
