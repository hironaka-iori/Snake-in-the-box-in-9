"""Trim positive-hint LRAT by dependency and export a kernel-reducible Lean check.

The generated theorem concerns the explicit CNF core only. The script also saves
original clause indices/reasons to support the unfinished geometric soundness proof.
"""
import json
import argparse
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--prefix', default='outputs/ball_certificate')
parser.add_argument('--module', default='BallCertificate')
args = parser.parse_args()
data = json.loads(Path(args.prefix+'.json').read_text(encoding='utf-8'))
n = len(data['clauses'])
steps = {}
for line in Path(args.prefix+'.lrat').read_text(encoding='utf-8').splitlines():
    fields = line.split()
    if fields[1] == 'd':
        continue
    a = list(map(int, fields))
    z = a.index(0)
    steps[a[0]] = (a[1:z], a[z+1:-1])
assert not steps[max(steps)][0]
needed = {max(steps)}
todo = list(needed)
while todo:
    k = todo.pop()
    if k <= n:
        continue
    for h in steps[k][1]:
        assert h > 0, 'Only RUP certificates are supported'
        if h not in needed:
            needed.add(h)
            todo.append(h)
original = sorted(k for k in needed if k <= n)
derived = sorted(k for k in needed if k > n)
ids = {k: i+1 for i, k in enumerate(original + derived)}
clauses = [data['clauses'][k-1] for k in original]
proof = [(ids[k], steps[k][0], [ids[h] for h in steps[k][1]]) for k in derived]
core = {'original_clause_indices': original, 'clauses': clauses,
        'reasons': [data['reasons'][k-1] for k in original], 'proof': proof,
        'scope': 'Explicit CNF core only; no geometric reduction is certified.'}
Path(args.prefix+'_core.json').write_text(json.dumps(core, indent=2), encoding='utf-8')

def array(xs):
    return '#[' + ', '.join(map(str, xs)) + ']'

def prop(c):
    return ' ∨ '.join(f'p {abs(v)} = {str(v>0).lower()}' for v in c) or 'False'

all_clauses = {i+1: c for i,c in enumerate(clauses)}
out = ['import Std', 'import Std.Sat.CNF', '',
       'namespace '+args.module, 'open Std.Sat',
       'set_option maxHeartbeats 0', 'set_option maxRecDepth 1000000',
       'set_option linter.unnecessarySimpa false', '',
       '-- The CNF core is checked; the link to cube geometry is still pending.',
       'def formula : CNF Nat := [']
out += ['  [' + ', '.join(f'({abs(v)}, {str(v>0).lower()})' for v in c) + ']' +
        (',' if i+1 < len(clauses) else '') for i, c in enumerate(clauses)]
out += [']', '']
for k,c,hs in proof:
    out += [f'private theorem step{k} (p : Nat → Bool)']
    out += [f'    (h{h} : {prop(all_clauses[h])})' for h in dict.fromkeys(hs)]
    out += [f'    : {prop(c)} := by']
    assigned = {}
    if c:
        out += ['  apply Classical.byContradiction', '  intro hc',
                '  simp only [not_or, Bool.not_eq_true, Bool.not_eq_false] at hc']
        if len(c)>1:
            out += ['  rcases hc with ⟨'+', '.join(f'u{i}' for i in range(len(c)))+'⟩']
        for i,v in enumerate(c):assigned[abs(v)]=(v<0, f'u{i}' if len(c)>1 else 'hc')
    closed=False
    for j,h in enumerate(hs):
        clause=all_clauses[h]
        assert not any(abs(v) in assigned and assigned[abs(v)][0]==(v>0) for v in clause), (k,h,'already true')
        unknown=[v for v in clause if abs(v) not in assigned]
        assert len(unknown)<=1,(k,h,unknown)
        facts=list(dict.fromkeys(assigned[abs(v)][1] for v in clause if abs(v) in assigned))
        simp=', '.join(facts+['Bool.false_eq_true', 'Bool.true_eq_false', 'false_or', 'or_false'])
        if not unknown:
            out += [f'  simpa only [{simp}] using h{h}', '']
            closed=True;break
        v=unknown[0]
        out += [f'  have t{j} : {prop([v])} := by', f'    simpa only [{simp}] using h{h}']
        assigned[abs(v)]=(v>0,f't{j}')
    assert closed,k
    all_clauses[k]=c
out += ['theorem formula_unsat : formula.Unsat := by',
        '  intro p', '  apply Bool.eq_false_iff.mpr', '  intro h',
        '  simp only [CNF.eval, formula, List.all_cons, List.all_nil, Bool.and_eq_true, and_true] at h',
        '  rcases h with ⟨' + ', '.join(f'c{i}' for i in range(1,len(clauses)+1)) + '⟩']
for i,c in enumerate(clauses,1):
    out += [f'  have h{i} : {prop(c)} := by',
            f'    simpa only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_eq_true, beq_iff_eq, Bool.false_eq_true, or_false] using c{i}']
for k,c,hs in proof:
    out += [f'  have h{k} := step{k} p '+ ' '.join(f'h{h}' for h in dict.fromkeys(hs))]
out += [f'  exact h{proof[-1][0]}', '', '#print axioms formula_unsat', 'end '+args.module, '']
Path('work/final_lean/'+args.module+'.lean').write_text('\n'.join(out), encoding='utf-8')
print(f'Exported {len(clauses)} original clauses and {len(proof)} ordinary Lean proof steps')
