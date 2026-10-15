"""Translate positive-hint RUP certificates to ordinary Lean proof terms.

Each derived clause is a separate theorem under the original CNF hypothesis.
Disjunction elimination replaces repeated simplifier calls and a giant final
local context. The generator is untrusted; Lean checks every emitted proof.
"""
import argparse
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--prefix', required=True)
parser.add_argument('--module', required=True)
parser.add_argument('--output-dir', default='work/final_lean')
parser.add_argument('--structured', action='store_true', help='Use small proposition records instead of a long CNF list')
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
assert steps and not steps[max(steps)][0]
needed = {max(steps)}
todo = list(needed)
while todo:
    k = todo.pop()
    if k <= n:
        continue
    for h in steps[k][1]:
        assert h > 0, 'Only positive-hint RUP is supported'
        if h not in needed:
            needed.add(h)
            todo.append(h)
original = sorted(k for k in needed if k <= n)
derived = sorted(k for k in needed if k > n)
ids = {k: i+1 for i, k in enumerate(original+derived)}
clauses = [data['clauses'][k-1] for k in original]
proof = [(ids[k], steps[k][0], [ids[h] for h in steps[k][1]]) for k in derived]
Path(args.prefix+'_core.json').write_text(json.dumps({
    'original_clause_indices': original, 'clauses': clauses,
    'reasons': [data['reasons'][k-1] for k in original], 'proof': proof,
    'scope': 'CNF only; geometric interpretation remains to be checked.'},
    separators=(',', ':')), encoding='utf-8')


def prop(c):
    return ' ∨ '.join(f'p {abs(v)} = {str(v > 0).lower()}' for v in c) or 'False'


def literals(c):
    return '['+', '.join(f'({abs(v)}, {str(v > 0).lower()})' for v in c)+']'


def inject(index, size, term):
    if size == 1:
        return term
    if index == 0:
        return f'(Or.inl {term})'
    return f'(Or.inr {inject(index-1, size-1, term)})'


def eliminate(clause, term, assigned, unknown, depth=0):
    def branch(v, name):
        if v == unknown:
            return name
        known = assigned[abs(v)][1]
        contradiction = f'(bool_contra {name} {known})' if v > 0 else f'(bool_contra {known} {name})'
        return contradiction if unknown is None else f'(False.elim {contradiction})'
    if len(clause) == 1:
        return branch(clause[0], term)
    name, tail = f'l{depth}', f'r{depth}'
    return f'(Or.elim {term} (fun {name} => {branch(clause[0], name)}) (fun {tail} => {eliminate(clause[1:], tail, assigned, unknown, depth+1)}))'


out = ['import Std', 'import Std.Sat.CNF', '', 'namespace '+args.module,
       'open Std.Sat', 'set_option maxHeartbeats 0', 'set_option maxRecDepth 1000000',
       'set_option linter.unnecessarySimpa false', '',
       '-- Explicit Boolean formula; geometric interpretation is a separate obligation.',
       'def formula : CNF Nat := [']
out += ['  '+literals(c)+(',' if i+1 < len(clauses) else '') for i, c in enumerate(clauses)]
out += [']', '',
        'private theorem bool_contra {b : Bool} (ht : b = true) (hf : b = false) : False :=',
        '  Bool.noConfusion (ht.symm.trans hf)', '',
        'private theorem bool_false_of_not_true {b : Bool} (h : ¬ b = true) : b = false := by',
        '  cases b <;> simp_all', '',
        'private theorem bool_true_of_not_false {b : Bool} (h : ¬ b = false) : b = true := by',
        '  cases b <;> simp_all', '',
        'private theorem input_at (p : Nat → Bool) (h : formula.Sat p)',
        '    (i : Nat) (hi : i < formula.length) : (formula[i]).eval p = true :=',
        '  List.all_eq_true.mp h _ (List.getElem_mem hi)', '']
if args.structured:
    out = out[:out.index('-- Explicit Boolean formula; geometric interpretation is a separate obligation.')]
    out += ['-- Exact clauses grouped into records to keep projection checking bounded.']
    for start in range(0, len(clauses), 32):
        out += [f'structure Block{start//32} (p : Nat → Bool) : Prop where']
        out += [f'  clause{i+1} : {prop(clauses[i])}' for i in range(start, min(start+32, len(clauses)))]
        out += ['']
    out += ['structure Constraints (p : Nat → Bool) : Prop where']
    out += [f'  block{j} : Block{j} p' for j in range((len(clauses)+31)//32)]
    out += ['',
            'private theorem bool_contra {b : Bool} (ht : b = true) (hf : b = false) : False :=',
            '  Bool.noConfusion (ht.symm.trans hf)', '',
            'private theorem bool_false_of_not_true {b : Bool} (h : ¬ b = true) : b = false := by',
            '  cases b <;> simp_all', '',
            'private theorem bool_true_of_not_false {b : Bool} (h : ¬ b = false) : b = true := by',
            '  cases b <;> simp_all', '']
hypothesis = 'Constraints p' if args.structured else 'formula.Sat p'
all_clauses = {}
for i, c in enumerate(clauses, 1):
    all_clauses[i] = c
    if args.structured:
        out += [f'private theorem step{i} (p : Nat → Bool) (h : Constraints p) : {prop(c)} := h.block{(i-1)//32}.clause{i}', '']
        continue
    out += [f'private theorem step{i} (p : Nat → Bool) (h : formula.Sat p) : {prop(c)} := by',
            f'  have hc := input_at p h {i-1} (by decide)',
            f'  change CNF.Clause.eval p ({literals(c)} : CNF.Clause Nat) = true at hc',
            '  simpa only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_eq_true, beq_iff_eq, Bool.false_eq_true, or_false] using hc', '']
for k, c, hs in proof:
    out += [f'private theorem step{k} (p : Nat → Bool) (h : {hypothesis}) : {prop(c)} := by']
    assigned = {}
    if c:
        out += ['  apply Classical.byContradiction', '  intro hc']
        for i, v in enumerate(c):
            conversion = 'bool_false_of_not_true' if v > 0 else 'bool_true_of_not_false'
            out += [f'  have u{i} : {prop([-v])} := {conversion} (fun hl => hc {inject(i,len(c),"hl")})']
            assigned[abs(v)] = (v < 0, f'u{i}')
    closed = False
    for j, h in enumerate(hs):
        clause = all_clauses[h]
        assert not any(abs(v) in assigned and assigned[abs(v)][0] == (v > 0) for v in clause)
        unknown = [v for v in clause if abs(v) not in assigned]
        assert len(unknown) <= 1
        term = eliminate(clause, f'(step{h} p h)', assigned, unknown[0] if unknown else None)
        if not unknown:
            out += [f'  exact {term}', '']
            closed = True
            break
        v = unknown[0]
        out += [f'  have t{j} : {prop([v])} := {term}']
        assigned[abs(v)] = (v > 0, f't{j}')
    assert closed
    all_clauses[k] = c
out += ['theorem formula_unsat : formula.Unsat := by',
        '  intro p', '  apply Bool.eq_false_iff.mpr', f'  exact step{proof[-1][0]} p', '',
        '#print axioms formula_unsat', 'end '+args.module, '']
if args.structured:
    out = out[:out.index('theorem formula_unsat : formula.Unsat := by')]
    out += ['theorem constraints_unsat (p : Nat → Bool) : ¬ Constraints p :=',
            f'  step{proof[-1][0]} p', '', '#print axioms constraints_unsat',
            'end '+args.module, '']
target = Path(args.output_dir)/(args.module+'.lean')
target.parent.mkdir(parents=True, exist_ok=True)
target.write_text('\n'.join(out), encoding='utf-8')
print(f'{args.module}: {len(clauses)} input clauses, {len(proof)} RUP proof steps')
