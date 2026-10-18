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
# Retain only propagation steps that support the final conflict of each RUP proof.
# This is an untrusted optimization: each retained step is still checked in Lean.
all_raw = {i: c for i, c in enumerate(data['clauses'], 1)}
all_raw.update({i: c for i, (c, _) in steps.items()})
raw_hint_count = sum(len(hs) for _, hs in steps.values())
for identifier, (target_clause, hints) in list(steps.items()):
    assigned = {abs(v): (v < 0, None) for v in target_clause}
    parents = {}
    final_hint = None
    for hint in hints:
        assert hint > 0, 'Only positive-hint RUP is supported'
        clause = all_raw[hint]
        assert not any(abs(v) in assigned and assigned[abs(v)][0] == (v > 0) for v in clause)
        unknown = [v for v in clause if abs(v) not in assigned]
        assert len(unknown) <= 1
        parents[hint] = {assigned[abs(v)][1] for v in clause if abs(v) in assigned} - {None}
        if not unknown:
            final_hint = hint
            break
        literal = unknown[0]
        assigned[abs(literal)] = (literal > 0, hint)
    assert final_hint is not None
    used, pending = set(), [final_hint]
    while pending:
        hint = pending.pop()
        if hint in used:
            continue
        used.add(hint)
        pending.extend(parents[hint])
    steps[identifier] = (target_clause, [hint for hint in hints if hint in used])
print(f'Propagation hints: {raw_hint_count} -> {sum(len(hs) for _, hs in steps.values())}')
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


print(len(original), len(derived), sum(len(hs) for _,_,hs in proof), flush=True)
