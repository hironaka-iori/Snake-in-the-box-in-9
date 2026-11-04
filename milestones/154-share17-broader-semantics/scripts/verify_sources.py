"""Check prepared-source identity and interpretation scope without Lean."""
from pathlib import Path
import hashlib, json, re

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
P = R / 'milestones/153-pair-conditioned-share17'
read = lambda p: json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
plan = read(H / 'data/source-plan.json')
assert plan['status'] == 'PREPARED_BROADER_SHARE17_SEMANTICS_UNCHECKED'
assert not plan['checked'] and not plan['Lean_started']
assert plan['bounds'] == [[4, 4], [0, 4], [4, 4], [0, 5], [3, 3]]
assert plan['counter_count'] == 9 and plan['semantic_variables'] == 6396
assert len(plan['module_order']) == len(plan['artifacts']) == 97
assert plan['shared_cnf_constant'] == 'Snake9.LocalWindow.ShareWindow153.cnf'
for p, digest in plan['source_files_sha256'].items():
    assert sha(R / p) == digest, p
texts = {}
for row in plan['artifacts']:
    p = H / row['path']
    assert p.stat().st_size == row['bytes'] and sha(p) == row['sha256'], p
    texts[row['module']] = p.read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', texts[row['module']]), p
assert not any((H / 'lean').rglob('*.olean'))
assert not (H / 'lean/LocalWindowCnf').exists()
for i in range(93):
    assert f'tags{i} ShareWindow153.raw{i}' in texts[f'Share154.Shard{i:02d}']
sem = texts['Share154.Semantics154']
assert '(h : Unsat ShareWindow153.cnf)' in sem
assert 'RefutedShare window bounds resolution cap' in sem
adapter = texts['CriticalShareAdapter154']
assert '(hunsat : Unsat ShareWindow153.cnf)' in adapter
assert 'ShareWindow154.local_share17_of_core_unsat154 hunsat' in adapter
assert 'Share153.Semantics153' not in adapter
forward = '''coreAlpha p (r+1) = 4 ∧ coreAlpha p (r+2) ≤ 4 ∧
        coreAlpha p (r+3) = 4 ∧ coreAlpha p (r+4) ≤ 5 ∧
        coreAlpha p (r+5) = 3'''
reverse = '''coreAlpha p (r+1) = 3 ∧ coreAlpha p (r+2) ≤ 5 ∧
        coreAlpha p (r+3) = 4 ∧ coreAlpha p (r+4) ≤ 4 ∧
        coreAlpha p (r+5) = 4'''
assert forward in adapter and reverse in adapter
old = read(P / 'data/semantic-source-plan.json')
for row in old['artifacts']:
    assert sha(P / row['path']) == row['sha256'], row['path']
report = dict(status='PASS_PREPARED_SOURCE_IDENTITY_ONLY', Lean_started=False,
              new_modules=97, source_bytes=sum(x['bytes'] for x in plan['artifacts']),
              original_153_source_artifacts_unchanged=True,
              shared_CNF_preserved=True, counter_count=9,
              forward_and_reverse_intervals_checked_as_source=True,
              actual_snake_theorem_complete=False, new_global_upper_bound=False,
              plan_sha256=sha(H / 'data/source-plan.json'),
              checker_sha256=sha(Path(__file__)),
              scope='Source hashes, clause references, proof-premise boundary, and interval orientation only. No Lean acceptance or new mathematical theorem is claimed.')
target = H / 'data/source-check.json'
content = json.dumps(report, indent=2) + '\n'
if target.exists():
    assert target.read_text(encoding='utf-8') == content
else:
    target.write_text(content, encoding='utf-8', newline='\n')
print(json.dumps(report))
