"""Save the completed round and an immutable observation of the running batch."""
from pathlib import Path
import datetime, hashlib, json, re, subprocess

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
read = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

def save(name, data):
    (HERE / 'data' / name).write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8')

assert not (HERE / 'data/checkpoint.json').exists()
assert not (HERE / 'data/check.lock').exists()
proof = read(HERE / 'data/proof-summary.json')
assert proof['status'] == 'PASS_THREE_COUNT_RESTRICTION'
assert len(proof['modules']) == 58 and len(proof['theorem_audits']) == 13
review = HERE / 'audit/final-review.md'
assert sha(review) == 'fed9b9e9ef13b555e5684a6e3f48efa5da14dcacb4e2ea3f09cb0173aa43983a'
prior_path = ROOT / 'milestones/110-critical-cycle-core-screen/data/checkpoint.json'
prior = read(prior_path)
paper = ROOT / 'paper/snake9_research.tex'
assert sha(paper) == prior['paper_sha256'] == sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))
family = read(HERE / 'data/family-profiles/results.json')
assert family['additional_removed'] == 7999 and family['edges'] == 4934590
assert [(p['mean'], p['range']) for p in family['profiles']] == [('3384/7', '3860/7'), ('496', '602')]

batch = ROOT / 'milestones/104-complete-potential-batch'
live = read(batch / 'data/batch-progress.json')
assert live['status'] == 'RUNNING'
raw = subprocess.check_output(['powershell', '-NoProfile', '-Command',
    f'Get-Process -Id {int(live["pid"])} -ErrorAction Stop | Select-Object Id,ProcessName,StartTime | ConvertTo-Json -Compress'], text=True)
process = json.loads(raw)
assert process['Id'] == live['pid'] and process['ProcessName'] == 'python'
observed = dict(recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(), verified_process=process, state=live)
tracked = set(subprocess.check_output(['git', '-c', 'core.commitGraph=false', 'ls-files', '--',
    'milestones/104-complete-potential-batch'], cwd=ROOT, text=True).splitlines())
extra = []
for group in live['selected']:
    rp = batch / 'data' / (group['module'] + '-audit.json')
    r = read(rp)
    assert sha(rp) == group['receipt_sha256'] and r['status'] == 'PASS_COMPLETE_BATCH_MODULE' and r['exit_code'] == 0
    assert sha(batch / 'lean' / (group['module'] + '.lean')) == r['source_sha256'] == sha(batch / r['source_snapshot'])
    assert sha(batch / r['log']) == r['log_sha256'] and sha(batch / 'build' / (group['module'] + '.olean')) == r['olean_sha256']
    for a in r['theorem_audits']:
        assert set(a['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
    for p in [rp, batch / r['log'], batch / r['source_snapshot'], (batch / r['source_snapshot']).parent / 'checker.py.txt']:
        if p.relative_to(ROOT).as_posix() not in tracked:
            extra.append(p)
refs = {ref: subprocess.check_output(['git', '-c', 'core.commitGraph=false', 'rev-parse', ref],
    cwd=ROOT, text=True).strip() for ref in ['HEAD', 'origin/main', 'origin/research/unconditional-241']}
assert refs['HEAD'] == refs['origin/main']
counts = live['contexts_checked_by_profile']
summary = f'''For canonical directions 012340, a new checked theorem requires the
second internal count to be at least 4, the third at least 3, or the
fourth at least 6. The outer two counts are unrestricted. The local
contradiction, actual-snake transfer and both graph orientations pass
Lean. There are 58 successful module records and 13 standard axiom
reports. The main contradiction has 2,040 clauses, 11,711 deductions
and 611,907 hints; independent replay passes. No mathematical definition
was introduced.

This restriction removes 1,462 additional graph keys beyond milestone
110, leaving 4,942,589. Its integer comparisons remain 235 and conditional
234. Four independently checked local witnesses rule out several stronger
local claims; their relaxed boundaries and multiple components prevent
interpreting them as complete snakes.

The proposed outer-sum lower bounds are 22 when the middle count is at
most 2, 19 when it is at most 3, and 17 without a middle restriction.
The sum-22 case has a complete native sorted-input contradiction with
71,388 deductions and 6,105,267 hints, independently reconstructed and
replayed. Concrete sum semantics, Lean replay and actual-snake transfer
remain pending. The generic counter-soundness helper is checked. The
two other sum cases have native UNSAT records without checked certificates.
Sorting retains all 84 literal occurrences, including seven duplicates.

Assuming all three sum bounds and their common coefficient-30 excess
argument removes 7,999 more graph keys, leaving 4,934,590. The completed
mean improves from 483 to 3384/7, with potential range 3860/7 and exact
comparison 1930913/8196. Its integer floor remains 235. A fourteen-edge
cycle attains the new mean. The conditional profile retains mean 496,
range 602 and floor 234. Every edge inequality was checked by the native
calculation; complete Lean graph certificates and the excess-budget
integration remain outstanding.

At the saved process-verified observation, milestone 104 was RUNNING with
{counts['completed']}/791 completed and {counts['conditional']}/791 conditional contexts
checked. Its active module was `{live['active']['module']}`. Preserve
that running batch. The reference union still has 1,366 unresolved entries.

The maintained range remains 191 through 235 edges, based on the
contributor proof and archived audit with a complete independent rebuild
pending. Conditional 234, the exact optimum and 196 remain unresolved.
Paper revision 106 is unchanged; the next full revision is 116. Large
proof artifacts have verified gzip archives, with raw originals retained
locally. Failed proof attempts preserve their original timeout status.
'''
latest = 'Latest continuation: [milestone 111](milestones/111-critical-count-intervals/README.md) proves a three-count restriction for actual snakes. Three proposed sum bounds improve the completed graph mean to 3384/7, while integer comparisons remain 235 and conditional 234. Sum proofs and the complete potential batch remain pending.'
priority = 'Next research priority: Inspect the new fourteen-edge obstruction and test a stronger count-sum family on both full profiles before expensive certificate export. The sum-22 native contradiction is ready for concrete semantics and Lean proof reduction; preserve its repeated literals and the running milestone 104 batch.'
updates = {}
for name in ['README.md', 'COLLABORATION.md']:
    path = ROOT / name
    txt = path.read_text(encoding='utf-8')
    for prefix, value in [('Latest continuation:', latest), ('Next research priority:', priority)]:
        txt, n = re.subn('^' + re.escape(prefix) + '.*$', lambda _: value, txt, count=1, flags=re.M)
        assert n == 1
    updates[path] = txt
path = ROOT / 'milestones/README.md'
txt = path.read_text(encoding='utf-8')
i = txt.index('- [Milestone 110:')
assert '- [Milestone 111:' not in txt
updates[path] = txt[:i] + '- [Milestone 111: three-count restriction and sum family](111-critical-count-intervals/README.md). A checked local theorem and a conditional fractional graph improvement; integer comparisons remain 235 and 234.\n\n' + txt[i:]
path = ROOT / 'RESEARCH_LEDGER.md'
txt = path.read_text(encoding='utf-8')
assert '## Milestone 111:' not in txt
updates[path] = txt + '\n\n## Milestone 111: three-count restriction and conditional sum family\n\n' + summary + '\n' + priority + '\n'
path = ROOT / 'handoff/CURRENT_STATUS.md'
txt = path.read_text(encoding='utf-8')
i = txt.index('## Milestone 110 checkpoint')
assert '## Milestone 111 checkpoint' not in txt
updates[path] = txt[:i] + '## Milestone 111 checkpoint\n\n' + summary + '\nEarlier checkpoint sections below are historical snapshots.\n\n' + txt[i:]
templates = {ROOT / 'handoff' / name: (HERE / 'handoff-templates' / name).read_bytes()
    for name in ['README.md', 'NEXT_AGENT_PROMPT.md']}
checkpoint = dict(status='PASS_THREE_COUNT_RESTRICTION_AND_CONDITIONAL_FAMILY_TEST', previous_goal_turn='progress',
    recorded_at=observed['recorded_at'], prior_checkpoint=prior_path.relative_to(ROOT).as_posix(), prior_checkpoint_sha256=sha(prior_path),
    proof_summary_sha256=sha(HERE / 'data/proof-summary.json'), final_review_sha256=sha(review),
    mathematical_note_sha256=sha(HERE / 'mathematical-note.md'), family_result_sha256=sha(HERE / 'data/family-profiles/results.json'),
    combined_result_sha256=sha(HERE / 'data/combined-experiment.json'), archives_sha256=sha(HERE / 'data/large-artifact-archives.json'),
    checked_final_modules=58, theorem_axiom_audits=13, new_mathematical_definitions=0,
    remaining_reference_entries=1366, recovered_reference_indices=prior['recovered_reference_indices'],
    actual_snake_checked=True, directions=proof['directions'], count_bounds=proof['bounds'],
    additional_excluded_keys=1462, total_excluded_keys=4419, restricted_graph_keys=4942589,
    conditional_family_additional_exclusions=7999, conditional_family_total_exclusions=12418, conditional_family_graph_keys=4934590,
    family_profile_comparisons=[dict(profile='completed', mean='3384/7', range='3860/7', comparison='1930913/8196', integer=235),
        dict(profile='conditional', mean='496', range='602', comparison='551765/2348', integer=234)],
    sorted_sum_native_replay=True, sum_inequalities_lean_checked=False, excess_budget_lean_checked=False,
    complete_restricted_graph_lean_certificate=False, maintained_interval=[191, 235], conditional_target=234,
    upper_bound_evidence='Contributor proof and archived audit; complete independent rebuild pending.',
    exact_optimum_unresolved=True, paper_revision=106, next_paper_revision=116, paper_sha256=sha(paper), git_refs_before_commit=refs,
    scope='One new actual-snake restriction and a conditional fractional improvement in the finite graph. No improved integer snake bound. Sum theorems, excess integration, residual reference union and complete graph certificates remain unresolved.')
save('batch-observation.json', observed)
checkpoint['batch_observation_sha256'] = sha(HERE / 'data/batch-observation.json')
save('additional-batch-evidence.json', [p.relative_to(ROOT).as_posix() for p in sorted(set(extra))])
for path, txt in updates.items():
    path.write_text(txt, encoding='utf-8')
for path, raw in templates.items():
    path.write_bytes(raw)
save('checkpoint.json', checkpoint)
print(json.dumps(dict(status=checkpoint['status'], batch_counts=counts, additional_batch_files=len(set(extra))), indent=2))
