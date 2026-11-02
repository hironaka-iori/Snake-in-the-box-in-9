"""Freeze the relaxed exclusion and save a process-verified batch observation."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
save=lambda name,data:(HERE/'data'/name).write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
assert not (HERE/'data/checkpoint.json').exists() and not (HERE/'data/check.lock').exists()
proof=read(HERE/'data/proof-summary.json')
assert proof['status']=='PASS_RELAXED_EXCLUSION_AND_EIGHT_REFERENCE_ENTRIES'
assert (HERE/'audit/final-review.md').exists()
prior_path=ROOT/'milestones/107-reference-refutation-recovery/data/checkpoint.json';prior=read(prior_path)
assert sha(ROOT/'paper/snake9_research.tex')==prior['paper_sha256']==sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))
batch=ROOT/'milestones/104-complete-potential-batch';live=read(batch/'data/batch-progress.json')
assert live['status']=='RUNNING'
raw=subprocess.check_output(['powershell','-NoProfile','-Command',f'Get-Process -Id {int(live["pid"])} -ErrorAction Stop | Select-Object Id,ProcessName,StartTime | ConvertTo-Json -Compress'],text=True)
process=json.loads(raw);assert process['Id']==live['pid'] and process['ProcessName']=='python'
snapshot=dict(recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),verified_process=process,state=live)
save('batch-observation.json',snapshot)
tracked=set(subprocess.check_output(['git','-c','core.commitGraph=false','ls-files','--','milestones/104-complete-potential-batch'],cwd=ROOT,text=True).splitlines())
extra=[]
for group in live['selected']:
    name=group['module'];rp=batch/'data'/(name+'-audit.json');r=read(rp)
    assert sha(rp)==group['receipt_sha256'] and r['status']=='PASS_COMPLETE_BATCH_MODULE' and r['exit_code']==0
    assert sha(batch/'lean'/(name+'.lean'))==r['source_sha256']==sha(batch/r['source_snapshot'])
    assert sha(batch/r['log'])==r['log_sha256'] and sha(batch/'build'/(name+'.olean'))==r['olean_sha256']
    for a in r['theorem_audits']:assert set(a['axioms'])<={'propext','Classical.choice','Quot.sound'}
    for p in [rp,batch/r['log'],batch/r['source_snapshot'],(batch/r['source_snapshot']).parent/'checker.py.txt']:
        if p.relative_to(ROOT).as_posix() not in tracked:extra.append(p)
save('additional-batch-evidence.json',[p.relative_to(ROOT).as_posix() for p in sorted(set(extra))])
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip() for ref in ['HEAD','origin/main','origin/research/unconditional-241']}
assert refs['HEAD']==refs['origin/main']
c=dict(status='PASS_RELAXED_EXCLUSION_AND_EIGHT_ENTRIES',previous_goal_turn='progress',recorded_at=snapshot['recorded_at'],
    prior_checkpoint=prior_path.relative_to(ROOT).as_posix(),prior_checkpoint_sha256=sha(prior_path),
    proof_summary_sha256=sha(HERE/'data/proof-summary.json'),batch_observation_sha256=sha(HERE/'data/batch-observation.json'),
    final_review_sha256=sha(HERE/'audit/final-review.md'),mathematical_note_sha256=sha(HERE/'mathematical-note.md'),
    checked_final_modules=9,theorem_axiom_audits=15,new_mathematical_definitions=0,
    recovered_reference_indices=proof['recovered_reference_indices'],relaxed_bounds=proof['relaxed_bounds'],
    pending_reference_entries=1370,remaining_union_equivalence='Snake9.RecoveredReference108.reference_union_iff_remaining_eight',
    pending_reference_proposition='AllRefutedList of referenceKeys filtered to omit the eight explicit keys in ReferenceCoverage108',
    reference_union_refutation_checked=False,complete_graph_potential_certificates_checked=False,
    pending_conditional_local_cases=prior['pending_conditional_local_cases'],pending_share_floors=prior['pending_share_floors'],
    unconditional_edge_interval=[191,235],conditional_target=234,upper_bound_evidence=prior['upper_bound_evidence'],
    case7302_state=prior['case7302_state'],paper_revision=106,next_scheduled_paper_revision=116,paper_sha256=prior['paper_sha256'],
    git_refs_before_commit=refs,
    scope='One relaxed local exclusion covers seven exact reference entries; together with milestone107 eight are checked. Full union, complete graph certificates, five conditional shares and exact optimum remain unresolved. No new numerical bound.')
save('checkpoint.json',c)
counts=live['contexts_checked_by_profile']
summary=f'''Lean now excludes the simultaneous singleton-count bounds 2,2,3 at
the first, fourth and fifth internal centres of direction word 012304.
The second and third counts may range from 0 through 21. Six unused counter
limits were relaxed while preserving the 120 raw clauses and their variable
meanings. A regenerated contradiction has 75 deductions and 426 antecedent
references, independently checked as plain-clause RUP and through Lean.

A checked bounds-containment argument supplies seven exact catalogue entries.
Together with milestone 107's first entry, indices 0,472,495,535,572,602,619,620
are discharged. Lean proves equivalence between the full catalogue assertion
and the filtered assertion for 1,370 remaining entries. Nine final modules
and fifteen axiom reports pass. No new mathematical definitions were added.

The failed first coverage attempt and successful repair are preserved. The
repair uses the existing computable centre-list equality before finite checks.
Shared dependencies were reused; a clean independent rebuild is not asserted.
The three source reviews and final proof audit agree on the scope.

At the immutable process-verified observation, milestone 104 was RUNNING with
{counts['completed']}/791 completed-profile contexts and {counts['conditional']}/791
conditional-profile contexts checked. Its active module was {live['active']['module']}.
Consult its live record for later progress. Its active files were unchanged.

The maintained interval remains 191 through 235 edges, with the contributor
proof and archived audit supporting 235 and its complete independent rebuild
pending. Conditional 234 still requires the remaining reference entries,
complete graph certificates and five local floors (16,18,16,16,16). The exact
optimum and conjecture 196 remain open. Paper revision 106 is unchanged;
the next full revision is scheduled for 116.
'''
latest=('Latest continuation: [milestone 108](milestones/108-smaller-reference-recovery/README.md) checks a relaxed three-count exclusion covering seven reference entries; eight entries are now discharged and 1,370 remain. The complete potential batch continues. The numerical interval and paper revision 106 are unchanged.')
priority=('Next research priority: Test whether the relaxed 012304 exclusion removes any currently accepted full graph keys in either orientation, for both potential profiles. If it adds no graph restriction, inspect other small archived cores for unnecessary count assumptions and broader catalogue coverage. Preserve the running milestone 104 batch.')
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;t=p.read_text(encoding='utf-8')
    for prefix,value in [('Latest continuation:',latest),('Next research priority:',priority)]:
        t,n=re.subn('^'+re.escape(prefix)+'.*$',lambda _:value,t,count=1,flags=re.M);assert n==1
    p.write_text(t,encoding='utf-8')
p=ROOT/'milestones/README.md';t=p.read_text(encoding='utf-8');i=t.index('- [Milestone 107:');assert '- [Milestone 108:' not in t
p.write_text(t[:i]+'- [Milestone 108: relaxed exclusion and eight recovered entries](108-smaller-reference-recovery/README.md). One smaller contradiction covers seven exact keys; Lean checks the 1,370-entry remaining obligation.\n\n'+t[i:],encoding='utf-8')
p=ROOT/'RESEARCH_LEDGER.md';t=p.read_text(encoding='utf-8');assert '## Milestone 108:' not in t
p.write_text(t+'\n\n## Milestone 108: relaxed three-count exclusion\n\n'+summary+'\n'+priority+'\n',encoding='utf-8')
p=ROOT/'handoff/CURRENT_STATUS.md';t=p.read_text(encoding='utf-8');i=t.index('## Milestone 107 checkpoint')
p.write_text(t[:i]+'## Milestone 108 checkpoint\n\n'+summary+'\nEarlier checkpoint sections below are historical snapshots.\n\n'+t[i:],encoding='utf-8')
(ROOT/'handoff/README.md').write_text('''# Research handover

Start with [current status](CURRENT_STATUS.md), the
[continuation assignment](NEXT_AGENT_PROMPT.md), and
[milestone 108](../milestones/108-smaller-reference-recovery/README.md).
A relaxed three-count exclusion covers seven exact reference entries.
Together with milestone 107, eight entries are checked and 1,370 remain.
The checked remaining-list equivalence supplies the full union premise once
that residual list is proved.

Milestone 104's complete potential batch remains active. Verify its process
and live record before acting. Do not start another copy or modify its active
sources, checker or generator. Complete context coverage and final assemblies
are still required. Both bound profiles use the reference restrictions.

The maintained interval is 191 through 235 edges. Conditional 234 also needs
five local floors (16,18,16,16,16). The original case 7302 target-20 replay
remains stopped; a target-18 proof must use separate files.

The manuscript remains revision 106, preserving all authors and local hyperlink
settings. Its open source and repository mirror are identical. The built-in
compiler was unavailable before TeX processing; no updated PDF is verified.
Only necessary, repeatedly used mathematical concepts should be defined.
The next full manuscript revision is scheduled for 116.
''',encoding='utf-8')
(ROOT/'handoff/NEXT_AGENT_PROMPT.md').write_text('''# Continuation assignment

Continue the empty-square route in E:/Snake-in-a-box. Start with milestone 108's
mathematical note, proof summary, checkpoint and final independent review.
Verify milestone 104's live record and recorded process. Do not duplicate or
modify its complete potential batch.

## Current checked result

Snake9.RecoveredReference108.relaxed_reference_refuted proves
Refuted (winOf [0,1,2,3,0,4]) [(0,2),(0,21),(0,21),(0,2),(0,3)].
The original 120-clause D012304A22623 core and its semantic source are recovered
from pin 7cb52aad. A fresh contradiction has 75 deductions and 426 hints.
The independent plain-clause check and all nine final Lean modules pass.
Fifteen axiom reports contain standard axioms only.

The relaxed proof adjusts only six unused counter limits in a local expression.
All raw clauses, tags, variable meanings and counter positions stay fixed.
The semantic checker validates every counter, including unused ones.
refuted_of_tighter_centres transfers the result to seven exact reference keys.
Together with milestone 107's first key, recovered indices are
0,472,495,535,572,602,619,620. reference_union_iff_remaining_eight proves the
full union assertion equivalent to the filtered list printed explicitly in
ReferenceCoverage108.lean. remaining_eight_key_count proves its length 1370.
The intermediate two-key erasure theorem remains saved but is superseded.
Use the eight-key filter statement for continuation.

The first coverage attempt failed on kernel evaluation of Nat.log2.
The successful proof rewrites centresOf through Tags.centresK_eq before
decide +kernel. Both attempts are saved. Recovered modules use the unique
Recovered108 import prefix; use build-isolated and environment-isolated.json.
Do not shadow shared top-level LocalWindowSat/Cnf/Unsat module directories.
Existing shared support objects are reused; no clean rebuild is asserted.

## Most useful next check

Test the relaxed 012304 exclusion against the exact currently accepted full
graph keys, at every eligible window position and in both orientations.
Use the correct coordinate-shape normalization and singleton-count alignment.
Audit full keys rather than only source/target state pairs. If additional
keys are excluded, measure the effect on both completed and conditional
potential profiles in new files, preserving the active batch's graph.
An observed numerical improvement requires exact coverage and a checked
snake-to-filter argument before it becomes a new bound.

If this relaxed exclusion is already implied by the existing graph filters,
inspect other small archived cores before replaying one proof per catalogue
entry. Rank by the number of remaining keys a relaxed interval box covers.
Counter tags with .over inspect k; first/mono/step do not. Consequently even
some referenced counters may permit relaxed limits. This broader optimization
is untested. Always recheck all counter metadata and the full semantic theorem.
Do not infer admissible relaxations solely from an unused-variable scan.

Milestone 107 records 143 exact older D alternatives, before the new coverage.
Their source correspondence alone is not proof. Recover each chosen core
with its own metadata and full CNF; do not mix radii or change theorem types.

## Other obligations and preservation

Milestone 104 produces AllCompleted104 and AllConditional104 only after all
groups pass. Audit complete coverage, dependencies and axioms before claiming
the complete graph premises. Its status is determined by actual process and
receipts, not observation timeouts. Leave its pinned checker/generator unchanged.
Use at most one additional compiler, with the existing memory gate.

Conditional 234 still needs cases 7301,7302,7303,7307,7308 with caps
15,17,15,15,15, hence floors 16,18,16,16,16. Case 7302's old target-20 replay
remains stopped after a preserved 900-second timeout and 649 successes.
A target-18 proof needs new sources. The reference catalogue remains incomplete.

The maintained interval is 191 through 235 edges. The contributor's 235 proof
has its archived audit and pending independent rebuild. The optimum and 196
remain unresolved; keep the goal active.

Paper revision 106 remains unchanged; the next full revision is 116. Preserve
D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and its repository mirror,
all three authors and exact hypersetup. No current PDF is verified because the
built-in compiler failed before TeX processing. Define only necessary concepts
that recur; keep Lean implementation details out of the manuscript.

Python: C:/Users/hironakaiori/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe,
with -B -X utf8. Lean 4.19 and mathlib are under
D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research.
Reuse existing support objects; do not copy the complete overlay or add -M4096.

Leave unrelated .gitignore and milestones/50-three-count-return/excess-screen/
data/critical-family.json edits untouched. Fetch before publishing, stage exact
reviewed files, verify staged bytes, then push the completed round. Historical
handover manifests remain historical and must not be rewritten.
''',encoding='utf-8')
print(json.dumps(dict(status=c['status'],remaining_reference_entries=1370,batch_counts=counts,additional_batch_files=len(set(extra))),indent=2))
