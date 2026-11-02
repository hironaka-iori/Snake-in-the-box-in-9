"""Save the recovered entry and an immutable observation of the active graph batch."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
save=lambda name,data:(HERE/'data'/name).write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
assert not (HERE/'data/checkpoint.json').exists() and not (HERE/'data/check.lock').exists()
proof=read(HERE/'data/proof-summary.json');assert proof['status']=='PASS_ONE_REFERENCE_REFUTATION_RECOVERED'
prior_path=ROOT/'milestones/106-paper-revision/data/checkpoint.json';prior=read(prior_path)
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
c=dict(status='PASS_FIRST_REFERENCE_ENTRY_AND_REMAINING_LIST',previous_goal_turn='progress',recorded_at=snapshot['recorded_at'],
    prior_checkpoint=prior_path.relative_to(ROOT).as_posix(),prior_checkpoint_sha256=sha(prior_path),
    proof_summary_sha256=sha(HERE/'data/proof-summary.json'),batch_observation_sha256=sha(HERE/'data/batch-observation.json'),
    recovery_guidance_sha256=sha(HERE/'audit/recovery-guidance.md'),older_alternatives_sha256=sha(HERE/'data/older-alternatives.json'),
    exact_older_alternative_keys=143,next_candidate_union_index=472,
    checked_final_modules=19,theorem_axiom_audits=14,new_mathematical_definitions=0,
    recovered_reference_keys=[dict(index=0,directions=[0,1,2],symbols=[1,1],root='Q012A11')],
    pending_reference_entries=1377,pending_reference_proposition='AllRefutedList Snake9.Reference85.referenceKeys.tail',
    remaining_union_equivalence='Snake9.RecoveredReference107.reference_union_iff_remaining',
    reference_union_refutation_checked=False,complete_graph_potential_certificates_checked=False,
    pending_conditional_local_cases=prior['pending_conditional_local_cases'],pending_share_floors=prior['pending_share_floors'],
    unconditional_edge_interval=[191,235],conditional_target=234,upper_bound_evidence=prior['upper_bound_evidence'],
    case7302_state=prior['case7302_state'],paper_revision=106,next_scheduled_paper_revision=116,paper_sha256=prior['paper_sha256'],
    git_refs_before_commit=refs,scope='One exact reference refutation and reduction to the remaining 1377 entries; standard axioms. Full union, full potential and five conditional shares remain pending. No new numerical bound.')
save('checkpoint.json',c)
counts=live['contexts_checked_by_profile']
summary=f'''The first exact reference key, directions 012 and singleton symbols (1,1),
has a recovered closed Lean refutation. The original 1,172-clause semantic
input matches the archived source. A fresh LRAT certificate has 968 lemmas
and 41,184 hints, independently checked as plain-clause RUP and through seven
Lean segments. The final isolated replay has 19 checked modules and 14
standard-axiom reports. No new mathematical definitions were added.

Lean proves that the full reference-union assertion is equivalent to the
assertion for its remaining 1,377 entries. The first failed combined import
attempt is preserved; the successful attempt changes only recovered import
paths to avoid shadowing shared modules. Existing support objects are reused.
This is recovery of an established restriction, with no new numerical bound.

An independent source audit identifies 143 exact older D alternatives,
including the recovered first entry. The next representative is union index
472, with a recorded 120-clause core; its decoded clauses match the archive.
The alternative-root correspondence supplies no unperformed proof replay.

At the immutable process-verified observation, milestone 104 was RUNNING with
{counts['completed']}/791 completed-profile contexts and {counts['conditional']}/791
conditional-profile contexts checked. Its active module was
{live['active']['module']}. Consult the live record for later progress.

The maintained interval is 191 through 235 edges. The contributor upper bound
retains its archived audit and pending independent rebuild. The remaining
reference entries, complete graph certificates and five conditional shares
remain distinct requirements. Paper revision 106 is unchanged; the next full
revision is scheduled for 116. The exact optimum and conjecture 196 remain open.
'''
latest=('Latest continuation: [milestone 107](milestones/107-reference-refutation-recovery/README.md) recovers the first exact reference refutation in Lean and proves that 1,377 entries remain. The complete potential batch continues. The paper remains revision 106 and the numerical interval is unchanged.')
priority=('Next research priority: Extend the recovered reference procedure using exact source/core correspondence and isolated import prefixes; use smaller older proofs when their theorem types match the same key. Preserve the running milestone 104 batch and audit both final assemblies when complete. The five conditional local floors remain (16,18,16,16,16).')
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;t=p.read_text(encoding='utf-8')
    for prefix,value in [('Latest continuation:',latest),('Next research priority:',priority)]:
        t,n=re.subn('^'+re.escape(prefix)+'.*$',lambda _:value,t,count=1,flags=re.M);assert n==1
    p.write_text(t,encoding='utf-8')
p=ROOT/'milestones/README.md';t=p.read_text(encoding='utf-8');i=t.index('- [Milestone 106:');assert '- [Milestone 107:' not in t
p.write_text(t[:i]+'- [Milestone 107: first recovered reference refutation](107-reference-refutation-recovery/README.md). Exact input, regenerated LRAT, closed Lean entry and remaining-list equivalence; 1,377 entries remain.\n\n'+t[i:],encoding='utf-8')
p=ROOT/'RESEARCH_LEDGER.md';t=p.read_text(encoding='utf-8');assert '## Milestone 107:' not in t
p.write_text(t+'\n\n## Milestone 107: reference refutation recovery\n\n'+summary+'\n'+priority+'\n',encoding='utf-8')
p=ROOT/'handoff/CURRENT_STATUS.md';t=p.read_text(encoding='utf-8');i=t.index('## Milestone 106 checkpoint')
p.write_text(t[:i]+'## Milestone 107 checkpoint\n\n'+summary+'\nThe current remaining-reference premise is the tail of the exact list.\nEarlier checkpoint sections below are historical snapshots.\n\n'+t[i:],encoding='utf-8')
(ROOT/'handoff/README.md').write_text('''# Research handover

Start with [current status](CURRENT_STATUS.md), the
[continuation assignment](NEXT_AGENT_PROMPT.md), and
[milestone 107](../milestones/107-reference-refutation-recovery/README.md).
The first exact reference entry is now checked; 1,377 remain. The new
remaining-list equivalence plugs into the existing milestone 105 implications.

Milestone 104's complete potential batch remains active. Verify its process
and live record before any action. Do not start another copy or modify its
active sources, checker or generator. Only complete context coverage and the
final assemblies discharge the complete graph premises.

The maintained interval is 191 through 235 edges. Conditional 234 also needs
the five pending local floors (16,18,16,16,16). The original case 7302 target-20
replay remains stopped. A target-18 proof must use separate sources.

The paper remains revision 106, with all three authors and local hyperlink
settings preserved. The open source and repository mirror are identical.
The built-in compiler was unavailable before TeX processing, so no updated
PDF is verified. Introduce only necessary, repeatedly used definitions.
The next full manuscript revision is scheduled for 116.
''',encoding='utf-8')
(ROOT/'handoff/NEXT_AGENT_PROMPT.md').write_text('''# Continuation assignment

Continue the empty-square route in E:/Snake-in-a-box. Read milestone 107's
mathematical note, proof summary, checkpoint and recovery guidance. Then read
milestone 104's live record and NEXT.md and verify its recorded process.
The complete potential batch is still running; do not duplicate or modify it.

## Checked reference recovery

Snake9.RecoveredReference107.adjacent_ones_refuted is the closed refutation
for winOf [0,1,2] and boundsOf [1,1]. The first exact reference key is checked
to be this entry. reference_union_iff_remaining proves equivalence between
AllRefutedList referenceKeys and AllRefutedList referenceKeys.tail; the tail
has 1,377 entries. The full union remains unproved. Use the existing milestone
105 bound implications after reconstructing the full union from its tail.

The exact Q012A11 CNF and semantic sources were recovered from pin7cb52aad.
The original full-CNF indices, the decoded Lean raw clauses and the 1,172
core clauses agree. A fresh core-only CaDiCaL LRAT proof is trimmed, remapped
to original clause IDs and exported by the pinned contributor generator.
The separate plain-clause RUP audit and all19 final Lean modules pass.
Four new wrapper conclusions and ten reused certificate statements have
standard-axiom audits. This recovers an established exclusion; it gives no
new upper bound or claim of a clean rebuild of shared dependencies.

The successful environment is data/environment-isolated.json and the output
directory is build-isolated. Recovered sources use import prefix Recovered107.
Do not put new files under bare LocalWindowSat/Cnf/Unsat in a leading search
directory: that shadows entire shared module directories. The failed first
attempt, successful imports-only ports, logs and receipts are preserved.
Do not alter this frozen evidence; make the next batch in a new milestone.

## Next work

Extend the recovery procedure to the remaining exact keys. Inspect the
recovery guidance for older D certificates proving identical key statements;
their smaller cores may save work. A chosen root must end in the exact
Refuted(winOf directions)(boundsOf symbols) type. Root-name similarity or
a historical solver report is insufficient. Verify raw clauses against their
own compatible metadata and CNF; never pair another radius's proof with them.

The older direction and direction5 catalogues contain 143 distinct exact
alternative D roots for union keys, including the recovered first key.
There are 142 additional candidates. These source correspondences are not
replayed refutations. The next small representative is union index 472,
D012304A22623: its recorded core has 120 clauses and its recorded proof has
75 lemmas and 426 hints. The count symbol six also exercises the interval
[6,21] semantics. Recover its own inputs and verify every correspondence.

Use a resumable single-compiler batch with source/object/log hashes and explicit
entry coverage. Test this additional representative before a broad launch.
Keep heavy work out of the active potential batch's memory budget. Existing
success receipts must be verified before reuse; preserve failures and timeouts.

Milestone 104 generates AllCompleted104 and AllConditional104 only after all
groups pass. Audit complete context coverage, dependencies and axioms before
publishing those graph certificates as complete. Do not infer completion
from an observation timeout or a stale lock; inspect the recorded process.

Conditional234 additionally needs cases7301,7302,7303,7307,7308 with share
caps15,17,15,15,15, giving floors16,18,16,16,16. The original case7302 target20
replay remains stopped after its preserved900-second timeout and649 successful
modules. A target18 proof needs separate files. Do not restart the old replay.

The maintained interval is191 through235 edges, using the inspected contributor
proof and archived audit for235; its full independent rebuild is pending.
The optimum and196 remain unresolved. Keep the full goal active.

## Manuscript and runtime

The current paper is revision106; the next full revision is116. Preserve the
exact D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex source and its
E:/Snake-in-a-box/paper/snake9_research.tex mirror. The built-in compiler failed
before TeX processing because of a Windows helper restriction; no current PDF
is verified. Preserve the three authors and local hypersetup settings.
Use ordinary notation and define only necessary, repeatedly used terms.
Keep Lean filenames and implementation definitions out of the paper.

Python: C:/Users/hironakaiori/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe,
with -B -X utf8. Lean4.19 and mathlib are under
D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research.
Reuse existing support objects; do not copy the full overlay. Do not add -M4096.

Leave unrelated .gitignore and
milestones/50-three-count-return/excess-screen/data/critical-family.json edits
untouched. Fetch before publication, stage exact reviewed files, verify their
staged bytes and push each completed round. Old handover manifests remain
historical; do not rewrite them to match newer shared documents.
''',encoding='utf-8')
# Normalize accidental number/word joins in the new assignment, outside paths.
p=ROOT/'handoff/NEXT_AGENT_PROMPT.md';t=p.read_text(encoding='utf-8')
for a,b in [('pin7cb','pin 7cb'),('all19','all 19'),('Conditional234','Conditional 234'),('cases7301','cases 7301'),('caps15','caps 15'),('floors16','floors 16'),('case7302','case 7302'),('target20','target 20'),('preserved900','preserved 900'),('and649','and 649'),('target18','target 18'),('is191','is 191'),('through235','through 235'),('for235','for 235'),('and196','and 196'),('revision106','revision 106'),('is116','is 116'),('Lean4.19','Lean 4.19')]:t=t.replace(a,b)
p.write_text(t,encoding='utf-8')
print(json.dumps(dict(status=c['status'],remaining_reference_entries=1377,batch_counts=counts,additional_batch_files=len(set(extra))),indent=2))
