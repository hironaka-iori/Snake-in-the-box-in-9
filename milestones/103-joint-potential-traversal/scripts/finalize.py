"""Save the checked traversal and comparisons, preserving the manuscript."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (HERE/'data/check.lock').exists()
assert not (HERE/'data/checkpoint.json').exists(),'Finalization is one-shot.'
subprocess.run([sys.executable,'-B','-X','utf8',str(HERE/'scripts/audit.py')],check=True)
s=read(HERE/'data/proof-summary.json');prior=ROOT/'milestones/102-potential-block-reduction/data/checkpoint.json';old=read(prior)
paper=ROOT/'paper/snake9_research.tex'
assert sha(paper)==old['paper_sha256']==sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))
case=ROOT/'milestones/73-countfree-share-catalogue/cases/case7302'
assert not (case/'data/proof-audit.json').exists()
assert sha(case/'logs/completion-record.json')==sha(ROOT/'milestones/93-defined-graph-potential/data/case7302-completion-observation.json')
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip() for ref in ['HEAD','origin/main']}
assert refs['HEAD']==refs['origin/main']
groups=read(HERE/'data/group-analysis.json')
for path,digest in groups['inputs_sha256'].items():assert sha(ROOT/path)==digest,path
selected={}
for p in ['completed','conditional']:
    rows=[x for x in s['comparisons'] if x['profile']==p]
    times={m:sum(x[m+'_seconds'] for x in rows) for m in ['baseline','joint']}
    selected[p]=min(times,key=times.get)
next_task=('Prepare one resumable sequential batch for all remaining contexts, reusing the six existing certificates per profile. '
    'Reuse one verified reduced check per identical acceptance root, weight expression and potential-root pair, then prove each original context by the bounded transfer. '
    'Select the baseline or joint method from the measured evidence, with a fallback for timed-out contexts. '
    'Assemble the original complete-graph theorem only after every context and every missing block are covered. '
    'Do not start another series of isolated timing pilots.')
c=dict(status='PASS_JOINT_TRAVERSAL_AND_MATCHED_CONTEXT_COMPARISONS',previous_goal_turn='progress',
    recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),proof_summary_sha256=sha(HERE/'data/proof-summary.json'),
    modules=len(s['modules']),theorem_audits=s['theorem_audits'],new_definitions=s['new_definitions'],
    complete_contexts=s['complete_contexts'],finite_coverage_by_profile=s['finite_coverage_by_profile'],
    comparisons=s['comparisons'],provisional_batch_method_by_profile=selected,
    complete_graph_potential_certificates_checked=False,unconditional_edge_interval=[191,235],conditional_target=234,
    upper_bound_evidence=old['upper_bound_evidence'],pending_reference_catalogues=old['pending_reference_catalogues'],
    pending_conditional_local_cases=old['pending_conditional_local_cases'],pending_share_floors=old['pending_share_floors'],
    case7302_state=old['case7302_state'],case7302_source_record_unchanged=True,
    paper_revision=96,next_scheduled_paper_revision=106,paper_sha256=sha(paper),
    prior_checkpoint=prior.relative_to(ROOT).as_posix(),prior_checkpoint_sha256=sha(prior),git_refs_before_commit=refs,
    next_task=next_task,scope='Traversal soundness and four matched profile/context comparisons. Coverage remains six contexts per profile; the optimum and a smaller global bound remain unresolved.')
(HERE/'data/checkpoint.json').write_text(json.dumps(c,indent=2)+'\n')
table='\n'.join(f"| {x['profile']} | {x['direction']}/{x['history']} | {x['baseline_seconds']:.3f} | {x['joint_seconds']:.3f} |" for x in s['comparisons'])
group_table='\n'.join(f"| {p} | {v['contexts']} | {v['unique_checks']} | {v['duplicate_contexts']} |" for p,v in groups['profiles'].items())
results=f'''Lean checked the general implication from successful joint traversal to
the existing prefix checker. Both source and target digit schedules, the
rejected-branch rule and the potential-width checks are covered. There are
{len(s['modules'])} checked modules and {s['theorem_audits']} distinct theorem axiom audits.
Only two reusable implementation definitions were added: branch selection
and joint traversal. No mathematical terminology or manuscript definition was added.

Four matched sequential comparisons passed, including transfer to the
original full context checker:

| Profile | Direction/history | Baseline seconds | Joint seconds |
| --- | --- | ---: | ---: |
{table}

Each pair uses the same imports, weights, potential roots, clipping bound,
acceptance root and candidate codes. No other Lean compiler was active at
launch. These are end-to-end module times from one pair per profile and
context; unrelated system activity was not isolated. They do not establish
a universal performance ordering.

The provisional batch choices, based on total time for the two contexts in
each profile, are completed: {selected['completed']}; conditional: {selected['conditional']}.
The batch should preserve a fallback for a context that exceeds its limit.

These contexts were already certified. Coverage therefore remains six of
791 contexts per profile: 34,701 accepted edges for the completed profile
and 34,148 for the conditional profile. There are 785 contexts per profile
still pending. Comparisons do not add distinct graph coverage.
'''
note=r'''# Joint traversal of the existing potential trees

## Proof

A six-digit base-six code $c<6^6$ determines the existing source offset
$\lfloor c/6\rfloor$ and target offset $c\bmod6^5$. The source therefore uses
the first five digits and the target the last five. While traversing the
acceptance diagram, the checker can select the appropriate potential
subtrees at the same digit positions.

Selection at a potential node is permitted only when the stored interval
width equals the expected width. If a digit is $j<6$ and the residual index
is $u<w$, the existing evaluator at index $jw+u$ equals the evaluator of
the selected child at index $u$. A constant leaf remains constant at any
remaining depth. These statements are checked in Lean.

The induction for joint traversal uses the original code interval. With
$d$ digits unread and prefix $p$, the codes lie in

$$p6^d\le c<(p+1)6^d.$$

For $d\ge1$, after choosing digit $j$, the interval becomes

$$ (6p+j)6^{d-1}\le c<(6p+j+1)6^{d-1}.$$

The quotient and remainder identities identify the same source and target
indices after each selection. The first target digit is skipped; the last
source digit is skipped. Rejected acceptance branches require no potential
check. At an accepted leaf, the checker evaluates exactly the original
capped inequality. Consequently, successful joint traversal implies the
existing prefix check, and the previously proved bounded transfer gives
the original graph-context check.

This is a one-way success implication. A malformed node width may cause
the new checker to fail even when the original evaluator succeeds. The
proof does not rely on any unproved global shape property of the potential
trees. It also preserves the original minima with 551 and 602.

## Checked comparison

'''+results+rf'''
## Complete batch

A source grouping of the proposed checks gives:

| Profile | Contexts | Distinct expressions | Repeated expressions |
| --- | ---: | ---: | ---: |
{group_table}

The grouping requires identical acceptance root, both potential roots and
all inputs to the exact reduced weight expression. This source analysis
does not itself certify reuse. Each reused theorem must still elaborate
and pass Lean against the explicit expression, followed by transfer to
the original direction/history context. Equal acceptance classes alone
are insufficient.

{next_task}

## Remaining mathematical obligations

The maintained project interval is $191\le a(9)\le235$ edges. The upper bound
retains the inspected contributor theorem and archived audit; a complete
independent rebuild is pending. The target 234 remains conditional. The
optimum and conjecture 196 remain unresolved.

The full graph certificates are pending. Both global chains also retain
AllRefuted6K235 and AllRefuted236. The conditional chain additionally needs
the five local refutations with caps $(15,17,15,15,15)$, giving floors
$(16,18,16,16,16)$. The stopped original case7302 target 20 evidence is
unchanged. A target 18 proof requires separate files.

The first traversal proof attempt had three tactic simplification errors.
The corrected source passed. The exact unsuccessful source and log remain
saved. No compiler is active at this checkpoint.

The paper remains revision 96 with all three authors and hyperlink settings
unchanged. The next scheduled full revision is 106.
'''
(HERE/'mathematical-note.md').write_text(note,encoding='utf-8')
(HERE/'README.md').write_text('# Milestone 103: joint potential traversal\n\n'+results+'''
Read the [mathematical note](mathematical-note.md),
[proof summary](data/proof-summary.json), [checkpoint](data/checkpoint.json)
and [source review](audit/traversal-review.md). The candidate metadata records
generated proposals; proof status comes from the checked receipts.

No improved global snake bound is claimed. The next step is complete,
resumable graph certification with verified reuse of identical checks.
''',encoding='utf-8')
latest=('Latest continuation: [milestone 103](milestones/103-joint-potential-traversal/README.md) proves joint traversal soundness and checks four matched profile/context comparisons. Coverage remains six contexts per profile. Complete graph certificates are pending; the interval remains 191 through 235, with 234 conditional.')
priority='Next research priority: '+next_task+' Paper revision 96 is unchanged; the next full revision is 106.'
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;t=p.read_text()
    for prefix,value in [('Latest continuation:',latest),('Next research priority:',priority)]:
        t,n=re.subn('^'+re.escape(prefix)+'.*$',lambda _:value,t,count=1,flags=re.M);assert n==1
    p.write_text(t)
p=ROOT/'milestones/README.md';t=p.read_text();i=t.index('- [Milestone 102:');assert '- [Milestone 103:' not in t
p.write_text(t[:i]+'- [Milestone 103: joint potential traversal](103-joint-potential-traversal/README.md). General soundness and four matched comparisons; complete graph certification is next.\n\n'+t[i:])
p=ROOT/'RESEARCH_LEDGER.md';t=p.read_text();assert '## Milestone 103:' not in t
p.write_text(t+'\n\n## Milestone 103: joint potential traversal\n\n'+latest+'\n\n'+results+'\n'+priority+'\n')
p=ROOT/'handoff/CURRENT_STATUS.md';t=p.read_text();a=t.index('## Milestone 102 checkpoint');b=t.index('## Result and evidence boundary',a)
t=t[:a]+'## Milestone 103 checkpoint\n\n'+results+'\n'+next_task+'\n\n'+t[b:]
t=t.replace('The milestone 102 checkpoint\nabove supersedes them:','The milestone 103 checkpoint\nabove supersedes them:');p.write_text(t)
(ROOT/'handoff/README.md').write_text('''# Research handover

Start with [current status](CURRENT_STATUS.md) and the
[continuation assignment](NEXT_AGENT_PROMPT.md). The latest checkpoint is
[milestone 103](../milestones/103-joint-potential-traversal/README.md).

All 791 context equations and all 412 potential-block equations are checked.
Joint traversal now has a checked success implication to the original prefix
checker. Four matched comparisons passed. Six contexts per profile remain
certified, with 785 per profile pending. No coverage is added by benchmarks.

The maintained interval is 191 through 235 edges; 234 remains conditional.
The contributor upper bound retains its archived audit and pending independent
rebuild. The optimum and conjecture 196 remain unresolved.

Preserve both reference catalogues, the five pending local share bounds and
the stopped original case7302 target 20 evidence. A target 18 proof needs
separate files. Reuse the existing proof overlay and successful receipts.

Paper revision 96, authors Iori Hironaka, Tommy Ma and Steven Zhan, and hyperlink
settings are unchanged. The next full revision is 106. Use standard notation
and introduce definitions only when necessary and repeatedly used.
''')
p=ROOT/'handoff/NEXT_AGENT_PROMPT.md';previous=p.read_text();tail=previous[previous.index('## Global evidence and remaining assumptions'):]
tail=tail.replace('milestones/102-potential-block-reduction/scripts/check.py','milestones/103-joint-potential-traversal/scripts/check.py')
tail=tail.replace('environment reuses milestone 101 and the milestone 98 support overlay.','environment reuses milestone 102 and the milestone 98 support overlay.')
intro=f'''# Continuation assignment

Continue the empty-square charging route in `E:/Snake-in-a-box`. Read milestone
103's mathematical note, proof summary and checkpoint. The general joint
traversal proof and all four matched comparisons passed. The active goal is
unresolved. No compiler is active at this checkpoint.

## Next task

{next_task}

The provisional methods from the two-context totals are completed:
{selected['completed']}; conditional: {selected['conditional']}. These are limited timing
observations, not a general performance theorem. The exact measurements and
source grouping are in milestone 103. The 591 completed and 578 conditional
source groups are proposed reuse groups; Lean must check each application.

The reusable traversal theorem is Snake9.Joint103.joint_root_prefix. It takes
weight, P, R, acceptance root, source and target potential trees, and a
successful checkJoint equation. It returns the exact original prefix-check
equation with clipped values at code/6 and code%7776. No graph premise is added.
The definitions step and checkJoint are the only new reusable helpers.

Use the existing bounded transfer
Snake9.BoundedPrefixTransfer102.contextCheck_of_bounded_prefix and block
equalities Snake9.PotentialBlocks102.completed_at_i / conditional_at_i.
The source offset code/6 requires code<46656; target code%7776 is bounded.
All 791 context formulas remain available in Context101Group00 through 12.

Reuse the completed contexts listed in milestone 102's proof summary:
completed 35/0 and conditional 177/43 from 100; both profiles 99/37 from 101;
both profiles 0/0, 1/0, 9/0 and 10/0 from 102. The repeated checks in 103 add
no coverage. Keep full direction/history keys and both potential caps.

The generator in 103 supports --method joint or baseline and selected
--contexts. For a complete batch, extend it with verified theorem reuse,
dependency order and a resumable queue; avoid regenerating audited sources.
Do not modify this frozen milestone to run the complete batch.

No unsupported native evaluation, incomplete proof or arbitrary-snake claim
was introduced. The successful theorem audits contain only propext,
Classical.choice and Quot.sound. One unsuccessful traversal proof attempt
is preserved with exact source and log.

'''
p.write_text(intro+tail)
print(c['status'],c['modules'],'modules;',c['theorem_audits'],'audits;',selected)
