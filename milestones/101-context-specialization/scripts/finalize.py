"""Publish the audited context equations and finite checks after compilation."""
from pathlib import Path
import datetime, hashlib, json, re, subprocess, sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (HERE/'data/check.lock').exists()
assert not (HERE/'data/check-extra.lock').exists()
subprocess.run([sys.executable,'-B','-X','utf8',str(HERE/'scripts/audit.py')],check=True)
s=read(HERE/'data/proof-summary.json')
prior=ROOT/'milestones/100-prefix-potential-checker/data/checkpoint.json';old=read(prior)
paper=ROOT/'paper/snake9_research.tex'
assert sha(paper)==old['paper_sha256']==sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))
case=ROOT/'milestones/73-countfree-share-catalogue/cases/case7302'
assert not (case/'data/proof-audit.json').exists()
assert sha(case/'logs/completion-record.json')==sha(ROOT/'milestones/93-defined-graph-potential/data/case7302-completion-observation.json')
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip() for ref in ['HEAD','origin/main']}
assert refs['HEAD']==refs['origin/main']
next_task=('Use the checked equations for all 791 contexts to extend the finite potential certificates. '
    'First test exact reduction of each fixed source/target potential lookup to its recorded subtree, '
    'retaining the original cap and proving the needed count-code bounds. Benchmark one context per profile '
    'before expanding. Reuse the four complete context certificates and preserve the reference/local premises.')
c=dict(status='PASS_ALL_CONTEXT_SPECIALIZATIONS_AND_EMITTING_CERTIFICATES',previous_goal_turn='progress',
    recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    proof_summary_sha256=sha(HERE/'data/proof-summary.json'),modules=len(s['modules']),theorem_audits=s['theorem_audits'],
    direction_equations=505,context_equations=791,complete_contexts=s['complete_contexts'],
    finite_coverage_by_profile=s['finite_coverage_by_profile'],
    all_context_weights_and_endpoints_checked=True,complete_graph_potential_certificates_checked=False,
    unconditional_edge_interval=[191,235],conditional_target=234,upper_bound_evidence=old['upper_bound_evidence'],
    pending_reference_catalogues=old['pending_reference_catalogues'],pending_conditional_local_cases=old['pending_conditional_local_cases'],
    pending_share_floors=old['pending_share_floors'],case7302_state=old['case7302_state'],case7302_source_record_unchanged=True,
    paper_revision=96,next_scheduled_paper_revision=106,paper_sha256=sha(paper),
    prior_checkpoint=prior.relative_to(ROOT).as_posix(),prior_checkpoint_sha256=sha(prior),git_refs_before_commit=refs,
    next_task=next_task,
    scope='Exact evaluator equations for all contexts and two complete finite contexts per profile. Complete graph certificates and improved global bounds remain unresolved.')
(HERE/'data/checkpoint.json').write_text(json.dumps(c,indent=2)+'\n')
table='\n'.join(f"| {x['profile']} | {x['direction']}/{x['history']} | {x['accepted_edges']:,} | {x['seconds']:.3f} | {x['origin_milestone']} |" for x in s['complete_contexts'])
results=f'''All 505 direction lookups and all 791 context equations passed Lean. The
context equations preserve the exact selected rule list, source and target,
acceptance class, and both weight profiles. They hold for every natural count
code. The combined import check found no declaration conflict.

The milestone has {len(s['modules'])} checked modules and {s['theorem_audits']:,}
distinct theorem axiom audits. The only permitted logical axioms are
`propext`, `Classical.choice` and `Quot.sound`; no incomplete proof or unchecked
native evaluation is used. Exact sources, snapshots, logs and dependencies
are recorded in the proof summary and individual receipts.

The complete finite checks now comprise two contexts per profile:

| Profile | Direction/history | Accepted edges | Compiler seconds | Milestone |
| --- | --- | ---: | ---: | ---: |
{table}

Direction 99/history 37 is checked under both profiles, so its 6,043 accepted
keys must not be counted twice as distinct graph edges. Coverage is 13,194
accepted edges for the completed profile and 12,641 for the conditional
profile. Each context theorem covers all 46,656 candidate codes through the
checked acceptance traversal. The earlier 207 pilot edges are already included.

The complete graph inequalities still need 789 contexts per profile. The
all-context evaluator equations do not discharge those finite inequalities.
Compiler times are observations from the recorded runs. Some equation batches
overlapped the independent finite-check queue, and memory limits temporarily
delayed new batches. These times are not a controlled performance comparison.
'''
note=r'''# Exact context equations and further potential checks

## Purpose and argument

The weight and endpoint formulas previously repeated fixed table lookups for
every count code. For each direction and stored history, these lookups can be
evaluated once without changing the edge weight.

The proof first filters the existing history-rule catalogue by its suffix
condition. A list induction proves that omitted rules contribute zero and
that the maximum of the remaining contributions equals the original value.
The selected list is checked against the original catalogue in its original
order, including multiplicity. Each retained rule still uses its original
count-cap test, geometric credit and stronger credit.

The direction equations evaluate the geometric credit, both count-free
floors and the five conditioned rules. The latter use the exact forward and
reverse canonical words. Each context then combines these equations with
the checked selected list. Source and target equations preserve the history
update and the original state numbering. The weight and endpoint equalities
hold for all natural count codes, without a hidden range assumption.

Only one reusable evaluator is added to the proof implementation. The
generated files add equations, without introducing further mathematical
definitions or a replacement graph model.

## An emitting history rule

In direction 99/history 37, index the six encoded count symbols from 0 to 5.
The single emitted history rule contributes 19
when $c_1\le2$ and $c_2\le2$, and contributes
18 otherwise. The other conditioned contribution is 96 when the last-five
count code is 3221, and zero otherwise. The geometric contribution is 5;
the completed and conditional floors are respectively 0 and 18.

Consequently, both profile weights agree in this context: the history credit
already supplies at least 18. Lean checks the explicit piecewise formulas and
their equality for every count code. The profiles still use different
potential arrays and slopes, so their potential inequalities require
separate checks.

Exact numerical selection finds 6,043 accepted count codes. Four make the
capped history credit increase the final credit from 18 to 19 in both
profiles. These observations selected a relevant test case. Its full
potential inequalities are subsequently checked in Lean and transferred back
to the original context checker.

## Verification

'''+results+r'''
## Consequences and remaining work

The maintained project interval remains $191\le a(9)\le235$ edges. The upper
bound retains the inspected contributor theorem and archived audit; its
complete independent rebuild is pending. The target 234 remains conditional.
This milestone does not claim a smaller bound or settle the conjecture 196.

Both final chains retain the reference catalogues AllRefuted6K235 and
AllRefuted236. The conditional chain additionally retains the five local
refutations with caps $(15,17,15,15,15)$, giving floors $(16,18,16,16,16)$.
Equalities between executable weight formulas do not establish these local
share bounds. The original case7302 target 20 replay remains stopped and
unchanged; a target 18 attempt requires separate evidence.

All context weights and endpoints are now available in reduced form. The
next repeated lookup to examine is the potential itself. For a fixed source
or target state block, the balanced root lookup can potentially be replaced
by its recorded subtree. The proof must preserve the original range cap and
establish the relevant count-code bound. This is a proposed optimization,
with no measured speed improvement claimed here.

In particular, reducing the source potential to one fixed block requires
$c<46656$, hence $c/6<7776$. A source-block equation must not be asserted for
all natural codes. A subsequent transfer can use the existing accepted-code
soundness theorem and the interval checker with this bound kept explicit.

The numerical grouping into 582 joint context classes still needs Lean
equality and transport proofs before certificates can be reused across
groups. Matching acceptance classes or endpoint pairs alone is insufficient.
The existing context proofs should be reused in every subsequent assembly.

Paper revision 96, the three authors and hyperlink settings are unchanged.
The next scheduled full paper revision is 106.
'''
(HERE/'mathematical-note.md').write_text(note,encoding='utf-8')
(HERE/'README.md').write_text('''# Milestone 101: exact equations for every context

'''+results+'''
Read the [mathematical note](mathematical-note.md),
[checkpoint](data/checkpoint.json), [proof summary](data/proof-summary.json),
and [independent source review](audit/independent-review.md).

The generated JSON files describe candidates at generation time. Current
proof status is supplied by the individual Lean receipts and proof summary.
The saved unsuccessful pilot attempt was caused by an unqualified identifier;
its source snapshot and log are retained. The corrected source passed.

The maintained interval is 191 through 235 edges; 234 remains conditional.
The complete graph certificate is pending for both profiles.
''',encoding='utf-8')
latest=('Latest continuation: [milestone 101](milestones/101-context-specialization/README.md) checks exact weights, endpoints and acceptance data for all 791 contexts. A count-dependent emitting context passes both potential checks, bringing complete coverage to two contexts per profile. All-context finite certificates remain pending; the interval remains 191 through 235, with 234 conditional.')
priority='Next research priority: '+next_task+' Paper revision 96 is unchanged; the next full revision is 106.'
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;t=p.read_text()
    for prefix,value in [('Latest continuation:',latest),('Next research priority:',priority)]:
        t,n=re.subn('^'+re.escape(prefix)+'.*$',lambda _:value,t,count=1,flags=re.M);assert n==1
    p.write_text(t)
p=ROOT/'milestones/README.md';t=p.read_text();i=t.index('- [Milestone 100:');assert '- [Milestone 101:' not in t
p.write_text(t[:i]+'- [Milestone 101: exact equations for all contexts](101-context-specialization/README.md). All 791 evaluator equations and two finite contexts per profile checked; complete graph certificates remain pending.\n\n'+t[i:])
p=ROOT/'RESEARCH_LEDGER.md';t=p.read_text();assert '## Milestone 101:' not in t
p.write_text(t+'\n\n## Milestone 101: all context equations and an active capped history\n\n'+latest+'\n\n'+results+'\n'+priority+'\n')
p=ROOT/'handoff/CURRENT_STATUS.md';t=p.read_text();a=t.index('## Milestone 100 checkpoint');b=t.index('## Result and evidence boundary',a)
block='## Milestone 101 checkpoint\n\n'+results+'\n'+next_task+'''

The initial pilot with an unqualified identifier failed and is preserved with
its exact source snapshot. The corrected source passed. No compiler remains
active at this checkpoint. Both manuscript copies and the original case7302
evidence are unchanged. The existing global premises described below remain.

'''
t=t[:a]+block+t[b:]
t=t.replace('The milestone 100 checkpoint\nabove supersedes them:','The milestone 101 checkpoint\nabove supersedes them:')
p.write_text(t)
(ROOT/'handoff/README.md').write_text('''# Research handover

Start with [current status](CURRENT_STATUS.md) and the
[continuation assignment](NEXT_AGENT_PROMPT.md). The latest checkpoint is
[milestone 101](../milestones/101-context-specialization/README.md).

Exact evaluator equations now cover all 791 contexts. Complete finite
potential certificates cover two contexts per profile; the remaining 789
contexts per profile still need checking. The proof summary records exact
sources, dependency hashes, compiler logs, timings and axiom audits.

The maintained interval is 191 through 235 edges; 234 is conditional. The
contributor upper bound retains its archived audit and pending independent
rebuild. The optimum and conjecture 196 remain unresolved.

Milestone 98 supplies the actual weight, full-key walk and total charge;
99 supplies the potential candidates, checked ranges and exhaustive numerical
audit; 100 supplies prefix-traversal soundness; 101 supplies all fixed-context
equations and a context where capped history credit changes the final weight.

Preserve both reference catalogues and all five pending local share bounds.
The original case7302 target 20 replay is stopped. A target 18 proof must use
separate files. Reuse the existing proof overlay and successful receipts.

Paper revision 96, authors Iori Hironaka, Tommy Ma and Steven Zhan, and the
hyperlink settings are unchanged. The next full revision is 106. Use standard
notation and define only necessary concepts that are repeatedly used.
''')
p=ROOT/'handoff/NEXT_AGENT_PROMPT.md';previous=p.read_text();tail=previous[previous.index('## Global evidence and remaining assumptions'):]
tail=tail.replace('milestones/100-prefix-potential-checker/scripts/check.py','milestones/101-context-specialization/scripts/check.py')
tail=tail.replace('environment reuses milestone 99 and the milestone 98 support overlay.','environment reuses milestone 100 and the milestone 98 support overlay.')
intro='''# Continuation assignment

Continue the empty-square charging route in `E:/Snake-in-a-box`. Read milestone
101's mathematical note, checkpoint and proof summary. All 505 direction
equations and all 791 context equations passed Lean. The active goal remains
unresolved. Preserve standard notation and define only necessary, reused terms.

## Next task

'''+next_task+'''

The checked context families in namespace Snake9.Context101 are
selected_d_q, source_d_q, target_d_q, block_d_q, completed_d_q and conditional_d_q.
Direction lookups and conditioned-credit equations cover all 505 directions.
AllContextSpecializations101 imports every context without declaration
conflicts. The single emittedCredit helper keeps all original cap tests.

The explicit potential uses a balanced lookup over 206 blocks, each of size
7776. A fixed-block equality can reduce this repeated lookup to its recorded
subtree, while preserving the min551/min602 cap. Establish code/6<7776 from
code<46656 for the source; the target offset code%7776 is always bounded.
No performance gain from this proposed reduction is yet measured.
The source-block equation is not valid for arbitrary natural codes. Transfer
the bounded equality code by code with accepted_code_of_prefix_check and the
interval checker, or prove a bounded prefix congruence; do not use an
unrestricted rewrite under the count-code function.
PotentialChecker99.checkInterval_iff already introduces exactly the bounded
code obligation. Split on diagramKeep; a rejected code is immediate, and
accepted_code_of_prefix_check supplies the reduced inequality for an accepted
code. Rewrite the bounded potential equations at that point. This avoids
introducing a replacement context checker.

Reuse the complete finite theorems:

- Snake9.PrefixCertificates100.completed_context_reduced: completed35/0.
- Snake9.PrefixCertificates100.conditional_context_reduced: conditional177/43.
- Snake9.PrefixCertificates101.completed_context_99_37: completed99/37.
- Snake9.PrefixCertificates101.conditional_context_99_37: conditional99/37.

The first pair covers 7151 and 6598 accepted edges. The second pair each covers
6043 accepted edges. The latter share the same keys, so keep profile coverage
separate: 13194 completed and 12641 conditional accepted edges. Both profiles
still have 789 unproved complete contexts. Each context theorem covers all
46656 candidate codes with acceptance filtering.

EmittingReduction101 proves both weights agree at99/37. Rule000 contributes
19 if count symbols1 and2 (indexed from0) are at most2, and18 otherwise; the geometric and
floor credits do not change this history minimum. Four accepted codes activate
the stronger credit in both profiles. Their potentials and slopes differ,
so equal weights alone do not identify their finite inequalities.

The independent read-only review checked context data and import coverage.
The initial unqualified-canon pilot failure is preserved and superseded by
the corrected successful source. Do not repeat the old 300-second unreduced
context attempts. If needed, split a new check at the first count symbol and
assemble the six checked branches with PrefixChecker100 soundness.

The numerical582 joint context groups require exact Lean equality and
transport before reuse. Matching class roots or endpoint pairs alone is
insufficient. No compiler is active at the saved checkpoint.

'''
p.write_text(intro+tail)
print(c['status'],c['modules'],'modules;',c['theorem_audits'],'audits')
