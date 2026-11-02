"""Publish the audited potential-block reduction without changing the manuscript."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (HERE/'data/check.lock').exists()
subprocess.run([sys.executable,'-B','-X','utf8',str(HERE/'scripts/audit.py')],check=True)
s=read(HERE/'data/proof-summary.json');prior=ROOT/'milestones/101-context-specialization/data/checkpoint.json';old=read(prior)
paper=ROOT/'paper/snake9_research.tex'
assert sha(paper)==old['paper_sha256']==sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))
case=ROOT/'milestones/73-countfree-share-catalogue/cases/case7302'
assert not (case/'data/proof-audit.json').exists()
assert sha(case/'logs/completion-record.json')==sha(ROOT/'milestones/93-defined-graph-potential/data/case7302-completion-observation.json')
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip() for ref in ['HEAD','origin/main']}
assert refs['HEAD']==refs['origin/main']
next_task=('Retain the original decidable leaf comparison. Reduce repeated potential-tree evaluation inside the prefix check, following the feasibility note. '
    'Prove the traversal invariant and needed tree-shape facts before running a bounded comparison. '
    'Use the checked block equations and bounded transfer, preserve the original min caps and every accepted code, '
    'and extend the remaining finite certificates once the method is verified.')
c=dict(status='PASS_POTENTIAL_BLOCK_REDUCTION_AND_EIGHT_NEW_CONTEXTS',previous_goal_turn='progress',
    recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),proof_summary_sha256=sha(HERE/'data/proof-summary.json'),
    modules=len(s['modules']),theorem_audits=s['theorem_audits'],fixed_block_equations=412,new_definitions=0,
    complete_contexts=s['complete_contexts'],finite_coverage_by_profile=s['finite_coverage_by_profile'],comparisons=s['comparisons'],boolean_comparison=s['boolean_comparison'],
    complete_graph_potential_certificates_checked=False,unconditional_edge_interval=[191,235],conditional_target=234,
    upper_bound_evidence=old['upper_bound_evidence'],pending_reference_catalogues=old['pending_reference_catalogues'],
    pending_conditional_local_cases=old['pending_conditional_local_cases'],pending_share_floors=old['pending_share_floors'],
    case7302_state=old['case7302_state'],case7302_source_record_unchanged=True,
    paper_revision=96,next_scheduled_paper_revision=106,paper_sha256=sha(paper),
    prior_checkpoint=prior.relative_to(ROOT).as_posix(),prior_checkpoint_sha256=sha(prior),git_refs_before_commit=refs,
    next_task=next_task,scope='Bounded potential reduction and six complete contexts per profile. The full graph certificates and a smaller global snake bound remain unresolved.')
(HERE/'data/checkpoint.json').write_text(json.dumps(c,indent=2)+'\n')
new=[x for x in s['complete_contexts'] if x['origin_milestone']==102]
table='\n'.join(f"| {x['profile']} | {x['direction']}/{x['history']} | {x['accepted_edges']:,} | {x['seconds']:.3f} |" for x in new)
comparisons='\n'.join(f"| {x['profile']} | {x['archived_seconds']:.3f} | {x['seconds']:.3f} |" for x in s['comparisons'])
coverage='\n'.join(f"| {p} | {v['contexts']} | {v['accepted_edges']:,} | {791-v['contexts']} |" for p,v in s['finite_coverage_by_profile'].items())
bc=s['boolean_comparison']
results=f'''All 412 fixed-block equations passed Lean, together with the generic
bounded transfer to the original context checker. No definition was added.
The milestone contains {len(s['modules'])} checked modules and {s['theorem_audits']}
distinct theorem axiom audits. Successful sources contain no incomplete proof
or unchecked native evaluation; the permitted logical axioms are propext,
Classical.choice and Quot.sound.

Eight new complete profile/context checks passed:

| Profile | Direction/history | Accepted edges | Compiler seconds |
| --- | --- | ---: | ---: |
{table}

Including the earlier certificates, coverage is:

| Profile | Complete contexts | Accepted edges | Remaining contexts |
| --- | ---: | ---: | ---: |
{coverage}

Each context certificate covers all 46,656 candidate codes through the
checked acceptance test. Counts for different profiles are kept separate.
The repeated comparison context 99/37 adds no coverage.

For that same context, the recorded timings are:

| Profile | Archived implementation, seconds | Fixed-block implementation, seconds |
| --- | ---: | ---: |
{comparisons}

The archived and current runs had different workloads. These are observed
timings, without a controlled speedup claim or an extrapolation to all contexts.

A separate matched pair changed only the leaf comparison in completed 99/37.
The decidable comparison took {bc['decide_seconds']:.3f} seconds and direct
Boolean comparison took {bc['ble_seconds']:.3f} seconds. The runs were sequential,
with no other Lean process at launch. Both prove the same original context
statement. This is one pair; it does not establish performance on other contexts
or isolate unrelated system activity. The semantic equality is checked in Lean.
The direct Boolean variant was slower in this pair and is not adopted as an
optimization. This observation does not prove it is slower in every context.
'''
note=r'''# Potential lookup reduction with an explicit code bound

## Argument

The two existing potentials each use 206 blocks of 7776 entries. Once the
source or target block is fixed, its root lookup can be evaluated once.
For natural numbers $b$ and $r$ with $r<7776$,

$$
\left\lfloor\frac{7776b+r}{7776}\right\rfloor=b,
\qquad (7776b+r)\bmod7776=r.
$$

Substitution into the existing potential formula gives its exact value from
the recorded root for block $b$ and offset $r$. The original minimum with
551 or 602 is retained. The 206 root selections for each profile are checked
against the original balanced lookup by Lean; the source-text extraction
used to propose the roots is not trusted as proof.

For an edge code $c<46656$, the source offset is
$\lfloor c/6\rfloor<7776$. The target offset is $c\bmod7776<7776$.
The source reduction therefore needs the explicit code bound. It is not
asserted for arbitrary natural codes. The weight and endpoint equalities
from milestone 101 can still be used without a code bound.

The bounded transfer theorem proves the original context checker from a
successful reduced prefix test. For each code in its interval, a rejected
code satisfies the original edge check directly. An accepted code receives
the reduced inequality from the previously proved prefix soundness theorem;
the bounded equality then gives the original inequality. Direction, history,
count encoding, edge weight and potential cap remain exactly the same.

This is an equality-based reduction in certificate evaluation. It strengthens
neither the local share estimates nor the graph's potential slope.

## Checked results

'''+results+r'''
## Global status and continuation

The maintained project interval remains $191\le a(9)\le235$ edges. The upper
bound retains the inspected contributor theorem and archived audit, with its
complete independent rebuild pending. The target 234 remains conditional.
The optimum and conjecture 196 remain unresolved.

The complete graph certificate still has 785 contexts remaining per profile.
Both global chains also retain AllRefuted6K235 and AllRefuted236. The
conditional chain additionally retains the five local share refutations with
caps $(15,17,15,15,15)$, giving floors $(16,18,16,16,16)$. The original case7302
target 20 record is unchanged and stopped; a target 18 proof requires new files.

The direct Boolean comparison experiment is complete and its limited timing
evidence is recorded above. Both forms use Lean's existing natural-number
comparison; the experiment does not establish a new comparison algorithm.

The next candidate optimization is to reduce repeated descent through the
two potential trees while the acceptance prefix is traversed. Its exact
invariant and shape obligations are discussed in the feasibility note. It has
not yet been implemented, checked in Lean or benchmarked. Successful context
certificates from milestones 100, 101 and 102 should all be reused.

The initial redundant import of an unavailable Omega module failed before
the proof was processed. The corrected source uses the already available
tactic and passed. Both attempts are preserved with their exact source bytes.
No compiler remains active at the saved checkpoint.

Paper revision 96, its three authors and hyperlink settings are unchanged.
The next scheduled full revision is 106.
'''
(HERE/'mathematical-note.md').write_text(note,encoding='utf-8')
(HERE/'README.md').write_text('''# Milestone 102: bounded potential-block reduction

'''+results+'''
Read the [mathematical note](mathematical-note.md),
[proof summary](data/proof-summary.json), [checkpoint](data/checkpoint.json),
and [next optimization analysis](audit/next-optimization.md).

The [contributor handover review](audit/remote-review.json) records the separate
branch's pending 234 construction. Its remaining builds do not supply a
completed certificate for this model.

The candidate JSON records proposed data; current proof status comes from
the individual Lean receipts and the proof summary. The global interval
remains 191 through 235 edges; 234 is conditional.
''',encoding='utf-8')
latest=('Latest continuation: [milestone 102](milestones/102-potential-block-reduction/README.md) proves bounded potential-block reduction and all 412 fixed root selections. Eight new complete profile/context checks pass, for six contexts per profile. The complete graph certificates remain pending; the interval remains 191 through 235, with 234 conditional.')
priority='Next research priority: '+next_task+' Paper revision 96 is unchanged; the next full revision is 106.'
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;t=p.read_text()
    for prefix,value in [('Latest continuation:',latest),('Next research priority:',priority)]:
        t,n=re.subn('^'+re.escape(prefix)+'.*$',lambda _:value,t,count=1,flags=re.M);assert n==1
    p.write_text(t)
p=ROOT/'milestones/README.md';t=p.read_text();i=t.index('- [Milestone 101:');assert '- [Milestone 102:' not in t
p.write_text(t[:i]+'- [Milestone 102: bounded potential-block reduction](102-potential-block-reduction/README.md). All 412 fixed block equations and eight new finite profile/context checks; six complete contexts per profile.\n\n'+t[i:])
p=ROOT/'RESEARCH_LEDGER.md';t=p.read_text();assert '## Milestone 102:' not in t
p.write_text(t+'\n\n## Milestone 102: bounded potential-block reduction\n\n'+latest+'\n\n'+results+'\n'+priority+'\n')
p=ROOT/'handoff/CURRENT_STATUS.md';t=p.read_text();a=t.index('## Milestone 101 checkpoint');b=t.index('## Result and evidence boundary',a)
t=t[:a]+'## Milestone 102 checkpoint\n\n'+results+'\n'+next_task+'\n\n'+t[b:]
t=t.replace('The milestone 101 checkpoint\nabove supersedes them:','The milestone 102 checkpoint\nabove supersedes them:');p.write_text(t)
(ROOT/'handoff/README.md').write_text('''# Research handover

Start with [current status](CURRENT_STATUS.md) and the
[continuation assignment](NEXT_AGENT_PROMPT.md). The latest checkpoint is
[milestone 102](../milestones/102-potential-block-reduction/README.md).

All 791 context equations and all 412 potential-block equations are checked.
Six complete contexts per profile now pass the original finite checker;
785 per profile remain. Exact sources, dependency hashes, logs, axiom reports
and preserved failed attempts are recorded in each milestone.

The maintained interval is 191 through 235 edges; 234 remains conditional.
The contributor upper bound retains its archived audit and pending independent
rebuild. The optimum and conjecture 196 remain unresolved.

Milestone 98 supplies the actual weight, full-key walk and charge; 99 supplies
the potentials and ranges; 100 supplies prefix soundness; 101 supplies all
context equations; 102 reduces fixed potential lookups with explicit bounds.

Preserve both reference catalogues, the five pending local share bounds and
the stopped original case7302 target 20 evidence. A target 18 proof needs
separate files. Reuse the existing proof overlay and successful receipts.

Paper revision 96, authors Iori Hironaka, Tommy Ma and Steven Zhan, and hyperlink
settings are unchanged. The next full revision is 106. Use standard notation
and introduce definitions only when necessary and repeatedly used.
''')
p=ROOT/'handoff/NEXT_AGENT_PROMPT.md';previous=p.read_text();tail=previous[previous.index('## Global evidence and remaining assumptions'):]
tail=tail.replace('milestones/101-context-specialization/scripts/check.py','milestones/102-potential-block-reduction/scripts/check.py')
tail=tail.replace('environment reuses milestone 100 and the milestone 98 support overlay.','environment reuses milestone 101 and the milestone 98 support overlay.')
intro='''# Continuation assignment

Continue the empty-square charging route in `E:/Snake-in-a-box`. Read milestone
102's mathematical note, proof summary and audit/next-optimization.md. The
previous round made progress: all 412 fixed potential-block equations and
eight new complete profile/context checks passed. The active goal is unresolved.

## Next task

'''+next_task+'''

The existing block equalities are Snake9.PotentialBlocks102.completed_at_i
and conditional_at_i for i from 0 through 205. Each takes offset and a proof
offset<7776, and returns the exact original capped potential value at its
recorded subtree. The source offset code/6 requires code<46656; the target
offset code%7776 is always bounded. No equality for arbitrary source codes
was introduced. Root selections are checked by Lean against the original table.

The generic transfer is
Snake9.BoundedPrefixTransfer102.contextCheck_of_bounded_prefix, with arguments
test, w, P, pi, direction, history, class, block equality, successful prefix
test, and pointwise test equality on accepted codes below 46656. It proves
the original contextCheck. It introduces no new actual-snake premise.

Reuse every complete context listed in milestone 102's proof summary:
the completed profile at 35/0 and conditional profile at 177/43 from milestone 100;
both profiles at 99/37 from milestone 101; and both profiles at 0/0, 1/0, 9/0
and 10/0 from milestone 102. There are six per profile.
The new versions of 99/37 are comparison checks and add no coverage.
The context-specific formulas in milestone 101 remain available for all 791
contexts; no replacement graph or weight model is required.

The observed fixed-block timings at 99/37 are 56.860 s and 110.016 s, compared
with archived times of 111.750 s and 194.312 s. Workloads differed; do not state
a controlled speedup factor. The proof summary also records a fresh sequential
pair for direct Boolean versus decidable comparison. Both variants are checked;
their timings are one-context observations. The full graph still has 785
unproved contexts per profile.
Avoid simply launching all remaining expensive checks before testing the next
credible reduction. Preserve all successful certificates.

The matched Boolean experiment observed 61.672 s for the decidable comparison
and 92.234 s for direct Boolean comparison. Retain the decidable comparison;
this one pair supplies no performance improvement to pursue. It does not
establish a universal ordering of the two variants.

The proposed next traversal is unimplemented and unverified. Its source
potential uses the first five of six symbols and its target the last five.
The feasibility note identifies the shape and offset obligations. Confirm
those obligations and a bounded benchmark before claiming it is useful.

No compiler is active at this checkpoint. The unavailable redundant Omega
import failure is preserved and superseded by the corrected successful source.

'''
p.write_text(intro+tail)
print(c['status'],c['modules'],'modules;',c['theorem_audits'],'audits')
