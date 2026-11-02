"""Publish the completed prefix and context-specialization milestone."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (HERE/'data/check.lock').exists()
subprocess.run([sys.executable,'-B','-X','utf8',str(HERE/'scripts/audit.py')],check=True)
s=read(HERE/'data/proof-summary.json');prior=HERE.parent/'99-defined-potential-certificates/data/checkpoint.json';old=read(prior)
paper=ROOT/'paper/snake9_research.tex'
assert sha(paper)==old['paper_sha256']==sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))
case=ROOT/'milestones/73-countfree-share-catalogue/cases/case7302'
assert not (case/'data/proof-audit.json').exists()
assert sha(case/'logs/completion-record.json')==sha(ROOT/'milestones/93-defined-graph-potential/data/case7302-completion-observation.json')
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip() for ref in ['HEAD','origin/main']}
assert refs['HEAD']==refs['origin/main']
c=dict(status='PASS_PREFIX_SOUNDNESS_AND_TWO_COMPLETE_CONTEXTS',previous_goal_turn='progress',
    recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),proof_summary_sha256=sha(HERE/'data/proof-summary.json'),
    modules=len(s['modules']),theorem_audits=s['theorem_audits'],complete_contexts=s['contexts'],
    accepted_edges_checked=13749,complete_graph_potential_certificates_checked=False,
    exact_context_weight_and_endpoint_equalities_checked=True,generic_history_filter_equality_checked=True,
    prefix_soundness_checked=True,numerical_prefix_classes=127,
    unconditional_edge_interval=[191,235],conditional_target=234,upper_bound_evidence=old['upper_bound_evidence'],
    pending_reference_catalogues=old['pending_reference_catalogues'],pending_conditional_local_cases=old['pending_conditional_local_cases'],
    pending_share_floors=old['pending_share_floors'],case7302_state=old['case7302_state'],case7302_source_record_unchanged=True,
    paper_revision=96,next_scheduled_paper_revision=106,paper_sha256=sha(paper),
    prior_checkpoint=prior.relative_to(ROOT).as_posix(),prior_checkpoint_sha256=sha(prior),git_refs_before_commit=refs,
    next_task='Generate exact context constants and filtered history-rule lists, prove their pointwise equalities, and certify further complete contexts using prefix traversal. Reuse the two successful contexts and preserve remaining premises.',
    scope='Two complete finite contexts, all-code evaluator equalities and generic traversal soundness. The complete graph certificates and global numerical improvement remain unresolved.')
(HERE/'data/checkpoint.json').write_text(json.dumps(c,indent=2)+'\n')
table='\n'.join(f"| {x['profile']} | {x['direction']}/{x['history']} | {x['accepted_edges']:,} | {x['seconds']:.3f} |" for x in s['contexts'])
results='''## Checked results

Five modules passed with 25 theorem audits. Both complete contexts transfer to
the original context checker, using the exact original weights, endpoint
functions and potential candidates. No extra hypothesis is needed for either
finite context theorem.

| Profile | Direction/history | Accepted edges | Compiler seconds |
| --- | --- | ---: | ---: |
'''+table+'''

Each proof covers every one of the 46,656 codes in its context, with rejected
branches omitted by the checked soundness argument. Together the two contexts
contain 13,749 accepted edges. The earlier 207 accepted pilot edges lie inside
these contexts and are not additional coverage.

The old pointwise completed-context attempt and the prefix traversal with
unreduced weights both reached their 300-second limits. Those attempts remain
preserved. The successful checks also use exact context simplifications, so
the measured improvement concerns the combined implementation. The numerical
transition counts alone do not predict the compiler runtime.

## Exact weight and endpoint reductions

The history evaluator can discard every rule whose signature is not emitted
by the fixed direction/history context. Lean proves this equality for any
rule list and any count code. In particular, length-three signatures contribute
zero when the stored history has fewer than two symbols. Both selected
contexts emit no history share rule.

For the completed context $(35,0)$, Lean proves for every natural count code
$c$ that

$$w(c)=120(c\\bmod6+1)+
\\begin{cases}96,&c\\bmod7776=7106,\\\\0,&\\text{otherwise}.\\end{cases}$$

Its source and target indices are $77760+\\lfloor c/6\\rfloor$ and
$1049760+(c\\bmod7776)$. For the conditional context $(177,43)$, the weight is
$120(c\\bmod6+1)+16$, and the indices are $1353024+\\lfloor c/6\\rfloor$ and
$1500768+(c\\bmod7776)$. All these equalities are checked without a bound on $c$.
They simplify evaluation while retaining the original edge statement.

## Remaining work

The complete finite graph certificate remains pending for each profile. There
are 791 assigned contexts per profile, and this milestone completes one for
each. The 582 joint numerical context groups from milestone 99 still require
Lean equality and transport proofs before certificates can be reused.

The next step is to generate the constant data and emitted-rule list for each
context, prove the corresponding equalities once, and apply the checked prefix
traversal. Separate first-symbol branches can be used if a complete context
exceeds the resource limit. The original direct-evaluation sources are retained
as superseded benchmark implementations and should not be restarted blindly.

Two reference-catalogue closures remain for both global proof chains. The
conditional chain also retains the five local share floors
$(16,18,16,16,16)$, with refutation caps $(15,17,15,15,15)$. A finite potential
check does not discharge these local or reference assumptions.

The maintained interval remains $191\\le a(9)\\le235$ edges, with 234
conditional. The contributor upper bound retains its archived evidence and
pending independent rebuild. Existing proof objects are reused; no clean
rebuild of all dependencies is claimed. Paper revision 96 and its metadata
are unchanged; the next full revision is scheduled for milestone 106.
'''
p=HERE/'mathematical-note.md';text=p.read_text();start=text.index('## Verification status');p.write_text(text[:start]+results)
(HERE/'README.md').write_text('''# Milestone 100: checked prefix traversal and complete contexts

Lean now certifies two complete defined-graph contexts, covering 13,749 accepted
edges. The implementation combines a proved prefix traversal with exact
context-specific weight and endpoint equalities. Five modules and 25 theorem
audits passed; the complete finite graph certificates remain pending.

'''+results.split('## Exact weight and endpoint reductions')[0].replace('## Checked results','## Verification')+'''
Read the [mathematical note](mathematical-note.md),
[checkpoint](data/checkpoint.json), [proof summary](data/proof-summary.json),
and [prefix enumeration audit](data/prefix-enumeration-audit.json).
The maintained interval is $191\\le a(9)\\le235$ edges, with 234 conditional.
Original case7302 evidence and both manuscript copies are unchanged.
''')
latest=('Latest continuation: [milestone 100](milestones/100-prefix-potential-checker/README.md) proves shared-prefix traversal soundness and exact context weight/endpoint simplifications. Two complete contexts pass Lean, covering 13,749 accepted edges. The complete graph certificates remain pending. The maintained interval remains 191 through 235; 234 remains conditional.')
priority=('Next research priority: generate and prove constant context data and filtered history-rule lists, then certify further complete contexts with the checked prefix traversal. Reuse the two successful contexts; retain both reference-catalogue closures and the five conditional share assumptions. Paper revision 96 is unchanged; the next full revision is 106.')
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;t=p.read_text()
    for prefix,value in [('Latest continuation:',latest),('Next research priority:',priority)]:
        t,n=re.subn('^'+re.escape(prefix)+'.*$',lambda _:value,t,count=1,flags=re.M);assert n==1
    p.write_text(t)
p=ROOT/'milestones/README.md';t=p.read_text();i=t.index('- [Milestone 99:');assert '- [Milestone 100:' not in t
p.write_text(t[:i]+'- [Milestone 100: prefix traversal and complete context certificates](100-prefix-potential-checker/README.md). Exact evaluator reductions and two full Lean context checks; all-context certification remains pending.\n\n'+t[i:])
p=ROOT/'RESEARCH_LEDGER.md';t=p.read_text();assert '## Milestone 100:' not in t
p.write_text(t+'\n\n## Milestone 100: prefix traversal and exact context reductions\n\n'+latest+'\n\n| Profile | Direction/history | Accepted edges | Compiler seconds |\n| --- | --- | ---: | ---: |\n'+table+'\n\n'+priority+'\n')
p=ROOT/'handoff/CURRENT_STATUS.md';t=p.read_text();a=t.index('## Milestone 99 checkpoint');b=t.index('## Result and evidence boundary',a)
block='''## Milestone 100 checkpoint

The prefix traversal is sound: rejecting branches can be skipped and every
accepted code retains its original encoding and leaf inequality. Exact
history filtering, weight simplifications and endpoint formulas are checked.
The completed context 35/0 and conditional context 177/43 now pass Lean in
full, covering 7,151 and 6,598 accepted edges respectively. The earlier 207
pilot edges are included in this coverage. Five modules and 25 theorem audits
passed. See milestone 100's proof summary for exact timings and receipts.

The older pointwise and unreduced-prefix completed-context attempts timed out
at 300 seconds. The exact statements are now proved by ReducedCompleted100
and ReducedConditional100. The superseded implementations should be preserved,
not restarted. No compiler job remains active at this checkpoint.

Both potentials still pass all 4,947,008 defined graph edges numerically, with
zero extra or missing keys. Their concrete ranges 551 and 602 remain checked.
The complete Lean edge certificate remains pending for both profiles: one of
791 assigned contexts is now proved for each. The 582 joint numerical context
groups require equality/transport proofs before reuse.

The next step is to generate fixed context data and filtered history-rule
lists, prove pointwise equalities, and apply the checked traversal. The actual
weight, charge budget and full-key walk from milestone 98 remain available.
Both global chains retain two reference-catalogue closures. Conditional 234
also retains five local refutations with caps (15,17,15,15,15), giving floors
(16,18,16,16,16).

The maintained interval remains $191\\le a(9)\\le235$, with 234 conditional.
The contributor upper bound retains its archived evidence and pending complete
independent rebuild. Original case7302 target 20 evidence remains stopped and
unchanged; any target 18 proof needs separate files. Paper revision 96, authors
and hyperlink settings are unchanged; the next full revision is 106.

'''
t=t[:a]+block+t[b:];t=t.replace('The milestone 99 checkpoint\nabove supersedes them:','The milestone 100 checkpoint\nabove supersedes them:');p.write_text(t)
(ROOT/'handoff/README.md').write_text('''# Research handover

Start with [current status](CURRENT_STATUS.md) and the
[continuation assignment](NEXT_AGENT_PROMPT.md). The latest checkpoint is
[milestone 100](../milestones/100-prefix-potential-checker/README.md), containing
the mathematical argument, exact compiler receipts, numerical audit and
manifest. Two complete contexts are now certified in Lean. The full graph
certificates remain pending.

The maintained interval is $191\\le a(9)\\le235$ edges; 234 is conditional.
The contributor upper bound retains its archived audit and pending independent
rebuild. The exact optimum and the conjecture 196 remain unresolved.

Milestone 98 supplies the actual weights, full-key walk and total charge.
Milestone 99 supplies explicit potential candidates, checked range bounds and
the exhaustive numerical audit. Milestone 100 supplies the checked prefix
traversal and exact context simplifications. It certifies completed context
35/0 and conditional context 177/43, covering 13,749 accepted edges in total.
The earlier pilot edges lie within these contexts.

Continue with context specialization and further complete checks. Reuse
successful receipts. Preserve the original and unreduced-prefix timeout
attempts, both reference-catalogue premises and five conditional local shares.
The original case7302 target 20 attempt is stopped; a target 18 attempt must
use separate files. Reuse the existing proof overlay and milestone 100
environment instead of copying large object trees.

Paper revision 96 and its authors Iori Hironaka, Tommy Ma and Steven Zhan are
unchanged. The next full revision is 106. The open D: source and E: mirror
remain identical. Keep ordinary mathematical notation and define only
necessary concepts that are repeatedly used.
''')
(ROOT/'handoff/NEXT_AGENT_PROMPT.md').write_text('''# Continuation assignment

Continue the empty-square charging route in `E:/Snake-in-a-box`. Read milestone
100's mathematical note, checkpoint and proof summary. The previous turn made
progress: two complete graph contexts now pass Lean, through a checked prefix
traversal and exact context specialization. The active goal remains unresolved.

## Next task

Generate constant data and emitted history-rule lists for the remaining
contexts. Prove each specialization once, then use PrefixChecker100 with the
simplified leaf inequality and transfer it to the original contextCheck.
The generic historyCredit_filter_emitting theorem preserves all active rules
and their order. The short-history theorem removes the history contribution
when the stored prefix has fewer than two symbols. Fixed longer histories
can also emit no rule, as shown by the checked context 177/43 example.

Reuse these completed context theorems:

- ReducedCompleted100.completed_context_reduced: completed profile, slope 483,
  direction 35/history 0, all 7,151 accepted edges.
- ReducedConditional100.conditional_context_reduced: conditional profile,
  slope 496, direction 177/history 43, all 6,598 accepted edges.

Both are in namespace Snake9.PrefixCertificates100. PrefixChecker100 proves
contextCheck_of_prefix for arbitrary weights and potentials. ContextEndpoints100
and WeightSpecialization100 show how exact all-code equations transport a
small arithmetic check back to the original graph. Preserve source/history/
count keys, source/target order and raw state numbering.

The older CompletedContext100 and ConditionalContext100 sources are superseded
benchmark implementations. The former reached 300 seconds; the latter was not
started. Do not blindly restart them. If a new whole-context check is too
large, prove its six first-symbol branches separately and assemble them using
the same prefix recursion. Bound each trial and retain exact failed attempts.

Numerical classification gives 582 joint groups among 791 contexts, but these
groups need Lean equality and transport statements before certificate reuse.
Acceptance classes or endpoint pairs alone do not identify the weight.
One complete context per profile is proved so far; all-context certification
remains pending. The older 207 pilot edges lie inside the completed contexts.

## Global evidence and remaining assumptions

The maintained interval is $191\\le a(9)\\le235$ edges. The upper bound uses
the inspected contributor theorem and archived audit; a complete independent
rebuild remains pending. The improvement to 234 is conditional. No 196 witness
or optimality proof has been obtained.

Both potential arrays pass every one of the 4,947,008 defined graph edges in
independent exact-integer enumeration. There are zero extra/missing keys.
Both concrete potential range bounds are Lean-checked: 551 for completed,
602 for conditional floor 18. Completed slope is 483; conditional slope is 496.
The actual weight, boundary saving, total charge and full-key walk are checked
in milestone 98. Complete finite edge certificates remain in the final bounds.

Both chains still assume AllRefuted6K235 and AllRefuted236. Conditional 234
also assumes cases 7301, 7302, 7303, 7307, 7308 with refutation caps 15, 17, 15, 15, 15,
equivalently floors (16,18,16,16,16). Preserve the stopped original case7302
target 20 replay and its 649 successful modules. Any target 18 proof needs new
sources and evidence. Its old Check1 timeout was 900 seconds.

## Runtime, artifacts and publication

Use `milestones/100-prefix-potential-checker/scripts/check.py`, which snapshots
sources and checks dependencies, axioms and exact object/log bytes. Its
environment reuses milestone 99 and the milestone 98 support overlay. Do not
recopy the 3.3 GB overlay. Compile sequentially; keep at most three Lean jobs.
Do not add `-M4096`. Inspect live processes and records before any restart;
old active markers may be historical. Never edit a live checker or source.

Python is
`C:/Users/hironakaiori/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe`;
use `-B -X utf8`. Numerical packages are in `work/solver_packages`.
Lean 4.19 and mathlib are under
`D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research`.

Keep exact milestone bytes and manifests. Preserve unrelated `.gitignore`
and `milestones/50-three-count-return/excess-screen/data/critical-family.json`
changes. Fetch before committing, stage only reviewed files, verify staged
bytes and push after each completed research round.

The paper remains revision 96, with unchanged authors and hyperlink settings.
The next full revision is 106. The open source is
`D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex`; the mirror is
`E:/Snake-in-a-box/paper/snake9_research.tex`. Revise the open source in place
when due, keep the mirror identical and compile through the built-in tool.
Use standard notation; introduce a definition only when necessary and reused.
''')
print(c['status'],c['modules'],'modules;',c['theorem_audits'],'audits')
