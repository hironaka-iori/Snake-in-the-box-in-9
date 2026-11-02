"""Freeze the bounded potential-certification result and refresh the handover."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (HERE/'data/check.lock').exists()
subprocess.run([sys.executable,'-B','-X','utf8',str(HERE/'scripts/audit.py')],check=True)
summary=read(HERE/'data/proof-summary.json')
prior=HERE.parent/'98-concrete-weight-integration/data/checkpoint.json';old=read(prior)
paper=ROOT/'paper/snake9_research.tex'
assert sha(paper)==old['paper_sha256']==sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))
case=ROOT/'milestones/73-countfree-share-catalogue/cases/case7302'
assert not (case/'data/proof-audit.json').exists()
assert sha(case/'logs/completion-record.json')==sha(ROOT/'milestones/93-defined-graph-potential/data/case7302-completion-observation.json')
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip() for ref in ['HEAD','origin/main']}
assert refs['HEAD']==refs['origin/main']
full=summary['complete_context_modules']
descriptions={'CompletedContext99':'the completed profile at direction 35, history 0 (7,151 accepted edges)',
              'ConditionalContext99':'the conditional profile at direction 177, history 43 (6,598 accepted edges)'}
fullnote=('Complete-context Lean checks passed for '+', and '.join(descriptions[n] for n in full)+'.') if full else 'Complete-context Lean checks remain pending.'
if summary['pending_modules']:
    fullnote+=' Unfinished modules and their preserved attempts are listed in the proof summary; no failed or timed-out attempt proves its statement.'
for row in summary['pending_modules']:
    if row['status']=='TIMED_OUT':
        fullnote+=f" The {row['module']} attempt reached the 300-second limit."
    elif row['status']=='NOT_ATTEMPTED':
        fullnote+=f" {row['module']} was not started."
c=dict(status='PASS_NUMERIC_DEFINED_GRAPH_AND_CHECKED_POTENTIAL_RANGES',previous_goal_turn='progress',
    recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    proof_summary_sha256=sha(HERE/'data/proof-summary.json'),modules=len(summary['modules']),theorem_audits=summary['theorem_audits'],
    complete_context_modules=full,pending_modules=summary['pending_modules'],
    numerical_defined_graph_edges=4947008,numerical_extra_rows=0,numerical_missing_rows=0,
    potential_values_independently_reconstructed=3203712,concrete_ranges_checked=[551,602],
    generic_interval_and_context_soundness_checked=True,concrete_upper_bound_assembly_checked=True,
    complete_graph_inequality_checked_in_lean=False,
    pilot_interval=[9720,11880],pilot_accepted_edges=dict(completed=143,conditional=64),
    joint_context_groups=582,joint_context_reuse_checked_in_lean=False,
    pending_reference_catalogues=old['pending_reference_catalogues'],pending_conditional_local_cases=old['pending_conditional_local_cases'],
    pending_share_floors=old['pending_share_floors'],
    unconditional_edge_interval=[191,235],conditional_target=234,upper_bound_evidence=old['upper_bound_evidence'],
    case7302_state=old['case7302_state'],case7302_source_record_unchanged=True,
    paper_revision=96,next_scheduled_paper_revision=106,paper_sha256=sha(paper),
    prior_checkpoint=prior.relative_to(ROOT).as_posix(),prior_checkpoint_sha256=sha(prior),git_refs_before_commit=refs,
    next_task='Complete the finite potential certificates using checked intervals and context reuse; first specialize repeated context calculations and measure a bounded context. Preserve reference and five local assumptions.',
    scope='Both full defined-graph inequalities checked numerically; compact potential ranges, generic soundness and listed finite Lean checks certified. No new numerical global bound.')
(HERE/'data/checkpoint.json').write_text(json.dumps(c,indent=2)+'\n')

note=r'''# Potential certificates on the defined graph

Both saved potentials satisfy every edge inequality of the graph used by the
Lean interpretation. The independent enumeration finds exactly 4,947,008
accepted full keys, with no extra or missing keys relative to the saved graph.
This equality and the full edge scan are numerical results. Lean has checked
the concrete potential ranges, the interval-checking argument, the resulting
upper-bound statements with explicit finite-check assumptions, and the finite
checks recorded below. No new global numerical bound follows from this round.

## Mathematical argument

Use the existing edge weights and potential notation. For an edge $e:u\to v$
with weight $w_e$, the required inequality is

$$P+\pi(v)\le w_e+\pi(u),\qquad 0\le\pi\le R.$$

In this display the edge retains its complete direction, history and count
key; endpoint pairs alone need not identify its weight. Summing along the
$m-8$ graph edges of a snake gives

$$P(m-8)\le W+R.$$

Milestone 98 proves $W+4200m\le1098960$ for $m\ge9$. Hence

$$ (4200+P)m\le1098960+8P+R. $$

The completed profile has $P=483$ and $R=551$, giving
$4683m\le1103375<4683\cdot236$. The conditional profile has $P=496$ and
$R=602$, giving $4696m\le1103530<4696\cdot235$. The respective conclusions
are $m\le235$ and $m\le234$ after their remaining hypotheses are supplied.
The cases $m<9$ are immediate and included in the checked bound statements.

## Evidence obtained

The numerical checker reads the diagram and rule tables from Lean source
literals. It checks all 791 assigned contexts and all 127 shared acceptance
classes. The completed potential has 1,288,037 tight accepted edges; the
conditional potential has 1,828,136. Both have minimum slack zero.

The saved potentials are represented by shared six-way trees: 20,234 internal
nodes for the completed profile and 9,612 for the conditional profile, with
206 root positions each. A separate parser expands the actual generated Lean
literals and verifies all 3,203,712 entries against the original arrays.
Every entry agrees. Lean accepts the candidate definitions and proves their
range bounds for all natural state indices. Capping at the stated range
supplies this bound; the independent expansion confirms that the cap changes
none of the saved values.

Lean also verifies the accelerated diagram lookup against the original
diagram evaluation. The interval checker is proved sound and supports joining
adjacent intervals, transferring equal tests, and assembling complete
contexts. Missing context assignments are handled symbolically. The final
assembly uses these exact candidate potentials; it has no free potential or
range premise.

Both pilot intervals $9720\le c<11880$ passed Lean. The completed test uses
direction 35 and history 0, containing 143 accepted edges. The conditional
test uses direction 177 and history 43, containing 64 accepted edges. Rejected
codes impose no edge inequality. Smaller earlier pilot intervals lie inside
these intervals and are not additional coverage.

FULL_CONTEXT_NOTE

The exact successful modules, axiom reports, timings, source snapshots and
dependency hashes are recorded in `data/proof-summary.json`. Existing proof
objects and the milestone 98 object overlay are reused. This is not a clean
rebuild of every inherited proof dependency.

## Remaining proof obligations

The completed upper-bound assembly retains two reference-catalogue closures
and the Boolean certificate for every graph edge. The conditional assembly
also retains the five local refutations with caps $(15,17,15,15,15)$, or share
floors $(16,18,16,16,16)$, in case order 7301, 7302, 7303, 7307, 7308.
The complete finite edge certificate is still pending in Lean for both
profiles. Numerical success and individual context checks do not discharge it.

The original case7302 proof attempt, which targeted share 20, remains stopped
and unchanged. A proof of the weaker required share 18 must have separate
sources and evidence.

## Next step

Continue the finite potential verification using the checked interval
interface. Before expanding the batch, specialize the computations that are
constant in each direction/history context and measure a bounded test.
Traverse the acceptance diagram by shared prefixes and skip a branch as soon
as it reaches the rejecting leaf. This avoids restarting the same six-step
lookup for each of the 46,656 codes. Its soundness proof must retain the exact
prefix encoding and original acceptance predicate.
Repeated loading and reduction of the complete semantic environment may be
avoidable; any lighter evaluator must have a proved equality or valid
one-sided comparison with the current weight.

Independent comparison groups the 791 contexts into 582 joint classes of
identical acceptance roots, ordered potential blocks and complete weight
arrays. Every repeated array was compared directly after hash grouping.
This can remove 209 pairs of context checks once the corresponding Lean
equalities and transport are proved. Acceptance classes or endpoint pairs
alone are insufficient for that reuse.

The maintained interval remains $191\le a(9)\le235$ edges, with 234 conditional.
The contributor upper-bound theorem retains its archived audit and pending
independent rebuild. The exact optimum remains unresolved. Paper revision 96 is unchanged;
the next full revision is scheduled for milestone 106.
'''.replace('FULL_CONTEXT_NOTE',fullnote)
(HERE/'mathematical-note.md').write_text(note)
(HERE/'README.md').write_text('''# Milestone 99: concrete potential certificates

Both potential inequalities pass an independent exact-integer check on all
4,947,008 keys accepted by the defined graph. No extra or missing rows occur.
Lean checks the explicit potential ranges, the interval/context proof
interface, the conditional upper-bound assembly, and the finite tests recorded
in the proof summary. The complete edge certificate remains pending.

'''+fullnote+'''

Read the [mathematical note](mathematical-note.md),
[checkpoint](data/checkpoint.json), [proof summary](data/proof-summary.json),
[defined-graph audit](audit/defined-potential-audit.md),
[candidate-literal audit](audit/potential-literal-audit.md), and
[context reuse calculation](audit/context-compression.md).

The maintained interval remains $191\\le a(9)\\le235$ edges; 234 remains
conditional. Two reference-catalogue closures and five conditional local
refutations remain. Original case7302 evidence and both manuscript copies are
unchanged. No complete clean rebuild or new unconditional bound is claimed.
''')
latest=('Latest continuation: [milestone 99](milestones/99-defined-potential-certificates/README.md) verifies both potentials numerically on all 4,947,008 defined-graph edges, with zero extra or missing rows. Lean checks concrete ranges, interval/context soundness, the explicit-potential bound assembly and saved finite tests. The complete finite edge certificates remain pending. The global interval remains 191 through 235; 234 remains conditional.')
priority=('Next research priority: finish the potential edge certificates using bounded context checks, specializing repeated computations before a larger batch. Numerical context comparison gives 582 joint groups from 791 contexts; Lean reuse equalities remain necessary. Two reference-catalogue closures and five conditional local shares remain. Paper revision 96 is unchanged; the next full revision is 106.')
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;s=p.read_text()
    for prefix,value in [('Latest continuation:',latest),('Next research priority:',priority)]:
        s,n=re.subn('^'+re.escape(prefix)+'.*$',lambda _:value,s,count=1,flags=re.M);assert n==1
    p.write_text(s)
p=ROOT/'milestones/README.md';s=p.read_text();i=s.index('- [Milestone 98:')
assert '- [Milestone 99:' not in s
s=s[:i]+'- [Milestone 99: defined-graph potential checks and concrete ranges](99-defined-potential-certificates/README.md). Full numerical edge audit, checked potential candidates and finite Lean certificates; complete graph certificates remain pending.\n\n'+s[i:];p.write_text(s)
p=ROOT/'RESEARCH_LEDGER.md';s=p.read_text();assert '## Milestone 99:' not in s
p.write_text(s+'\n\n## Milestone 99: concrete potentials on the defined graph\n\n'+latest+'\n\n'+fullnote+'\n\n'+priority+'\n')
p=ROOT/'handoff/CURRENT_STATUS.md';s=p.read_text();a=s.index('## Milestone 98 checkpoint');b=s.index('## Result and evidence boundary',a)
block='''## Milestone 99 checkpoint

Both saved potentials pass every edge of the actual defined graph in an
independent exact-integer enumeration. The graph has precisely 4,947,008
accepted full keys across 791 contexts and 127 acceptance classes; there are
zero extra or missing rows relative to the saved array. This full enumeration
is numerical evidence, not a Lean theorem.

Lean accepts both compressed potential candidates and proves their ranges:
551 for the completed profile and 602 for the conditional floor-18 profile.
Independent parsing of the generated Lean literals reproduces all 3,203,712
saved values. Lean also checks the accelerated diagram lookup, interval and
context soundness, and the upper-bound assembly using these concrete candidates.
The two larger pilot intervals contain 143 and 64 accepted edges respectively.

'''+fullnote+'''

The complete edge certificate still remains in each final Lean bound statement.
Two reference-catalogue closures remain for both profiles; the conditional
profile also retains five local refutations with caps (15,17,15,15,15), giving
floors (16,18,16,16,16). The actual weight and total charge proofs from milestone
98 are complete and unchanged. All 127 coverage classes remain checked.

Numerical context reuse gives 582 joint groups from 791 contexts. Prove the
corresponding equalities before reusing certificates. First specialize repeated
context calculations and benchmark a bounded check; preserve full keys.

The maintained interval is $191\\le a(9)\\le235$, with 234 conditional. The
contributor upper-bound proof still needs a complete independent rebuild.
The original case7302 target-20 attempt remains stopped and unchanged; any
new target-18 proof must use separate files. Paper revision 96 and its metadata
are unchanged; the next full revision is 106. Use standard notation and define
only necessary concepts that are substantially reused.

'''
s=s[:a]+block+s[b:];s=s.replace('The milestone 98 checkpoint\nabove supersedes them:','The milestone 99 checkpoint\nabove supersedes them:');p.write_text(s)
(ROOT/'handoff/README.md').write_text('''# Research handover

Start with [current status](CURRENT_STATUS.md) and the
[continuation assignment](NEXT_AGENT_PROMPT.md). The current checkpoint is
[milestone 99](../milestones/99-defined-potential-certificates/README.md).
Its mathematical note, proof summary, exact manifest and independent audits
distinguish complete numerical evidence from the finite Lean checks.

The maintained interval is $191\\le a(9)\\le235$ edges. The upper bound retains
the contributor theorem and archived audit; its complete independent rebuild
is pending. The exact optimum and the conjecture 196 remain unresolved.
The proposed upper bound 234 remains conditional.

Milestone 98 completed the actual weight, full-key walk, boundary saving and
total charge integration. Milestone 99 checks both concrete potential ranges
and provides the finite checker and bound assembly. Both potentials pass all
defined edges numerically. The complete Lean edge certificates, two reference
catalogues and five conditional local refutations remain separate obligations.

'''+fullnote+'''

The least pending integer floor vector in the original target box remains
(16,18,16,16,16). The original case7302 target-20 proof attempt is stopped, with
649 successful modules preserved. A new target-18 attempt needs separate files.

Reuse the milestone 98 object overlay and milestone 99 environment file.
Inspect actual processes before restarting a job; old active markers may be
historical. Keep exact source, object and log hashes and run the milestone
verifier before staging. Preserve unrelated changes to `.gitignore` and
`milestones/50-three-count-return/excess-screen/data/critical-family.json`.

The paper remains revision 96, with Iori Hironaka, Tommy Ma and Steven Zhan as
authors and unchanged hyperlink settings. The next full revision is 106.
The authoritative editor source is
`D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex`; the repository mirror
is `E:/Snake-in-a-box/paper/snake9_research.tex`. Edit the open source in place
when a paper revision is due and use the built-in compiler on that source.
''')
(ROOT/'handoff/NEXT_AGENT_PROMPT.md').write_text('''# Continuation assignment

Continue the empty-square charging route in `E:/Snake-in-a-box`. Read milestone
99's mathematical note, checkpoint, proof summary and independent audits. Use
standard notation and introduce definitions only when necessary and repeatedly
used. The exact optimum remains unresolved; keep the active goal unfinished.

## Result and remaining assumptions

The maintained interval is $191\\le a(9)\\le235$ edges; 234 remains conditional.
The contributor upper bound retains its archived evidence and pending complete
independent rebuild. There is no 196 witness or optimality proof here.

The explicit completed potential has slope 483 and range 551. The conditional
floor-18 potential has slope 496 and range 602. Both pass all 4,947,008 defined
graph edges in independent Python enumeration, with zero extra or missing
keys. Independent parsing of the generated Lean literals reproduces every
saved potential entry. Their range bounds are checked in Lean for all states.

ConcreteAssembly99 states the final bounds with no free potential or range
premise. Each still assumes its graphCheck=true certificate. Both retain
AllRefuted6K235 and AllRefuted236; conditional234 also retains cases
7301,7302,7303,7307,7308 at caps15,17,15,15,15. These correspond to pending
share floors (16,18,16,16,16). Do not conflate numerical checking, a selected
context theorem and the complete finite graph certificate.

## Next task

Finish the graph-potential certificate, using the same defined graph and exact
Weights98 weight. PotentialChecker99 gives interval joining, test transfer,
context assembly, missing-block handling, and graph soundness. FastDiagram99
provides a proved-equal balanced diagram lookup. PotentialPilotLarge99 proves
both test intervals [9720,11880) and transfers them to the original checker.
They contain 143 completed-profile and 64 conditional-profile accepted edges.

'''+fullnote+'''

Check the proof-summary receipts before treating any full-context source as
proved. Do not blindly restart a timeout. Specialize repeated constant
direction/history calculations and benchmark before launching a large batch.
Prefer a traversal of shared count prefixes that skips rejecting diagram
branches. Prove that it covers the original accepted codes with their exact
encoding; the current pointwise lookup restarts for all 46,656 codes.
A lighter computational evaluator may avoid repeatedly importing and reducing
the full semantic environment; prove its equality or a sufficient one-sided
weight bound before reuse.

Numerical context classification has 582 completed groups and 564 conditional
groups, or 582 joint groups. Its tuples contain the acceptance root, ordered
source/target potential blocks and all 46,656 weight values. Reuse requires
Lean equality/transport statements. Acceptance classes and endpoint pairs
alone cannot replace the full direction/history/count key.

## Exact files and runtime

Candidate sources: `milestones/99-defined-potential-certificates/lean`.
Saved potentials:
`milestones/73-countfree-share-catalogue/data/proved-potential.i64.gz` and
`milestones/97-geometric-credit-integration/floor-sensitivity/012034-minimum/floor18-potential.i64.gz`.
Do not substitute the old floor20/range600 potential for floor18/range602.

Use `milestones/99-defined-potential-certificates/scripts/check.py` for bounded
sequential compilation and exact receipts. Reuse its environment and the
existing milestone 98 support overlay; do not recopy the 3.3 GB overlay.
The checker has a 300-second per-module limit and stores failed attempts.
Do not edit a source or checker while its process is running. Inspect both
the lock/record and actual process before resuming; old markers can be stale.

Python:
`C:/Users/hironakaiori/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe`.
Use `-B -X utf8`; numerical packages are in `work/solver_packages`.
Lean 4.19 and mathlib are under
`D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research`.
Do not add `-M4096`; keep at most three compiler processes, preferably one.

The original case7302 target20 replay is stopped after a 900-second Check1
timeout, with 649 successful modules. Preserve it. A new share18 proof needs
separate sources and receipts. Keep all milestone bytes, hashes and logs.
Preserve unrelated `.gitignore` and milestone50 critical-family changes.

Paper revision 96, authors and hyperlink settings remain unchanged. The next
full revision is 106. Keep the existing D: editor source and E: mirror aligned;
compile the original open document if a revision becomes necessary.
Fetch before committing and push only the reviewed milestone/handover files.
''')
print(c['status'],c['modules'],'modules;',c['theorem_audits'],'audits;',fullnote)
