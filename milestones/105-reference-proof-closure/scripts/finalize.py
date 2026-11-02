"""Save the checked union interface and an immutable observation of the live batch."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (HERE/'data/checkpoint.json').exists()
assert not (HERE/'data/check.lock').exists()
s=read(HERE/'data/proof-summary.json');assert s['status']=='PASS_EXACT_REFERENCE_UNION_INTERFACE'
prior_path=ROOT/'milestones/103-joint-potential-traversal/data/checkpoint.json';prior=read(prior_path)
assert sha(ROOT/'paper/snake9_research.tex')==prior['paper_sha256']==sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))
batch=ROOT/'milestones/104-complete-potential-batch';live=read(batch/'data/batch-progress.json')
assert live['status']=='RUNNING'
raw=subprocess.check_output(['powershell','-NoProfile','-Command',f'Get-Process -Id {int(live["pid"])} -ErrorAction Stop | Select-Object Id,ProcessName | ConvertTo-Json -Compress'],text=True)
process=json.loads(raw);assert process['Id']==live['pid']
snapshot=dict(recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),verified_process=process,state=live)
(HERE/'data/batch-observation.json').write_text(json.dumps(snapshot,indent=2)+'\n')
extra=[]
tracked=set(subprocess.check_output(['git','-c','core.commitGraph=false','ls-files','--','milestones/104-complete-potential-batch'],cwd=ROOT,text=True).splitlines())
for g in live['selected']:
    name=g['module'];rp=batch/'data'/(name+'-audit.json');r=read(rp)
    assert sha(rp)==g['receipt_sha256'] and r['status']=='PASS_COMPLETE_BATCH_MODULE'
    assert sha(batch/'lean'/(name+'.lean'))==r['source_sha256']==sha(batch/r['source_snapshot'])
    assert sha(batch/r['log'])==r['log_sha256'] and sha(batch/'build'/(name+'.olean'))==r['olean_sha256']
    for a in r['theorem_audits']:assert set(a['axioms'])<={'propext','Classical.choice','Quot.sound'}
    for p in [rp,batch/r['log'],batch/r['source_snapshot'],(batch/r['source_snapshot']).parent/'checker.py.txt']:
        if p.relative_to(ROOT).as_posix() not in tracked:extra.append(p)
(HERE/'data/additional-batch-evidence.json').write_text(json.dumps([p.relative_to(ROOT).as_posix() for p in sorted(set(extra))],indent=2)+'\n')
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip() for ref in ['HEAD','origin/main','origin/research/unconditional-241']}
assert refs['HEAD']==refs['origin/main']
c=dict(status='PASS_EXACT_REFERENCE_UNION_INTERFACE_WITH_ACTIVE_GRAPH_BATCH',previous_goal_turn='progress',
    recorded_at=snapshot['recorded_at'],proof_summary_sha256=sha(HERE/'data/proof-summary.json'),
    source_selection_sha256=sha(HERE/'data/source-selection.json'),batch_observation_sha256=sha(HERE/'data/batch-observation.json'),
    checked_theorems=5,new_definitions=0,pending_reference_proposition='AllRefutedList Snake9.Reference85.referenceKeys',
    reference_union_refutation_checked=False,complete_graph_potential_certificates_checked=False,
    replaces_old_catalogue_hypotheses_in_new_route=['AllRefuted6K235','AllRefuted236'],
    selected_reference_keys=1378,full_source_roots=1383,unused_source_roots=5,
    pending_conditional_local_cases=prior['pending_conditional_local_cases'],pending_share_floors=prior['pending_share_floors'],
    unconditional_edge_interval=[191,235],conditional_target=234,upper_bound_evidence=prior['upper_bound_evidence'],
    case7302_state=prior['case7302_state'],paper_revision=96,next_scheduled_paper_revision=106,paper_sha256=prior['paper_sha256'],
    git_refs_before_commit=refs,scope='The general implications are checked. The exact union refutations and complete graph certificates remain pending. The source selection is not a refutation proof.')
(HERE/'data/checkpoint.json').write_text(json.dumps(c,indent=2)+'\n')
note=r'''# The exact reference list suffices

The graph tests a fixed list of 1,378 reference patterns. Suppose every pattern
in that list is impossible in its stated local model. This is the remaining
reference-refutation assumption; the present argument does not prove it.

Take any fitting nine-direction window of an actual snake. For each reference
pattern that fits inside it, the assumed local refutation rules out both the
forward pattern and its joint direction-and-count reversal. The existing
length, count and coordinate-normalization lemmas justify these applications.
Hence the window passes the reference filter. The other three filter families
and both history-compatibility conditions already hold independently of the
reference catalogue. The window therefore passes the unchanged full filter.

The checked graph-coverage result places that window in the graph with its
complete direction, history and count key. Applying the graph's potential
inequality to each such row and telescoping gives the existing inequality

$$P(m-8)\le W+R.$$

Here the notation has its existing meaning: $m$ is the number of snake edges,
$W$ the total graph weight, $P$ the potential slope and $R$ its range bound.
The total-weight budget is unchanged:

$$W+4200m\le1098960.$$

For $m\ge9$, the two inequalities give

$$(4200+P)m\le1098960+8P+R.$$

The completed profile has $(P,R)=(483,551)$ and gives $m\le235$ under its
explicit reference and complete-graph premises. The conditional profile has
$(P,R)=(496,602)$ and gives $m\le234$ under those premises and the same five
local share assumptions as before. The case $m<9$ is immediate in both bounds.

Lean checked all five implications in this chain. No definitions were added.
The exact reference union, the complete graph inequalities and the five
conditional share claims remain distinct obligations. A partial graph check
cannot replace the complete graph premise.

## Which contributor proofs are needed

The pinned contributor wrappers identify one exact source entry for each
selected reference key. A direct selection uses 732 entries from the R4
catalogue, 635 from K6 and 11 additional entries from R4b. The selection checks
the literal key, its index, the semantic proof name and the refutation proof
name. It needs 1,378 distinct proof roots. The three full source catalogues
together reference 1,383 distinct roots, so only five roots are omitted.
This count is not a runtime estimate or a new combinatorial bound.

All selected generated semantic source files are present at the pinned Git
paths. The 1,378 generated refutation source files are absent at those paths.
The closed wrapper statements and historical Linux logs therefore cannot be
imported as freshly checked local proofs. Their missing refutation roots must
be recovered or regenerated and checked, with their exact dependencies.
This is a statement about the pinned Git paths, not a whole-machine absence
claim or a claim that the underlying proof data have been lost.

The new argument makes the required list explicit and avoids reconstructing
the two larger catalogue propositions. It preserves every reference test used
by the graph, every accepted edge, both potential caps and the full charge
budget. It establishes no smaller numerical bound by itself.

## Current status

The maintained project interval remains $191\le a(9)\le235$ edges. The 235
upper bound retains the contributor's archived evidence and pending complete
independent rebuild. The target 234 and the exact optimum remain unresolved.
The active milestone 104 batch continues its complete graph certification.
Its live record is authoritative for current progress; this milestone stores
an immutable process-verified observation.

The manuscript remains revision 96. The scheduled full revision at 106 should
present this argument with ordinary notation and explicit remaining premises.
The original case 7302 target 20 replay remains stopped and unchanged; a target 18
proof needs separate sources and evidence.
'''
(HERE/'mathematical-note.md').write_text(note,encoding='utf-8')
counts=live['contexts_checked_by_profile']
summary=f'''Five general theorems passed Lean with only propext, Classical.choice and
Quot.sound. No definitions were added. The new route assumes refutations for
the exact 1,378-pattern reference union, together with the unchanged complete
graph check and, for 234, the five local share premises. It does not prove
those remaining assumptions.

The source selection uses 1,378 of the 1,383 distinct roots in the full source
catalogues. All selected semantic sources are present in the pinned Git trees;
the generated refutation sources are absent there. This source audit supplies
no closed refutation.

Milestone 104 remains active. The saved process-verified observation records
{counts['completed']} completed-profile and {counts['conditional']} conditional-profile
contexts checked. Read its local data/batch-progress.json for current progress.
The interval remains 191 through 235 edges, with 234 conditional.
'''
(HERE/'README.md').write_text('# Milestone 105: exact reference-proof obligation\n\n'+summary+'''
Read the [mathematical argument](mathematical-note.md),
[checked proof summary](data/proof-summary.json),
[source selection](data/source-selection.json) and [checkpoint](data/checkpoint.json).
The older two-catalogue route remains available; the new route uses the exact
union proposition directly. The source selection records pending certificates.
''')
latest=('Latest continuation: [milestone 105](milestones/105-reference-proof-closure/README.md) proves that the exact 1,378-pattern reference union suffices for both existing upper-bound arguments. Five theorems pass Lean; no definitions are added. The union refutations and complete graph checks remain pending. Milestone 104 continues its active batch; the numerical interval is unchanged.')
priority=('Next research priority: Preserve the running milestone 104 batch and complete its audit. Recover or regenerate the exact reference refutation roots selected in milestone 105. The five conditional share premises remain. Revise the manuscript at scheduled milestone 106 using ordinary notation and explicit proof obligations.')
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;t=p.read_text()
    for prefix,value in [('Latest continuation:',latest),('Next research priority:',priority)]:
        t,n=re.subn('^'+re.escape(prefix)+'.*$',lambda _:value,t,count=1,flags=re.M);assert n==1
    p.write_text(t)
p=ROOT/'milestones/README.md';t=p.read_text();i=t.index('- [Milestone 104:');assert '- [Milestone 105:' not in t
p.write_text(t[:i]+'- [Milestone 105: exact reference-proof obligation](105-reference-proof-closure/README.md). Five checked implications using the exact union; closed refutations remain pending.\n\n'+t[i:])
p=ROOT/'RESEARCH_LEDGER.md';t=p.read_text();assert '## Milestone 105:' not in t
p.write_text(t+'\n\n## Milestone 105: exact reference-proof obligation\n\n'+summary+'\n'+priority+'\n')
p=ROOT/'handoff/CURRENT_STATUS.md';t=p.read_text();i=t.index('## Milestone 104 active batch')
p.write_text(t[:i]+'## Milestone 105 checkpoint\n\n'+summary+'\nThe new exact-union premise supersedes the two-catalogue premise only in the\nnew theorem chain. Earlier checkpoint descriptions below are historical.\n\n'+t[i:])
(ROOT/'handoff/README.md').write_text('''# Research handover

Start with [current status](CURRENT_STATUS.md) and the
[continuation assignment](NEXT_AGENT_PROMPT.md). The latest completed proof
step is [milestone 105](../milestones/105-reference-proof-closure/README.md).
The [milestone 104 batch](../milestones/104-complete-potential-batch/README.md)
is still active; inspect its process and live record before starting anything.

The new theorem chain needs refutations for the exact 1,378-pattern reference
union and the complete graph inequalities. Conditional 234 also needs the
same five local share claims. Five general implications are checked; these
remaining premises are not discharged by milestone 105.

The maintained interval is 191 through 235 edges. The contributor's 235 result
retains its archived audit and pending independent rebuild. The optimum and
conjecture 196 remain unresolved. Keep the original case 7302 replay unchanged.

The paper remains revision 96, with authors Iori Hironaka, Tommy Ma and Steven
Zhan and unchanged hyperlink settings. Revision 106 is next. Introduce a
definition only when necessary and repeatedly used.
''')
(ROOT/'handoff/NEXT_AGENT_PROMPT.md').write_text('''# Continuation assignment

Continue the empty-square route in E:/Snake-in-a-box. Read milestone 105's
mathematical note and checkpoint, then the live record and NEXT.md in
milestone 104. The complete certification batch is still active. Verify its
recorded processes; do not start a duplicate or edit a live proof/checker.

## Checked step and next obligations

Snake9.ReferenceAssembly105.completed235 and conditional234 take the existing
complete graphCheck, potential range and exact hypothesis
AllRefutedList Snake9.Reference85.referenceKeys. The latter theorem retains
all five local share refutations. All five supporting implications passed
Lean and standard-axiom audits. No definitions were added. The new theorem
chain does not require reconstructing AllRefuted6K235 or AllRefuted236.

The exact 1,378-key source map is in milestones/105-reference-proof-closure/data/source-selection.json.
It selects 732 R4 entries, 635 K6 entries and 11 R4b entries. The full source
catalogues share roots; the new selection omits only five distinct roots.
All selected semantic sources exist in the pinned Git trees, but their
generated Unsat root sources do not. Recover or regenerate those roots from
the saved proof artifacts and compatible generators; historical logs and
wrapper names do not supply a new local check. Do not claim all proof data
are absent: the audit checked the stated Git source paths.

Milestone 104 will generate and check AllCompleted104 and AllConditional104
after all groups pass. Its successful sources and receipts are immutable.
Complete its full dependency/axiom/coverage audit before publishing the graph
certificates as finished. The current batch and exact-union obligation serve
both upper-bound profiles.

Conditional 234 additionally needs cases 7301, 7302, 7303, 7307, 7308 with caps
15, 17, 15, 15, 15, giving floors 16, 18, 16, 16, 16. The original case 7302 target 20
replay remains stopped after its preserved 900-second timeout and 649 successful
modules. A target 18 proof needs separate files. Do not restart the old replay.

The maintained interval is 191 through 235 edges. The 235 result retains
inspected contributor evidence, with complete independent rebuilding pending.
The optimum and 196 remain unresolved. Keep the full research goal active.

## Scheduled manuscript revision and runtime

Revision 106 is due next. Read the complete current paper before revising its
argument. Use ordinary notation, omit unnecessary definitions, and keep Lean
file names and implementation definitions out of the paper. Preserve authors
Iori Hironaka, Tommy Ma and Steven Zhan and the existing hypersetup settings.
Edit D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex in place, maintain
the exact E:/Snake-in-a-box/paper/snake9_research.tex mirror, and compile the
open source through the built-in compiler. The current revision is 96.

Python is C:/Users/hironakaiori/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe;
use -B -X utf8. Lean 4.19 and mathlib are under
D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research.
Reuse the existing support overlay. Prefer sequential compilation; do not
start another heavy job alongside the complete batch. Do not add -M4096.

Preserve exact bytes, receipts and unsuccessful attempts. Leave unrelated
.gitignore and milestones/50-three-count-return/excess-screen/data/critical-family.json
edits untouched. Fetch before publication, stage exact reviewed paths, verify
the staged bytes and push each completed round. Do not update old manifests
merely because newer handovers supersede their shared-file entries.
''')
print(c['status'],counts,'active batch; 5 checked implications; no new definitions')
