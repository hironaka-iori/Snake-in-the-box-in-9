"""Save this round's proofs, native cutoff, and updated manuscript sources."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1]
D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,s):p.write_text(s.strip()+'\n',encoding='utf-8',newline='\n')
def save(p,x):write(p,json.dumps(x,indent=2))
state=json.loads((H/'data/case-23/state.json').read_bytes())
assert state['committed_jobs']==296 and len(state['frontier'])==11 and state['status']=='OPEN'
assert not (H/'data/history-search.lock').exists()
newreceipts=state['receipts'][100:]
totals={k:0 for k in ['nodes','seconds','subset_calls','subset_removals','subset_failures','tight_sets']}
statuses={}
for name in newreceipts:
 p=H/name;r=json.loads(p.read_bytes());o=json.loads((p.parent/'stdout.json').read_bytes())
 assert r['status']=='ACCEPTED_TRANSITION' and sha(p.parent/'stdout.json')==r['stdout_sha256']
 statuses[o['status']]=statuses.get(o['status'],0)+1
 for k in totals:totals[k]+=o[k]
proofs=[]
for name in ['Subset211','Spare211','Sharing211','ConcreteSpare47','ConcreteSpare06','ConcreteSpare06Odd']:
 p=H/'data'/f'{name}-audit.json';d=json.loads(p.read_bytes())
 assert d['status']=='PASS' and d['exit_code']==0 and d['stop_reason'] is None
 assert sha(Path(d['source']))==d['source_sha256'] and sha(Path(d['object']))==d['olean_sha256']
 assert sha(Path(d['log']))==d['log_sha256']
 for path,digest in d['dependencies'].items():assert sha(Path(path))==digest
 proofs.append({'module':name,'receipt':str(p.relative_to(H)),'sha256':sha(p),'reports':len(d['axioms'])})

main=(D/'snake9_research.tex').read_text(encoding='utf-8')
front=(D/'snake9_frontier_explanation.tex').read_text(encoding='utf-8')
spare=r'''
\paragraph{Outside sharing when words remain unused.}
The same square geometry gives an aggregate condition without full
saturation. Choose the larger singleton family at each antipodal pair
and all multi-visit intervals. The remaining singleton intervals occupy
at most two adjacent corners. Their free words are pairwise distinct:
equal words would repeat a vertex at one corner or create a chord
between the two corners.

Let $C$ be the words assigned to the chosen family and $O$ those assigned
to the outside intervals of that parity. If the alphabet has size $q$,
then $C$ and $O\setminus C$ are disjoint subsets of it, so
\[
|C|+|O\setminus C|\le q,\qquad
|C\cap O|\ge |C|+|O|-q.
\]
Thus at most $q-|C|$ outside intervals avoid sharing with the chosen
family. Every shared word still requires an antipodal singleton partner.
For the literal source, the checked counts give
\[
\begin{array}{c|c|r|r|r}
\text{retained coordinates}&\text{parity}&|C|&|O|&
\text{required shared words}\\\hline
(4,7)&\text{even}&31&2&\ge1\\
(0,6)&\text{even}&30&9&\ge7\\
(0,6)&\text{odd}&26&13&\ge7
\end{array}
\]
Here $q=32$. These are aggregate requirements; no particular outside
interval is forced to share by the counts alone. Lean checks the
finite-list inequality, its shared-word consequence and the source-derived
counts separately. The whole-path interpretation has the written argument
above; its complete Lean assembly remains pending. The corresponding
unsaturated-family search rules are not implemented in this round.

'''
anchor=r'\paragraph{Finding the subsets.}'
assert main.count(anchor)==1
main=main.replace(anchor,spare+anchor,1)
status=r'''At the round-211 cutoff, retained pair $(0,5)$ remains open with
11 unfinished regions. The new engine adds 196 accepted continuation
steps and 1,038,016 nodes; including round 209, this case has 296 steps
and 3,721,372 nodes. The last run retained its pending regions and exited
normally after the resource monitor requested a memory stop. The 196
new state transitions were independently audited. The number of unresolved
six-coordinate pairs remains 27~\cite{research211}.'''
main=main.replace('% ROUND211_SEARCH_STATUS',status)
front=front.replace('% ROUND211_SEARCH_STATUS',r'''The $(0,5)$ case remains open after 196 new continuation steps,
with 11 unfinished regions and 3,721,372 cumulative nodes. The latest
resource stop retained its pending regions. The other 26 unresolved
six-coordinate cases were unchanged in this round.

\paragraph{When the chosen family leaves spare words.}
The outside singleton intervals themselves require distinct words:
their base corners are either equal or adjacent. Let $C$ and $O$
be the word sets assigned to the chosen and outside families of one
parity. Both lie in an alphabet of 32 words, hence
\[
|C|+|O\setminus C|\le32,\qquad
|C\cap O|\ge |C|+|O|-32.
\]
The first inequality counts two disjoint word sets; the second follows
by splitting $O$ into its shared and unshared words. Consequently,
for retained pair $(4,7)$ at least one of its two even outside intervals
must share. For $(0,6)$ at least seven of nine even outside intervals,
and seven of thirteen odd outside intervals, must share with antipodal
partners. Which intervals share remains undetermined.

Lean checks the counting implications and the literal source counts.
The complete geometric assembly remains a written proof. These
unsaturated-family constraints are a next search direction; their
implementation is still pending.
''')
for name,s in [('snake9_research.tex',main),('snake9_frontier_explanation.tex',front)]:
 write(D/name,s);(R/'paper'/name).write_bytes((D/name).read_bytes())
save(H/'data/document-identities.json',{name:{'editor_source':str(D/name),'repository_source':str(R/'paper'/name),'sha256':sha(D/name)} for name in ['snake9_research.tex','snake9_frontier_explanation.tex']})

note=r'''
# Round 211: subset capacity and forced sharing

The working hypothesis was that joint distinct-word constraints remove combinations that survive separate binary supports. The new native engine records active subset pruning, but no controlled comparison establishes a speed improvement. The six-coordinate case retaining [0,5] remains open. No new Q9 construction or global upper bound is claimed.

## The proved deductions

If a subset J of variables must receive distinct words, and U is the union of their allowed words, every completion gives an injection J into U. Thus |U| < |J| is impossible. Equality means all U is used within J; every other variable known unequal to every member of J must avoid U. Removing those words preserves the same complete assignment and all its other constraints.

The 32-variable family for retained coordinates [0,5] is saturated. A matching discovers tight subsets through reachability: direct an arc from a variable to the matched owner of each allowed word. A reached set is closed, so its domain union is precisely its matched words. The implementation recomputes the actual union and cardinality before every rejection or deletion. Matching failure without a genuine deficient subset is an execution error, not an exclusion. Only other clique variables are pruned; outside singleton intervals retain their possible partner sharing. This is an application of standard matching methods, not a novelty claim. The primary precedent inspected is Jean-Charles Regin, AAAI-94, https://cdn.aaai.org/AAAI/1994/AAAI94-055.pdf (abstract and matching characterization).

## A further whole-path consequence

For one parity, choose all multi-visit intervals and the larger singleton family from each antipodal pair of the retained-coordinate square. All outside intervals then lie at at most two adjacent corners. Their words must also be pairwise distinct: equal words would repeat a vertex or create a chord. If C and O are the assigned word sets of the chosen and outside families, both fit in 32 words. Therefore

\[
|C|+|O\setminus C|\le32,\qquad |C\cap O|\ge|C|+|O|-32.
\]

At most the unused capacity of C can be occupied by outside intervals without a partner in C. Every shared word must have an antipodal singleton partner, by the square geometry.

| Retained pair | Parity | Chosen intervals | Outside intervals | Minimum partner sharing |
|---|---|---:|---:|---:|
| [4,7] | Even | 31 | 2 | 1 |
| [0,6] | Even | 30 | 9 | 7 |
| [0,6] | Odd | 26 | 13 | 7 |

These are aggregate requirements and do not identify particular partners or particular outside intervals that must share. In particular, one cannot remove all unpartnered values from every outside interval when spare words remain. If several outside intervals have no possible partner support, they consume that limited spare capacity. Developing this aggregate constraint is the next useful search step.

The alternate reachability description handles unsaturated matching families directly: reached words minus reached variables equals the number of reachable unmatched words. Only closures with no reachable unmatched word are tight. The detailed written argument and all 56 parity-family capacity counts are in logs/unsaturated-extension.md. This extension is not yet implemented.

## Verification and search scope

Six new Lean modules pass with nineteen theorem dependency reports. Subset211 checks four subset-capacity implications. Spare211 and Sharing211 check unused capacity and forced sharing. Three concrete modules derive the selected even/odd counts directly from the literal 99 source vertices. Their accepted sources, objects and dependency receipts are preserved. The generic counting implications and literal extraction do not themselves assemble the complete arbitrary-path/model interpretation or certify the native traversal. The whole-path link has the written geometric proof above. The failed first Sharing211 compilation and its corrected successful receipt are both retained.

The native source review found no unsound subset rule under the inherited clique assumptions. The fixed transfer audit verifies all 606 inherited files, all seven domain vectors, their order and model pins. The transfer changes only engine pins and adds its explicit record. No frozen round-209 evidence is modified.

The new search accepted 196 transitions: 170 exhausted subtrees and 26 limited runs, adding 1,038,016 nodes and 115.378 solver seconds. It records 5,022,135 subset value removals and 84,079 subset contradiction returns. These count repeated operations across branches, not distinct globally excluded assignments. The complete model remains OPEN with eleven pending regions; totals including the old engine are 296 jobs, 3,721,372 nodes and 361.033 solver seconds.

The last job exited normally after LOW_FREE_MEMORY was recorded and retained nine new regions; two older regions were unchanged. Its elapsed time also met the ordinary job limit, so the exact internal stopping condition is not inferred. The independent saved-record audit reconstructs every new state transition and final byte sequence. It does not replace a Lean traversal certificate.

The earlier open [0,4] and [3,4] cases remain at their round-209 states. Only [1,4] is excluded among all 28 six-history choices; twenty-seven remain unresolved. The general source-specific requirement remains six changed histories at the same length and fixed index matching.

## Publication and continuation

The main paper and short explanation are updated in place, preserving authors and local hyperlink settings, with exact repository mirrors. The contributor branch advanced to c999e9bd at its 13:03 UTC report: 3125/3127 built, leaving S012301A35344 and T012304A35346K47. The former was retried after a kernel reduction failure and the latter after stack overflow; the report supplies no completed 233 assembly. This progress was inspected, not merged or independently rebuilt. The archived 235 theorem and conditional 233/234 status are unchanged.

The goal is ACTIVE after the user's explicit resume. Continue from the frozen round-211 [0,5] state, or implement the spare-capacity constraints for [0,6] in a new milestone with its own model and proof boundary. Search and proof checks retain the existing resource limits. No software tests were created or run.
'''
write(H/'MATHEMATICAL_NOTE.md',note)
handoff=r'''
# Current state after round 211

The user explicitly resumed the goal after round210. The goal is ACTIVE; no current pause request exists. Round211 is PROGRESS. No new Q9 witness, global numerical bound or complete six-coordinate exclusion was obtained. The value196 remains unresolved.

Read milestones/211-subset-capacity/MATHEMATICAL_NOTE.md, data/completion.json and logs/subset-chain-review.md. Six new Lean modules pass with nineteen reports: four subset-capacity implications, unused-capacity and forced-sharing deductions, and literal interval counts. Full geometric-model assembly and native traversal certification remain pending.

New whole-path restriction: the outside singleton intervals of a selected square-base family are themselves pairwise unequal. If C and O are the chosen and outside word sets in a parity alphabet of32 words, then |C|+|O\C|<=32. Thus [4,7] even requires at least1 of2 outside intervals to share with antipodal partners; [0,6] even requires at least7 of9 and odd at least7 of13. The aggregate condition does not prescribe partners or let every outside interval lose all unpartnered values. Unsaturated matching/spare-capacity rules are the recommended next development; they have not been implemented.

## Frozen search states

| Case | Retained pair | Location | Jobs | Pending | Nodes | Status |
|---|---|---|---:|---:|---:|---|
|23|[0,5]|milestones/211-subset-capacity/data/case-23|296|11|3,721,372|OPEN|
|24|[0,4]|milestones/209-slice-capacity/data/case-24|150|8|9,625,900|OPEN|
|9|[3,4]|milestones/209-slice-capacity/data/case-9|150|3|8,142,891|OPEN|

Round211 adds196 accepted transitions, 1,038,016 nodes and115.378 solver seconds. The separately compiled subset engine uses matching to find tight/deficient sets and recomputes actual unions before pruning. The six hundred six inherited files and exact seven-region transfer were independently audited. The196 new transitions also reconstruct exactly. Five million recorded subset deletions are repeated operations, without a measured speedup. The last job saved coverage and exited normally after a memory-stop request; no worker is active. Sessions64900,67658 and22497 are terminal. The case remains open; only [1,4] is excluded among28 six-coordinate choices, leaving27 unresolved. All70 four-coordinate and56 five-coordinate models were previously exhausted natively, giving only the source-specific six-history requirement.

## Continue without changing evidence

To continue [0,5], copy its complete round211 case directory, scripts/capacity_continue.py, capacity_solver.c, history_model.py, native_resources.py, build/capacity_solver.exe, data/lower-dimensional-input.json and square-capacity.json to a new milestone with identical relative paths. Maintain exact engine/model pins. Existing runner requires an explicit transferred/copied state and will not regenerate a root model. Preserve the complete receipt prefix and transfer record. A changed engine requires a justified new transfer. For [0,4]/[3,4], retain the separate original runner and engine from round209; do not mix states. All accepted proof/source/object receipts are immutable.

Keep one heavy worker. Startup requires >=1GiB free, reserve >=768MiB, private bytes <=256MiB. Lean uses60s, -j1 -s8192. The55s startup wait does not lower thresholds. Assertions stay enabled; no Python -O or PYTHONOPTIMIZE. One coordinator owns continuation. Per-job STOP is not whole-batch cancellation; full power-loss durability is unproved. Do not create/run software tests unless asked.

The completed archived235 theorem has a successful saved audit but its full independent rebuild is pending.233/234 remain conditional. Latest inspected contributor revision c999e9bd reports3125/3127 built at13:03UTC, with S012301A35344 and T012304A35346K47 still pending. No merge or independent rebuild was performed. Do not conflate its catalogue with either retained graph or accepted-key package.

Editor originals remain D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and snake9_frontier_explanation.tex, with exact mirrors under E:/Snake-in-a-box/paper. Preserve authors and hypersetup; compile frontier first and main last. Current receipts belong in milestone211/data. Last full-paper review210; next scheduled220. Preserve unrelated .gitignore, milestone50 critical-family.json and pre-existing untracked files. Use narrowly scoped exact publication and avoid unfiltered git status.
'''
write(R/'handoff/CURRENT_STATUS.md',handoff);write(R/'handoff/NEXT_AGENT_PROMPT.md',handoff)
readme='''# Current result after round 211

Subset capacity is now proved and used in the open six-coordinate search. Six Lean modules pass with nineteen reports, covering the generic counting deductions and concrete source counts. A further consequence forces at least seven outside intervals to share with antipodal partners in each parity for retained coordinates [0,6]; its unsaturated-family search implementation remains pending.

The [0,5] continuation adds196 accepted steps and1,038,016 nodes, retaining11 unfinished regions after a safe resource stop. It remains open. No new Q9 witness or global bound is claimed. The goal is ACTIVE after the user's resume.

Read [the mathematical argument](milestones/211-subset-capacity/MATHEMATICAL_NOTE.md), [proofs and cutoff](milestones/211-subset-capacity/data/completion.json), [native chain audit](milestones/211-subset-capacity/logs/subset-chain-review.md), [handoff](handoff/CURRENT_STATUS.md) and [frontier explanation](paper/snake9_frontier_explanation.tex).

## Earlier checkpoints

'''
prior=(R/'README.md').read_text(encoding='utf-8')
if not prior.startswith('# Current result after round 211'):write(R/'README.md',readme+prior)
save(H/'data/completion.json',{'round':211,'status':'PROGRESS','goal_state':'ACTIVE','pause_requested':False,
 'started_utc':'2026-11-14T13:28:20+00:00','utc':datetime.now(timezone.utc).isoformat(),
 'new_q9_record':False,'new_global_bound':False,'new_six_coordinate_exclusions':0,
 'accepted_lean_modules':len(proofs),'theorem_reports':sum(p['reports'] for p in proofs),'proofs':proofs,
 'case23':{'status':state['status'],'jobs':state['committed_jobs'],'pending':len(state['frontier']),'nodes':state['nodes'],'seconds':state['seconds'],'state_sha256':sha(H/'data/case-23/state.json')},
 'new_transitions':len(newreceipts),'new_results':statuses,'new_operation_totals':totals,
 'six_coordinate_unresolved':27,'other_active_states':'milestones/209-slice-capacity/data/completion.json',
 'stopped_sessions':[64900,67658,22497],'native_stop':'RESOURCE_STOP; terminal exit0, retained11regions',
 'software_tests_created_or_run':False,'complete_native_certificate':False,
 'new_general_consequence':'At most the spare parity capacity can be used by outside intervals without an antipodal chosen-family partner.',
 'next_step':'Implement aggregate spare-word restrictions for [0,6] and/or continue frozen [0,5]; retain proof and search scope.'})
write(H/'README.md','''# Round211: subset capacity and forced sharing

Six Lean modules pass with19 reports. Subset capacity drives a new native continuation engine; a further unused-word argument forces partner sharing in unsaturated families. No Q9 witness or global bound is improved.

- [Mathematical note](MATHEMATICAL_NOTE.md)
- [Completion and search cutoff](data/completion.json)
- [Subset source review](logs/subset-engine-review.md)
- [Exact transfer audit](logs/frontier-transfer-review.md)
- [New native receipt-chain audit](logs/subset-chain-review.md)
- [Unsaturated families](logs/unsaturated-extension.md)
- [Spare-word deduction](logs/spare-word-proof.md)

All frozen prior records remain unchanged. Native search and complete geometric assembly retain their explicit limitations. No software tests were run. The goal remains active.
''')
save(H/'data/source-refresh.json',{'contributor_revision':subprocess.check_output(['git','rev-parse','origin/research/unconditional-241'],cwd=R,text=True).strip(),'report':'13:03UTC,3125/3127built;two pending;not merged or independently rebuilt','pending':['S012301A35344','T012304A35346K47'],'primary_precedent':'https://cdn.aaai.org/AAAI/1994/AAAI94-055.pdf','scope':'Read abstract and matching characterization; standard all-different filtering precedent. No novel matching algorithm claimed.'})
print(json.dumps({'proof_modules':len(proofs),'reports':sum(p['reports'] for p in proofs),'new_steps':len(newreceipts),'totals':totals,'status':'OPEN'},indent=2))
