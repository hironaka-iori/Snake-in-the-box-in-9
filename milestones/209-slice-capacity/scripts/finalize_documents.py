"""Save the terminal round209 results and update the existing manuscripts."""
from pathlib import Path
import datetime,hashlib,json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1]
D=Path('D:/Codex/2026-10-13/new-chat/outputs')
assert not (H/'data/history-search.lock').exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,d):p.write_bytes((json.dumps(d,indent=2)+'\n').encode())
def replace(t,a,b):
 if t.count(a)!=1:raise RuntimeError(a[:100])
 return t.replace(a,b)
cases=[]
for i in [24,9,23]:
 f=H/'data'/f'case-{i}';s=json.loads((f/'state.json').read_bytes());m=json.loads((f/'model.json').read_bytes())
 assert s['status']=='OPEN','Revise the conclusions for the new terminal result.'
 totals={k:0 for k in ['capacity_removals','partner_removals','capacity_failures']}
 for rec in s['receipts']:
  out=json.loads((H/rec).with_name('stdout.json').read_bytes())
  for k in totals:totals[k]+=out.get(k,0)
 cases.append({'index':i,'base':m['base'],'status':s['status'],'committed_jobs':s['committed_jobs'],
  'pending':len(s['frontier']),'nodes':s['nodes'],'solver_seconds':s['seconds'],
  'state':f'data/case-{i}/state.json','state_sha256':sha(f/'state.json'),**totals})
proofs=[]
for name in ['Capacity209','Square209','ConcreteCapacity209']:
 p=H/'data'/(name+'-audit.json');a=json.loads(p.read_bytes());assert a['status']=='PASS'
 proofs.append({'module':name,'receipt':str(p.relative_to(H)),'sha256':sha(p),
  'source_sha256':a['source_sha256'],'olean_sha256':a['olean_sha256'],'reports':len(a['axioms'])})
completion={'round':209,'status':'PROGRESS','goal_state':'ACTIVE','pause_requested':False,
 'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'base_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
 'new_q9_record':False,'new_global_bound':False,'new_exhausted_coordinate_pairs':0,
 'accepted_lean_modules':len(proofs),'theorem_reports':sum(p['reports'] for p in proofs),'proofs':proofs,
 'cases':cases,'six_coordinate_total_exhausted':1,'six_coordinate_total_unresolved':27,
 'capacity_result':'Case23 fixed[0,5] even capacity12+10+10=32, forcing nine antipodal singleton word sharings.',
 'scope':'Written whole-path geometric argument; Lean checks square geometry, generic capacity consequences, and literal source-derived interval counts. Complete geometric-model assembly and concrete search certification remain pending.',
 'contributor_ref':'6eab58c4ead3acb19deb40e626cd66fd2bf101b1',
 'resources':{'startup_free_bytes':1024**3,'reserve_free_bytes':768*1024**2,'private_limit_bytes':256*1024**2},
 'next':'Whole-paper review at round210; then continue preserved open frontiers with unchanged engines.'}
save(H/'data/completion.json',completion)

section=r'''
\subsection{Square-base capacity and forced shared words}
\label{sec:capacity209}
Retain two coordinates and write each path vertex as $(z,u)$ with
$z\in Q_2$ and $u\in Q_r$, where $r\ge1$. Divide the path into maximal
intervals on which $u$ is constant. Their free-word parities alternate.
Two distinct intervals of the same parity have no consecutive pair
of original path indices.

\begin{proposition}[Square-base capacity]
For one free-word parity, let $M$ count intervals visiting more than
one base vertex and let $N_z$ count intervals visiting only $z\in Q_2$.
Then
\[
M+\max(N_{00},N_{11})+\max(N_{01},N_{10})\le 2^{r-1}.
\]
\end{proposition}
\begin{proof}
If two such intervals have the same free word, every base pair across
them must have distance at least two. A repeated base word would repeat
a full vertex, and base distance one would give a chord. Each square
vertex has a unique vertex at distance two, its opposite corner.
Nonempty visit sets with all cross pairs at distance two must therefore
both be singletons at opposite corners.

Every multi-visit interval consequently has a word distinct from every
other interval of its parity. Choose all of these intervals and the
larger singleton family from each opposite-corner pair. Their words
are pairwise distinct, and only $2^{r-1}$ words have the chosen parity.
\end{proof}

The displayed demand is exact for the equal-word conflicts within
one parity: pair singleton intervals across opposite corners as far
as possible, give each pair one word, and give separate words to the
unpaired and multi-visit intervals. Constraints between opposite
free-word parities still have to be satisfied.

For the saved 98-edge parent, retaining coordinates 0 and 5 gives
81 intervals. Among the even intervals the counts are
\[
M=12,\qquad (N_{00},N_{01},N_{10},N_{11})=(5,4,10,10).
\]
The 12 multi-visit intervals and the ten singleton intervals at each
of $10$ and $11$ therefore use all 32 even words of $Q_6$ exactly once.
Every singleton at $00$ must share its word with a singleton at $11$;
every singleton at $01$ must share with one at $10$. These give exactly
nine words used by two intervals, with no word used by three intervals.
The other 23 even words belong to one interval each. A multi-visit
interval may contain more than one full vertex with its word.
The shared partners are existential choices, not prescribed pairings.

This saturation has consequences within every unfinished branch.
Each even word must remain available in some selected clique domain.
If only one such domain contains it, that variable must take it.
An outside singleton domain may be intersected with the union of its
opposite-corner partners' domains. These follow from the requirement
that the 32 selected variables use all 32 words, and preserve every
completion of the original model.

Lean checks the square's opposite-corner property, generic finite
capacity and saturation deductions, and the unique-carrier and
partner-support implications. A separate kernel calculation derives
the 81 intervals, both parity count vectors, and the 32 selected
indices directly from the literal 99-vertex source. Three modules
pass with thirteen dependency reports~\cite{research209}. The complete
geometry-to-model assembly and native search remain separate proof
obligations.

The added deductions are active in a separately reviewed native
search. Retained pairs $(0,4)$, $(3,4)$ and $(0,5)$ all remain open.
The other 24 unresolved pairs retain only their initial limited
searches. The previously exhausted pair $(1,4)$ remains the sole
six-coordinate exclusion. No new parent or global $Q_9$ bound follows.

'''
mp=D/'snake9_research.tex';main=mp.read_bytes().decode()
main=replace(main,'finite exclusion certificate remains pending.\nNo longer',
'''finite exclusion certificate remains pending.
A square-base capacity inequality forces nine shared free words
at opposite singleton slices for one retained-coordinate pair.
Its geometric core, counting implications and source-derived
interval counts receive separate Lean checks.
No longer''')
main=replace(main,r'\section{Construction experiments and their scope}\label{app:experiments}',
 section+r'\section{Construction experiments and their scope}\label{app:experiments}')
main=replace(main,'''The searches retaining $(0,4)$ and $(3,4)$ have saved open frontiers;
the other 25 pairs retain only their initial limited searches.''',
'''At that checkpoint, the searches retaining $(0,4)$ and $(3,4)$ had
saved open frontiers; the other 25 pairs retained only their initial
limited searches.''')
bib=r'''\bibitem{research209}
I. Hironaka, T. Ma and S. Zhan, \emph{Square-base capacity and forced
shared words in coordinate-history searches}. Research record 209,
14 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/209-slice-capacity}.

'''
main=replace(main,r'\end{thebibliography}',bib+r'\end{thebibliography}')
mp.write_bytes(main.encode())
fp=D/'snake9_frontier_explanation.tex';front=fp.read_bytes().decode()
front=replace(front,'Research state after round 208','Research state after round 209')
old=r'''The pairs $(0,4)$ and $(3,4)$ have saved unfinished regions, and the
other 25 pairs remain unresolved after their initial limited searches.
Continuing these exact regions is the next step. A successful different
parent would still need a separate $Q_9$ joining construction.'''
new=r'''The pairs $(0,4)$ and $(3,4)$ still have saved unfinished regions.

A stronger geometric restriction arises from the two retained
coordinates. Split the path into constant-free-word intervals.
For distinct intervals of the same free-word parity, equal free
words force every base pair to have distance two. Otherwise a
vertex repeats or a chord appears. In a square each vertex has
only one opposite corner, so both intervals must visit singleton
base vertices at opposite corners.

For one parity, let $M$ count intervals visiting several base
vertices and $N_z$ those visiting only $z$. Choosing all multi-visit
intervals and the larger singleton family from each opposite pair
therefore gives distinct free words, proving
\[
M+\max(N_{00},N_{11})+\max(N_{01},N_{10})\le 2^{r-1}.
\]
For retained coordinates $(0,5)$ in the saved parent, the even
counts are $M=12$ and $(N_{00},N_{01},N_{10},N_{11})=(5,4,10,10)$.
The selected 32 intervals use every even word of $Q_6$.
Thus each of the five singleton intervals at $00$ shares a word
with one at $11$, and each of the four at $01$ shares with one at
$10$. Exactly nine words are shared by pairs of intervals.

In a branch, every even word must have a possible carrier in the
32 selected intervals. A sole possible carrier is forced. Each
outside singleton must also retain a word available to one of its
opposite-corner partners. These deductions strengthen the search
without prescribing which partner is chosen.

Three Lean modules pass with thirteen reports: the square geometry,
generic capacity and support implications, and extraction of the
81 intervals and counts directly from the literal source. The full
model assembly and native exclusion proof remain pending.
The strengthened $(0,5)$ search remains open, as do $(0,4)$ and
$(3,4)$. The other 24 unresolved pairs retain their initial limited
searches. No new parent or global bound has been obtained.
A successful different parent would still need a separate $Q_9$
joining construction.'''
front=replace(front,old,new);front=replace(front,'research records 175--208.','research records 175--209.')
fp.write_bytes(front.encode())
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
 (R/'paper'/name).write_bytes((D/name).read_bytes())
save(H/'data/document-identities.json',{name:{'editor_source':str(D/name),'repository_source':str(R/'paper'/name),'sha256':sha(D/name)} for name in ['snake9_research.tex','snake9_frontier_explanation.tex']})

rows='\n'.join(f"| {c['index']} | {c['base']} | {c['committed_jobs']} | {c['pending']} | {c['nodes']:,} | OPEN |" for c in cases)
handoff=f'''# Current state after round 209

The goal remains ACTIVE. The user instructed continued work until she requests a stop. Round209 is PROGRESS. No new Q9 witness, numerical bound or optimality proof. The value196 remains unresolved. Read milestones/209-slice-capacity/MATHEMATICAL_NOTE.md and data/completion.json first.

NEW MATHEMATICS: For same-parity constant-free-word intervals over a retained Q2, equal free words are possible only for singleton visits at antipodal base vertices. Thus M+max(N0,N3)+max(N1,N2)<=2^(r-1). For fixed coordinates[0,5], even countsM12,singles[5,4,10,10] saturate32. All32evenwords occur exactly once on the selected clique; nine outside variables must share words with antipodal singleton partners. This does not prescribe individual partners. Opposite-parity pair conditions remain essential.

LEAN: Three modules pass with13reports. Capacity209 checks finite injection, saturation, domain capacity, unique carriers and partner support. Square209 checks square antipodes and singleton visit sets under cross-separation. ConcreteCapacity209 derives81intervals, even[12,5,4,10,10], odd[6,9,9,8,8] and the32selected indices directly from the literal99source. Complete actual-path/model assembly and native search certificates remain pending. Accepted source, receipts and objects are immutable.

SEARCH SNAPSHOT:

| Case | Retained coordinates | Committed jobs | Pending | Nodes | Status |
|---|---|---:|---:|---:|---|
{rows}

Cases24/9 use the unchanged208engine; each inherits100steps and adds50. An independent audit confirmed all1200inherited run files, checkpoint bytes and100new transitions. Case23 uses the separately reviewed capacity engine with required-word support, unique-carrier forcing and partner-domain unions. Its source rules were validated against the original binary tables on initialization. It remains a native calculation. No general matching algorithm is implemented or benchmark speedup established.

PRESERVED FRONTIER: Only case18 fixed[1,4] is excluded among28six-coordinate models (round208). All56five-coordinate models exhaust natively, so a different class requires at least SIX changed histories at the same length and index matching. There is no general seven-history result. Twenty-four pairs retain only initial limited searches. Earlier round205geometric bridges remain pending.

NEXT: Round210 is due for the whole-paper review (previous200). Then continue the open exact frontiers. Freeze209bytes. In a new milestone copy unchanged original engine scripts/binary/input and complete cases24/9; copy capacity_continue.py, capacity_solver.c, capacity_solver.exe, square-capacity.json and completecase23 too. Maintain relative paths and exact engine/model pins. Use original continue_search.py for24/9 and capacity_continue.py for23, sequentially. The engine roots follow their file locations. Do not regenerate or alter pinned files, and do not mix the two engines' states. A changed engine needs an explicitly justified transfer.

RESOURCES: One heavy worker. Search/Lean startup>=1GiBfree, reserve>=768MiB, privatebytes<=256MiB. Lean60s,-j1 -s8192. Bounded55s startup wait retains thresholds. No Python-O; data/python-configuration.json records optimization0, assertions enabled, noPYTHONOPTIMIZE. Single coordinator; manual per-job STOP does not promise batch cancellation. Process recovery is supported; fullpower-loss durability is unproved. No software tests.

CONTRIBUTOR: Refreshed origin/research/unconditional-241 at6eab58c4ead3acb19deb40e626cd66fd2bf101b1 adds two production receipts. No merged or independently rebuilt global bound. Last explicitly read total remains3120/3127 at09:55UTC14November; do not infer an updatedtotal from individual logs. Archived235rebuild pending;233/234conditional.

DOCUMENTS: Existing D:/Codex/2026-10-13/new-chat/outputs originals mirroredbyte-for-byte toE:/Snake-in-a-box/paper. Preserve authors andhypersetup. Compile frontier first/mainlast, read current receipts. Exact publicationmanifest limits scope. Preserve .gitignore, milestone50critical-family.json and unrelateduntrackedfiles; avoid unfilteredgitstatus. No current pause request.
'''
for name in ['CURRENT_STATUS.md','NEXT_AGENT_PROMPT.md']:(R/'handoff'/name).write_bytes(handoff.encode())
lead='''# Current result after round 209

Square-base geometry gives a capacity inequality for whole coordinate histories. The retained pair[0,5] saturates the32even-word capacity, forcing nine shared words at opposite singleton slices. Three Lean modules pass with13reports, covering the geometric core, capacity/support implications and source-derived interval counts. The full model and native exclusions remain separate.

The strengthened search and continued pairs[0,4],[3,4] remain open. No new Q9 witness or global bound. The goal remains active.

Read [the argument](milestones/209-slice-capacity/MATHEMATICAL_NOTE.md), [completion and current states](milestones/209-slice-capacity/data/completion.json), [independent geometric review](milestones/209-slice-capacity/logs/capacity-review.md), [handoff](handoff/CURRENT_STATUS.md) and [frontier explanation](paper/snake9_frontier_explanation.tex).

## Earlier checkpoints

'''
readme=R/'README.md';readme.write_bytes(lead.encode()+readme.read_bytes())
(H/'README.md').write_text('''# Round209

The square-base capacity bound forces nine antipodal singleton word sharings in the retained[0,5] model. Three Lean modules pass with13reports. The strengthened native search remains open; no new global bound or witness follows.

- [Mathematical argument](MATHEMATICAL_NOTE.md)
- [Current states and verification](data/completion.json)
- [Independent geometric review](logs/capacity-review.md)
- [Capacity implementation review](logs/capacity-implementation-review.md)
- [Inherited and continued chain audit](logs/continued-chains-review.md)
- [Compilation receipts](data/latex-compilation.json)

The goal remains active. Preserve accepted bytes and resume from copies in a new milestone. Round210 is due for the whole-paper review.
''',encoding='utf-8')
pub=H/'scripts/publication.py';pub.write_bytes(pub.read_bytes().replace(b'Round208 research artifacts',b'Round209 research artifacts'))
print(json.dumps(completion,indent=2))
