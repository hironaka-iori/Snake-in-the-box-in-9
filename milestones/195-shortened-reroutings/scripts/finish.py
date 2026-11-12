from pathlib import Path
import datetime,hashlib,json,re,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def read(name):return json.loads((H/'data'/name).read_bytes())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def prose(s):
 return re.sub(r'\b(the|a|an|two|three|one|with|of|for|and|in|at|all|through|contains|using|use|has|have|by|after|from|before|to|on|over|occupy|give|gives|produce|produces|target|record|records|Round|round|coordinates|coordinate|components|case|pairs|dimension|corresponding|observed|balanced|saved|known|remains|is|or|than|both|Four|Two)(?=\d)',r'\1 ',s)
modules=['QuotientLift195','Symmetry195']+[f'SymmetryEdges195_{i}' for i in range(8)]+['QuotientPorts195']
accepted=[]
for name in modules:
 d=read(name+'-audit.json');assert d['status']=='PASS' and d['exit_code']==0 and d['stop_reason'] is None
 for p,h in d['dependencies'].items():assert sha(p)==h
 for key,digest in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(d[key])==d[digest]
 accepted.append(dict(module=name,reports=len(d['axioms']),receipt_sha256=sha(H/'data'/(name+'-audit.json'))))
searches={name:read(name+'.json') for name in ['quotient50','affine50-omit4','lower-four98','bank-four192','lower-four98-fixed','bank-four191-fixed']}
assert all(searches[n]['status']=='UNKNOWN' and not searches[n]['witness'] for n in ['quotient50','affine50-omit4','lower-four98','bank-four192'])
assert all(searches[n]['status']=='OPTIMAL' and searches[n]['witness'] for n in ['lower-four98-fixed','bank-four191-fixed'])
for name,d in searches.items():assert sha(H/'data'/(name+'.pbtxt'))==d['model_sha256']
sym=read('symmetric-lift.json');assert sym['maximum_joined_edges']==42 and sym['commuting_isometries']==1536
short=read('closure8.json');assert short['status']=='RESOURCE_LIMIT' and short['witness'] is None
assert short['script_sha256']==sha(H/'data/closure8-source.py.txt')
comparison=read('symmetry-comparison.json');assert len(comparison['candidates'])==20 and not comparison['matches']
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
def rev(ref):return subprocess.check_output(git+['rev-parse',ref],cwd=R,text=True).strip()
summary=dict(round=195,status='PROGRESS',goal_status='active',previous_turn_classification='PROGRESS: round194 results and pause handoff published; explicit user resumption now applies',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 base_head=rev('HEAD'),contributor_head=rev('origin/research/unconditional-241'),accepted_modules=accepted,
 dimensional_pattern='Q8 two25-edge components are exchanged by one coordinate transposition and three fixed coordinate flips; use two-path faces and four crossings for Q9.',
 restricted_symmetric_join_maximum=42,paired_forest_vertices=86,balanced47_symmetry_maps=20,
 searches={n:dict(status=d['status'],seconds=d['seconds'],witness=bool(d['witness'])) for n,d in searches.items()},
 interrupted_short_state_search=dict(status=short['status'],completed_states=len(short['completed_states']),discovered_states=len(short['states']),counts_by_edges=short['counts_by_edges'],complete_closure=False),
 new_q9_record=False,new_global_bound=False,next_direction='Use the observed47-edge paired-forest involution and safe quotient edges. Replace the expensive flow formulation by a degree relaxation with sound cycle exclusions; retain the full quotient contact graph and forbid both endpoints of double-lift edges. Continue towards a100-vertex two-path face and a compatible95-vertex opposite face for194 edges.',
 scope='Lean checks generic lifting and the distance-three involution properties. Native restricted enumeration and model witnesses remain separate. All UNKNOWN outcomes are unresolved. The affine omission limit counts quotient orbits, equivalently at most8 omitted vertices from the96-vertex paired forest, not at most4 per labelled path.')
(H/'data/completion.json').write_text(json.dumps(summary,indent=2)+'\n')
(H/'data/review.json').write_text(json.dumps(dict(reviewer='exchange191_review',mode='Read-only source and mathematical review; no computations or edits',findings=['No soundness flaw found in the restricted max42 enumeration, quotient models, four-port contraction, or Lean statements.','The affine omission constraint counts quotient orbits;4 omitted orbits permit8 omitted vertices from the paired forest.','Bad quotient edges require forbidding both endpoints; deleting the edge alone would conceal cross-path chords.','Fixed face inputs must actually be two paths, not a degree-two graph with extra cycles. The fixed reconstructions decode and validate complete snakes.','The20 labelled isometries are not a classification of all symmetries. UNKNOWN gives no exclusion.']),indent=2)+'\n')
note=r'''# Round 195: dimensional patterns and symmetric path forests

The construction goal remains active. The user redirected this round towards patterns in the 6-to-7 and 7-to-8 constructions. No new Q9 record or upper bound was obtained. The new useful result is a precise construction family and its checked lifting argument.

## What transfers between dimensions

The displayed Q7 snake has the decomposition 18+24+6+2=50. The prior comparison showed that its24-edge Q6 middle is more useful than the displayed optimal26-edge middle, whose best compatible two-crossing lift has48 edges. Compatibility must be optimized jointly.

The displayed Q8 snake has the decomposition 8+25+10+25+26+4=98. One face contains two25-edge paths, hence52 vertices; the opposite face contains three paths with47 vertices. A single longest Q7 snake has51 vertices, so allowing two components increases the useful face occupancy.

For Q9, use two nonadjacent paths in one Q8 face and three in the other. The vertex sets A and B must intersect exactly in four crossing ports. All four ports are endpoints of the two A paths, and have B-degree at most one. The graph joining the five face components through the four ports must be connected. Then all full-graph degrees are at most two and the edge count is (|A|-2)+(|B|-3)+4=|A|+|B|-1; connectivity forces one induced path. Equivalently, the B components contain1,2,1 ports, with the two-port component joining different A components. Singleton outer B paths are allowed. Connectivity cannot be omitted: a cycle plus a path can satisfy the degree and edge counts.

A useful provisional target is two49-edge A paths, using100 vertices, together with95 compatible B vertices. This would give194 edges. A97-vertex B forest would give196. These are construction targets, with neither existence nor optimality established. Base Hamming parity reverses in the other face: the full colour difference is the A difference minus the B difference. Two49-edge A paths are balanced; a194-edge construction therefore needs B colour difference plus or minus one.

## The observed symmetry

With coordinate indices0 through6, the two25-edge Q7 components are exchanged by g(x)=sigma(x) xor73, where sigma swaps coordinates2 and5, and73 flips coordinates0,3 and6. This is an involution. Its paired vertices have Hamming distance3 or5. Extend g to Q8 by leaving coordinate7 unchanged.

Identify each vertex with its partner under g. The resulting graphs have64 vertices in the first case and128 in the extension; adjacency means that at least one cube edge joins the two pairs. The128-vertex graph is the Cartesian product of the64-vertex graph and one binary edge.

An induced path in this quotient lifts to two disjoint nonadjacent induced paths in Q8. Choose the first representative; each step then has a unique neighbouring representative. Uniqueness follows because two representatives of one orbit have distance at least three and therefore cannot share a cube neighbour. Distinct quotient vertices prevent intersection of the two lifted paths. A contact between nonconsecutive lifted vertices would project to a quotient chord. A contact between consecutive vertices of different lifts would give two possible lifts of one edge, already excluded. Contacts within one orbit are excluded by the same distance condition.

Lean checks the generic path-lifting and separation implications, transport under an involution, and all256 values of this specific involution. Eight further chunks check every cube-neighbour image and the absence of common cube neighbours of paired vertices. These proofs do not certify the numerical search census or the complete solver encoding.

## Restricted construction and the Q9 comparison

All1536 specified commuting isometries were used to place a second copy of the observed25-edge quotient path. All choices of one contiguous subpath in each face, with one crossing, were considered. The maximum within this family is42 edges. The corresponding Q8 pair has two43-vertex paths,86 vertices total, and was independently checked for all pairwise adjacencies and cross-contacts. This is a restricted native maximum, not the unrestricted quotient optimum.

Among the36 distinct labelled four-crossing fixed forests extracted from the saved Q9 bank, one uses98 vertices and35 use96. Twenty transition-determined isometries exchange balanced47-edge component pairs. Seventeen use two coordinate transpositions and two fixed coordinate flips; three use three transpositions and two fixed flips. None belongs to the directly matched one-transposition, three-fixed-flip class of the Q8 example. This is a comparison of the enumerated labelled maps, not a classification of all forest symmetries.

The first observed47-edge pair has an involution with minimum partner distance two. Some quotient edges then lift to a square. Such an edge cannot be used in a pair of nonadjacent paths, and selecting its two quotient endpoints is forbidden. It is insufficient merely to delete the quotient edge, since that would hide a real cross-path contact. A second Lean separation lemma requires uniqueness only on the chosen consecutive steps, covering this more general construction principle under explicit premises.

## Computations and limitations

The connected-flow quotient search for50 vertices under the extended Q8-example symmetry remained UNKNOWN after120 seconds. The query using the first saved47-edge pair, seeking50 quotient vertices with at most four omitted original orbits and one fixed endpoint, remained UNKNOWN after90 seconds. Four omitted orbits mean at most eight omitted vertices from the96-vertex paired forest; they do not bound omissions from each individually labelled component by four.

The four-crossing completion with the98-vertex fixed bank face and target192 edges remained UNKNOWN after120 seconds. The variable opposite-face lower-dimensional query targeting98 also remained UNKNOWN after30 seconds. With both face selections fixed to the known examples, the same contraction-and-flow model reconstructs the98-edge Q8 and191-edge Q9 snakes, and both decoded paths pass all-pairs checks. These reconstructions establish feasibility of the stated patterns. They do not establish an optimum or resolve the larger queries.

The earlier short-state search stopped at the768MiB free-memory reserve after completing six states and discovering238 states. It established no complete closure and found no longer witness. Its exact source is preserved. The source's overly frequent resource sampling was corrected afterwards without rerunning that branch; all incomplete coverage remains unresolved.

## Next step

Continue from the observed47-edge paired forest, using its safe quotient edges. Replace the expensive connectivity-flow search by the induced-degree relaxation and exclude disconnected cycles when they appear; each such exclusion is sound because a cycle cannot be a selected subset of an induced path. Keep an explicit omitted-orbit bound initially, then widen it if the restricted query is excluded. A valid50-vertex quotient path would give a100-vertex two-path face; its remaining three-path completion must still be solved. The separate four-crossing completion can vary the ports and fixed face instead of repeating the unchanged timeout.

There is no novelty claim for quotient lifting, graph contraction, or path-forest gluing. The specific observed symmetries and their usefulness for this construction are the research findings of this round. The archived235 upper-bound rebuild and conditional233/234 dependencies are unchanged. The next whole-manuscript review remains round200.
'''
(H/'MATHEMATICAL_NOTE.md').write_text(prose(note))
(H/'README.md').write_text('''# Round 195: dimensional patterns and paired paths

Read [the mathematical note](MATHEMATICAL_NOTE.md) and [completion record](data/completion.json). The main result is a checked quotient-lifting principle motivated by the two25-edge components in the98-edge Q8 construction, together with a comparison to symmetric47-edge components in the Q9 bank.

The restricted one-crossing quotient construction reaches42 edges. The larger searches remain UNKNOWN. Known98- and191-edge patterns are reconstructed with selected face vertices fixed. No new record or global bound follows.

The model archive restores raw solver inputs to data/. The source of the interrupted short-state search is preserved separately. Research remains active; the next route is the47-edge paired-forest quotient with explicit forbidden double edges and cycle exclusions.
''')
section=r'''
\subsection{Dimensional transfer through two-path faces}
\label{sec:forests195}

The comparison $18+24+6+2=50$ shows that compatible components can
outperform a lift built around a longer middle path. The next transition
has a different useful feature:
\[
98=8+25+10+25+26+4.
\]
Two of the five projected components occupy one face and contain
$2(25+1)=52$ vertices, exceeding the51 vertices of a longest single
$Q_7$ snake. The other face contains47 vertices in three components.
This motivates a four-crossing construction in $Q_9$.

\begin{proposition}[Joining two path forests]
Let $Q_n[A]$ consist of two nontrivial paths and $Q_n[B]$ of three
paths. Suppose $A\cap B$ consists of four vertices, each an endpoint
of its $A$ component and of degree at most one in $Q_n[B]$.
If the incidence multigraph on the five components, with one edge
for each common vertex, is connected, then
$A\times\{0\}\cup B\times\{1\}$ induces a path in $Q_{n+1}$
of length $|A|+|B|-1$.
\end{proposition}
\begin{proof}
All selected degrees are at most two. The number of selected edges is
\[
(|A|-2)+(|B|-3)+4=|A|+|B|-1.
\]
The incidence condition gives connectivity. A connected finite graph
of maximum degree two with one fewer edge than vertices is a path.
Every possible cube edge has been included: within faces by the
induced-forest hypotheses, and between faces exactly at $A\cap B$.
\end{proof}
The opposite-face components must contain one, two and one ports,
with the two-port component connecting different $A$ components.
Singleton outer components are allowed. Without connectivity, a
cycle and a separate path may satisfy the same degree counts.

\paragraph{A symmetry visible in the lower-dimensional construction.}
Index coordinates from zero. The two25-edge components above are
exchanged by
\[
g(x)=\sigma(x)\oplus e_0\oplus e_3\oplus e_6,
\]
where $\sigma$ exchanges coordinates2 and5. Here $g^2$ is the identity,
and $\Ham(x,g(x))$ is3 or5. Extend $g$ to $Q_8$ by leaving coordinate7
unchanged. Identifying each vertex with its partner gives a128-vertex
quotient graph; two pairs are adjacent when a cube edge joins them.
It is the Cartesian product of the corresponding64-vertex quotient
of $Q_7$ and one binary edge.

\begin{proposition}[Lifting a quotient path]
For this involution, every induced quotient path of length $\ell$
lifts to two disjoint, nonadjacent induced paths of length $\ell$
in $Q_8$.
\end{proposition}
\begin{proof}
Choose either representative of the first quotient vertex.
Each following step has exactly one neighbouring representative:
two representatives of the next pair cannot both be neighbours,
since their mutual distance is at least three. The partner choices
give the second path. Distinct quotient vertices prevent repeated
or shared lifted vertices. An edge between nonconsecutive lifted
vertices would project to a quotient chord. An edge between the
two paths at consecutive positions would contradict uniqueness of
the lifted edge, and the paired vertices at the same position are
nonadjacent.
\end{proof}
The generic lifting and separation arguments pass Lean. Finite
checks also establish this involution's values, cube-edge images,
and the required separation for all256 vertices of $Q_8$.

Two49-edge lifted paths would occupy100 vertices. A compatible
opposite-face forest on95 vertices would then produce194 edges;
97 opposite-face vertices would produce196. These are construction
targets. Their existence and any optimality conclusion remain open.
For194 edges, the opposite-face colour difference must be $1$ or $-1$,
because the two49-edge paths are balanced and cube parity reverses
between faces.

\paragraph{Finite evidence and the next construction.}
A native enumeration of1536 specified commuting isometries considers
all one-crossing joins of two contiguous subpaths of the displayed
25-edge quotient path. Its restricted maximum is42 edges, yielding
two nonadjacent42-edge paths in $Q_8$. This gives86 face vertices
and does not settle the unrestricted quotient maximum.

The saved $Q_9$ bank contains balanced47-edge pairs related by
different involutions:20 labelled maps were found by matching
transitions, allowing reversal. Their minimum partner distance can
be two. In that case some quotient edges lift to squares, so their
two endpoints cannot both be selected. Keeping the full quotient
adjacency relation is essential; merely deleting these edges would
hide cross-path contacts. A further Lean separation argument uses
uniqueness only on the chosen path steps.

The50-vertex quotient query for the extended lower-dimensional
symmetry remains unresolved after120 seconds. For the first observed
47-edge pair, the query allowing at most four omitted seed orbits,
with one endpoint fixed, remains unresolved after90 seconds.
The omission count concerns quotient orbits, hence at most eight
vertices from the original96-vertex paired forest; it does not
control each labelled path separately. A four-crossing query with
the98-vertex bank face fixed and target192 edges also remains
unresolved after120 seconds.

With both face selections fixed to known examples, the contraction
and connectivity model reconstructs the98-edge and191-edge paths;
both decoded paths pass native all-pairs checks. These computations
provide no new record or global bound. The next attempt uses the
observed47-edge pair, retains the forbidden-pair conditions, and
excludes disconnected cycles as they occur instead of repeating
the unchanged connectivity-flow query. The construction criteria
are written deductions; the solver encoding and numerical searches
are not complete Lean certificates. Records appear
in~\cite{forests195archive}.

'''
shorttext=r'''
\paragraph{Transferring the dimensional construction.}
The useful patterns are compatibility in $6\to7$ and multiple
components per face in $7\to8$. In the98-edge example, one face
contains two25-edge paths, hence52 vertices; the other contains
three paths with47 vertices. Four crossings join these five
components. For $8\to9$, two49-edge paths in one face and95
compatible vertices in three opposite-face paths would give194
edges. This remains a construction target.

The two25-edge components are exchanged by an involution that swaps
two coordinates and flips three others. Identifying paired vertices
reduces the search to a smaller graph. An induced path there lifts
to two disjoint, nonadjacent paths: a repeat or a nonconsecutive
contact would project to a repeat or chord, while the distance
between partners prevents two lifts of a consecutive edge.
The lifting argument and this symmetry's finite properties pass Lean.

A restricted construction using1536 placements reaches two42-edge
paths in $Q_8$, giving86 face vertices. The saved $Q_9$ bank instead
provides symmetric47-edge pairs under other involutions. Their
quotients require an additional rule: both endpoints of an edge
that lifts to a square cannot be selected. A Lean separation lemma
supports this version under explicit safe-step hypotheses.

The larger quotient and four-crossing searches remain unresolved.
Known98- and191-edge patterns are reconstructed when their face
selections are fixed. The next attempt starts from an observed
47-edge pair and seeks a larger pair while excluding disconnected
cycles as they appear. A larger pair must still be joined to a
compatible opposite-face forest before it yields a longer snake.

'''
section=prose(section);shorttext=prose(shorttext)
edits=[]
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
 p=D/name;old=p.read_bytes();text=old.decode('utf-8');preamble=text[:text.index('\\begin{document}')]
 (H/'data'/(name+'.before.txt')).write_bytes(old)
 if name=='snake9_research.tex':
  anchor='\\section{Construction experiments and their scope}';assert text.count(anchor)==1 and '\\label{sec:forests195}' not in text
  text=text.replace(anchor,section+anchor)
  text=text.replace('The next construction route is to reroute the shorter 189-edge states\nbefore endpoint regrowth. Records and proof receipts are retained','Round194 proposed rerouting the shorter189-edge states before\nendpoint regrowth. The following subsection develops the subsequent\ndimensional construction route. Records and proof receipts are retained')
  bib=r'''\bibitem{forests195archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Dimensional transfer through symmetric path forests}. Research record195, 12 November2026. Lifting proofs, symmetry comparisons and restricted construction searches:
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/195-shortened-reroutings}.

'''
  text=text.replace('\\end{thebibliography}',bib+'\\end{thebibliography}')
 else:
  text=text.replace('Research state after round 194','Research state after round 195')
  text=text.replace('The next $Q_9$ search will allow rerouting of the shorter 189-edge\nstates before endpoint regrowth.','The proposed rerouting search on the shorter189-edge states remains\nincomplete. The current dimensional route is described next.')
  text=text.replace('\\textbf{7. What is proved, and what remains.}',shorttext+'\\textbf{7. What is proved, and what remains.}')
  text=text.replace('research records 175--194','research records 175--195')
  preamble=preamble.replace('Research state after round 194','Research state after round 195')
 assert text[:text.index('\\begin{document}')]==preamble
 p.write_text(text,encoding='utf-8');mirror=R/'paper'/name;mirror.write_bytes(p.read_bytes())
 assert sha(p)==sha(mirror)
 edits.append(dict(editor=str(p),mirror=str(mirror),before_sha256=hashlib.sha256(old).hexdigest(),after_sha256=sha(p),preamble_preserved_except_short_date=True))
(H/'data/manuscript-edits.json').write_text(json.dumps(edits,indent=2)+'\n')
handoff='''# Round 195 complete; goal active

The user explicitly resumed after the round194 pause and requested construction methods based on6-to-7 and7-to-8. Read milestones/195-shortened-reroutings/MATHEMATICAL_NOTE.md and data/completion.json.

Current focus: four-crossing lifts made from two Q8 paths in one face and three in the other. Two49-edge paths give100 face vertices; a compatible95-vertex opposite forest would give194 edges. This is a target, with no construction or optimality result yet.

The observed Q8 two25-edge components are exchanged by swapping coordinates2/5 and XOR73. The involution extends to Q8 and has partner distances3 or5. Its128-vertex quotient gives a route to symmetric nonadjacent path pairs. Lean checks generic lifting and separation, the finite involution and neighbour properties, and a safe-step version for distance-two involutions. Eleven accepted modules have16 theorem reports.

The restricted1536-isometry, two-subpath, one-crossing construction has native maximum42 edges, giving86 face vertices. The saved Q9 bank has balanced47-edge paired components under different involutions;20 labelled maps were found. The first such map has distance-two partners. Keep the full quotient adjacency and forbid selecting both endpoints of double-lift edges. Do not simply delete those edges.

Next: use scripts/affine_search.py and the first observed47-edge pair, replacing connectivity flow with an induced-degree relaxation and sound cycle exclusions. The initial target is50 quotient vertices, hence two49-edge paths. Its at-most-four-omission bound counts quotient orbits, equivalently at most8 omitted vertices from the96-vertex paired forest. It does not bound each labelled component separately. Widen that restricted neighbourhood if excluded. A valid paired forest still needs the opposite-face completion; scripts/four_crossings.py gives the precise four-port model including singleton outer components and connectivity.

Current UNKNOWN runs: quotient50(120s); affine50-omit4(90s); lower-four98(30s); bank-four192(120s). No exclusion follows. Fixing both face selections reconstructs known98- and191-edge paths; all-pairs verification passes. The earlier short-state scan stopped for low free memory after6 completed states and238 discovered states, so its closure is incomplete. Its source is preserved and the sampling-interval bug was corrected afterwards. Do not repeat an unchanged timeout.

Inherited round194 result: one block replacement through44 edges then endpoint addition excluded for131 saved191-edge Q9 snakes; repeated-move closure only through33. Known suboptimal48-edge Q7 comparison has minimum block in[38,43]. No new Q9 record or global upper bound in195.

Archived235 still awaits a complete independent rebuild;233/234 remain conditional. Round187 has93/98 batches and11904/12424 clauses; critical contradiction and actual-snake transfer pending. The contributor branch remains ecc47830c77df280f402f851799336dc81a7f680 at the opening refresh; its reported2659/3118 production modules were not independently rebuilt. Whole-manuscript review next at200.

Keep the existing D:/Codex/2026-10-13/new-chat/outputs manuscripts authoritative and mirror E:/Snake-in-a-box/paper. Preserve author order and hypersetup. Preserve unrelated .gitignore and milestone50 critical-family edits. Keep one heavy worker,1GiB startup free memory,768MiB reserve,256MiB Lean limit,60s proof checks, and bounded solver runs. All research processes must be terminal before publication.
'''
handoff=prose(handoff)
(R/'handoff/CURRENT_STATUS.md').write_text(handoff)
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text('Continue the active construction goal from round195. Inspect repository state and the saved evidence before continuing.\n\n'+handoff)
p=R/'README.md';old=p.read_text();p.write_text('''# Current result after round 195

The current construction route transfers the two-path face pattern of the98-edge Q8 snake to Q9. A checked quotient-lifting argument produces two disjoint nonadjacent paths from a suitable quotient path. The observed25-edge pair and saved47-edge pairs have different involution types; distance-two partners require explicit forbidden-pair constraints.

The restricted symmetric construction reaches two42-edge Q8 paths. Larger searches remain unresolved. Known98- and191-edge patterns are reconstructed with face selections fixed. No new record or global bound is claimed. Research remains active.

Read [round195](milestones/195-shortened-reroutings/README.md), [the argument](milestones/195-shortened-reroutings/MATHEMATICAL_NOTE.md), [handoff](handoff/CURRENT_STATUS.md), and [frontier explanation](paper/snake9_frontier_explanation.tex).

## Earlier checkpoints

'''+old)
print('Saved round195 results, manuscripts and active handoff; accepted modules',len(accepted),'reports',sum(r['reports'] for r in accepted))
