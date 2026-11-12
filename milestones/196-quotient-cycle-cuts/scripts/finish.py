from pathlib import Path
import datetime,hashlib,json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def read(name):return json.loads((H/'data'/name).read_bytes())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
names=['affine50-omit4','affine50-free-omit4','affine50-free-omit6','affine50-free-omit6-retry']
results={n:read(n+'.json') for n in names}
assert results['affine50-omit4']['status']=='INFEASIBLE'
decisive=results['affine50-free-omit4'];assert decisive['status']=='INFEASIBLE' and decisive['root'] is None
assert len(decisive['dynamic_cycle_cuts'])==3
wider=results['affine50-free-omit6-retry'];assert not wider['witness'],'Inspect and certify the newly found construction before closing.'
assert wider['status'] in ['INFEASIBLE','UNKNOWN','RESOURCE_LIMIT','TIME_LIMIT']
lower=7 if wider['status']=='INFEASIBLE' else 5
inputs=[]
for name,d in results.items():
 assert not d['witness'];assert sha(H/'data'/(name+'.pbtxt'))==d['model_sha256']
 assert sha(H/'scripts/search.py')==d['script_sha256']
 assert sha(R/'milestones/195-shortened-reroutings/data/symmetry-comparison.json')==d['source_sha256']
 assert sha(R/'milestones/195-shortened-reroutings/data/forest-profiles.json')==d['profile_sha256']
 inputs.append(dict(result=name,status=d['status'],seconds=d['seconds'],iterations=len(d['iterations']),cycle_cuts=len(d['dynamic_cycle_cuts']),model_sha256=d['model_sha256']))
accepted=[]
for module in ['CycleCut196','CycleData196']+[f'ConcreteCycle196_{i}' for i in range(3)]:
 d=read(module+'-audit.json');assert d['status']=='PASS' and d['exit_code']==0 and d['stop_reason'] is None
 for p,h in d['dependencies'].items():assert sha(p)==h
 for key,digest in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(d[key])==d[digest]
 accepted.append(dict(module=module,reports=len(d['axioms']),receipt_sha256=sha(H/'data'/(module+'-audit.json'))))
cycles=read('cycle-cuts.json');assert cycles['source_sha256']==sha(H/'data/affine50-free-omit4.json')
for ordered,original in zip(cycles['ordered_cycles'],decisive['dynamic_cycle_cuts']):assert len(ordered)==36 and set(ordered)==set(original)
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
def rev(ref):return subprocess.check_output(git+['rev-parse',ref],cwd=R,text=True).strip()
summary=dict(round=196,status='PROGRESS',goal_status='pause_after_publication_requested_by_user',previous_turn_classification='PROGRESS: round195 introduced and checked the dimensional quotient construction, published as76948f42',
 utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),base_head=rev('HEAD'),contributor_head=rev('origin/research/unconditional-241'),searches=inputs,accepted_modules=accepted,
 minimum_omitted_seed_orbits=lower,minimum_added_orbits=lower+2,minimum_omitted_paired_vertices=2*lower,minimum_added_paired_vertices=2*(lower+2),
 restriction='The specific affine involution and safe quotient paths of50 vertices. Both endpoints are free in the decisive query. This is a necessary computational restriction, not an attained minimum or a global bound.',
 cut_certificate='All three36-vertex cuts in the four-omission free-end model have Lean noncontainment proofs. Solver infeasibility itself has no Lean contradiction certificate.',
 new_q9_record=False,new_global_bound=False,next_action='On explicit resumption, inspect the six-omission outcome. Change the search if it remains unresolved; do not repeat an unchanged timeout. An endpoint or block search in the safe quotient, or a different observed involution, can pursue a50-vertex path. A paired forest still requires its opposite-face completion for a longer Q9 snake.')
(H/'data/completion.json').write_text(json.dumps(summary,indent=2)+'\n')
(H/'data/input-audit.json').write_text(json.dumps(dict(inputs=inputs,cycle_sets_match=True,proof_receipts=accepted),indent=2)+'\n')
(H/'data/review.json').write_text(json.dumps(dict(reviewer='exchange191_review',mode='Read-only source and mathematical review; no computations or edits',findings=['The decisive free-end query has no hidden root constraint. Hints affect search order only.','Exactly two selected degree-one vertices and all other selected degrees two give one path plus disjoint cycles.','Excluding all vertices of each observed cycle is necessary for any induced path.','Colour balance is necessary because the involution preserves cube parity.','At least five omitted seed orbits implies at least seven added orbits, hence ten omitted and fourteen added vertices in the paired forest. This is not an attained minimum.','A resource-stopped query is unresolved. Initial model plus all dynamic cuts are needed for reproduction.','The cycle-cut theorem and its concrete instances do not certify the final solver infeasibility.']),indent=2)+'\n')
(H/'data/resource-events.json').write_text(json.dumps(dict(lean_startup_rejected=True,observed_startup_free_bytes=842797056,required_startup_free_bytes=1073741824,compiler_started_on_rejected_attempt=False,source='Saved tool output during this round; later startup and accepted proof receipts show recovery.',wider_original_status=results['affine50-free-omit6']['status'],retry_status=wider['status']),indent=2)+'\n')
wide_sentence=(f'The six-omission retry returned {wider["status"]} after {wider["seconds"]:.3f} seconds. '+('It increases the necessary omission count to seven.' if wider['status']=='INFEASIBLE' else 'The six-omission case remains unresolved.'))
note=r'''# Round 196: cycle exclusions in the paired-path construction

The user requested a pause after this round. Publish this checkpoint and stop; resume only upon an explicit request. No longer Q9 snake or global upper bound was obtained.

## Construction context

The goal remains a pair of49-edge paths in one Q8 face, occupying100 vertices, and a compatible three-path forest occupying95 vertices in the other face. Four crossings would give194 edges. The pair is sought through the safe quotient construction identified in round195.

This round fixes the involution determined by the first saved47-edge pair. In coordinates0 through7 it swaps0 with3 and2 with4, then flips coordinates0 through5. It preserves Hamming parity. Its128 quotient vertices represent pairs of cube vertices. A quotient edge having two possible lifts would create a square, so both endpoints of each such edge cannot be selected. There are16 such forbidden pairs in this input. The remaining selected adjacency is still evaluated in the full quotient contact graph.

## Degree relaxation and cycle exclusions

For each quotient vertex v, let x_v indicate selection and e_v indicate a path endpoint. Each quotient edge has a variable equal to the conjunction of its endpoint selections. Impose selected degree2x_v-e_v, e_v at most x_v, exactly50 selected vertices and exactly two endpoint flags. The decisive query leaves both endpoints free. Colour counts are25 and25 because the quotient is bipartite. At most four of the48 seed orbits may be omitted.

These constraints allow one path and disjoint cycles. Whenever a cycle C occurs, impose sum_{v in C} x_v at most |C|-1. A path cannot contain every vertex of C. More generally, no nonempty finite set in which every vertex has two distinct internal neighbours can be contained in an induced path: take the contained vertex with greatest path index. Both neighbours would have to occur at the unique immediately preceding position, a contradiction.

Lean checks the finite-maximum argument and this general noncontainment theorem. It also checks the actual neighbours and noncontainment of each of the three36-vertex cycle sets used in the decisive four-omission query. The quotient adjacency in these concrete certificates is computed from the specified coordinate permutation, translation and cube-neighbour maps. Five modules pass, with eleven theorem reports. The proof source snapshots and logs of two initial elaboration failures are preserved; accepted sources contain no admitted statements.

## Results

The fixed-root four-omission query is INFEASIBLE in7.469 seconds, without dynamic cycle cuts. The free-end four-omission query is INFEASIBLE in51.688 seconds after excluding three36-vertex cycles. The resulting necessary condition is that every50-vertex safe quotient path, if one exists under this involution, omits at least five of the48 original seed orbits and adds at least seven. In the actual paired forest, this means at least ten old vertices omitted and fourteen new vertices added. Individual labelled components may exchange representatives of an orbit, so these counts must not be applied separately to each component.

The six-omission query first stopped for the free-memory reserve after30.891 seconds. Its interrupted result is retained. @WIDER@

The strongest recorded necessary count after this round is at least @LOW@ omitted seed orbits and at least @ADD@ added orbits, corresponding to at least @DEL2@ omitted and @ADD2@ added vertices in the paired forest. This is a restricted computational lower restriction, not an attained minimum. The solver's final infeasibility has not been replayed in Lean; the checked cycle cuts are separate from that missing certificate.

## Reproduction and next step

The raw initial models are retained locally and packaged in data/solver-models.zip. Reproduce a terminal model by adding its recorded dynamic_cycle_cuts to its initial model. Omitting those cuts does not reproduce the decisive free-end query. Input hashes, resource records, solver iterations and proof receipts are retained.

On resumption, inspect the six-omission result before choosing the next bound. If unresolved, change the search representation rather than repeating the same limit. Searching endpoints and replacement blocks directly in the safe quotient can avoid disconnected cycles by construction; changing to another observed paired-forest involution is also available. Any larger paired forest still needs compatible ports and opposite-face paths before it yields a longer Q9 snake. The earlier6-to-7 comparison warns that maximizing the pair alone may sacrifice this compatibility.

The archived235 proof still awaits a complete independent rebuild. The233/234 bounds retain their documented conditions. Whole-manuscript consistency review remains scheduled for round200. No historical novelty is claimed for the finite-cycle exclusion principle.
'''
replacements={'@WIDER@':wide_sentence,'@LOW@':str(lower),'@ADD@':str(lower+2),'@DEL2@':str(2*lower),'@ADD2@':str(2*(lower+2))}
for key,val in replacements.items():note=note.replace(key,val)
(H/'MATHEMATICAL_NOTE.md').write_text(note,encoding='utf-8',newline='\n')
(H/'README.md').write_text('''# Round 196: quotient cycle exclusions

Read [the mathematical note](MATHEMATICAL_NOTE.md) and [completion record](data/completion.json).

The four-omission free-end query for a50-vertex safe quotient path is computationally infeasible. Three concrete36-vertex cycle exclusions and their general justification pass Lean. The final solver infeasibility remains outside Lean. The six-omission outcome is recorded separately; no new Q9 record or global bound follows.

The user requested a pause after this round. Do not start round197 without an explicit resumption.
''',encoding='utf-8',newline='\n')
section=r'''
\subsection{Cycle exclusions in the paired-path search}
\label{sec:cycles196}

Fix the involution of the first saved47-edge pair from the preceding
comparison. It exchanges coordinates0 with3 and2 with4 and flips
coordinates0 through5. In its128-vertex quotient,16 pairs of adjacent
vertices have two possible lifted edges; their endpoints cannot both
be selected. The full quotient adjacency is retained when imposing
inducedness. The target is50 quotient vertices, corresponding to two
49-edge paths in $Q_8$.

For a selected vertex $v$, impose degree $2x_v-e_v$, where $x_v$ is its
selection indicator and $e_v\le x_v$ its endpoint indicator. Require
$\sum x_v=50$ and $\sum e_v=2$. Both endpoints may move. The involution
preserves parity, so a path has25 selected vertices of each colour.
These degree conditions allow a path together with disconnected cycles.
Each observed cycle $C$ supplies the necessary inequality
\[
\sum_{v\in C}x_v\le |C|-1.
\]

\begin{lemma}
No nonempty finite vertex set having two distinct neighbours within
the set at every vertex can be contained in an induced path.
\end{lemma}
\begin{proof}
Choose a contained vertex having greatest index along the path.
Its two distinct internal neighbours must both occur before it.
Inducedness requires each to occupy the immediately preceding index,
which is impossible.
\end{proof}
The finite-maximum argument and this noncontainment statement pass
Lean. The three specific36-vertex sets used below also have checked
neighbour and noncontainment proofs for the actual quotient relation.
These certificates justify the cuts; they do not certify the final
solver infeasibility.

With one seed endpoint fixed, the query permitting at most four
omitted seed orbits is infeasible in7.469 seconds. Allowing both
endpoints to move gives infeasibility in51.688 seconds, after three
cycle exclusions. Thus a50-vertex safe quotient path under this
involution, if one exists, must omit at least five of the48 seed
orbits and add at least seven. The paired forest must consequently
omit at least ten old vertices and add at least fourteen. These
counts concern the union of the paired paths; they do not apply
separately to either labelled component.

The first six-omission run stopped for the free-memory reserve.
@WIDER@
The strongest recorded necessary omission count is therefore @LOW@
seed orbits. This restriction is computational and confined to the
specified involution. It establishes neither an attained minimum nor
a new global bound or construction. A larger pair must still have
compatible crossing ports and opposite-face paths. Exact models,
cycle sets and proof receipts appear in~\cite{cycles196archive}.

'''
shortsection=r'''
\paragraph{Removing disconnected cycles from the construction search.}
For the chosen symmetric47-edge pair, the revised search permits
both endpoints to move and seeks50 quotient vertices. Its degree
constraints can produce a path together with cycles. Whenever a
cycle appears, at least one of its vertices must be excluded.
The reason is direct: the greatest-indexed cycle vertex on an
induced path would need two distinct neighbours at the same
preceding position. Lean checks this argument and all three
36-vertex cycle sets used in the four-omission calculation.

That calculation is infeasible even with free endpoints. Hence any
desired50-vertex safe quotient path under this involution must omit
at least five seed orbits and add at least seven, corresponding to
ten omitted and fourteen added vertices in the paired forest.
The numerical infeasibility remains a native solver result.
@WIDER@
No longer nine-dimensional snake follows. A larger pair must still
be completed by a compatible opposite-face forest.

'''
for key,val in replacements.items():section=section.replace(key,val);shortsection=shortsection.replace(key,val)
import re
def polish(s):
 return re.sub(r'\b(the|a|an|two|three|one|with|of|for|and|in|at|all|through|contains|using|use|has|have|by|after|from|before|to|on|over|occupy|give|gives|produce|produces|target|record|records|round|coordinates|coordinate|components|case|pairs|dimension|corresponding|observed|balanced|saved|known|remains|is|or|than|both|its|hence|indices|distance|uses|seeking|targeting|discovering|valid|archived|conditional|optimal|symmetric|specific|specified|least|paired|first|chosen|following|these|new|input|giving|fixed)(?=\d)',r'\1 ',s,flags=re.I)
section=polish(section);shortsection=polish(shortsection)
edits=[]
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
 p=D/name;old=p.read_bytes();text=old.decode('utf-8');preamble=text[:text.index('\\begin{document}')]
 (H/'data'/(name+'.before.txt')).write_bytes(old)
 if name=='snake9_research.tex':
  marker='\\section{Construction experiments and their scope}';assert text.count(marker)==1 and '\\label{sec:cycles196}' not in text
  text=text.replace(marker,section+marker)
  bib=r'''\bibitem{cycles196archive}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Cycle exclusions for symmetric paired-path constructions}. Research record 196, 12 November 2026. Solver models, exact cycle cuts and checked noncontainment proofs:
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/196-quotient-cycle-cuts}.

'''
  text=text.replace('\\end{thebibliography}',bib+'\\end{thebibliography}')
 else:
  text=text.replace('Research state after round 195','Research state after round 196');preamble=preamble.replace('Research state after round 195','Research state after round 196')
  marker='\\textbf{7. What is proved, and what remains.}';assert text.count(marker)==1
  text=text.replace(marker,shortsection+marker).replace('research records 175--195','research records 175--196')
 assert text[:text.index('\\begin{document}')]==preamble
 p.write_text(text,encoding='utf-8',newline='\n');mirror=R/'paper'/name;mirror.write_bytes(p.read_bytes());assert sha(p)==sha(mirror)
 edits.append(dict(editor=str(p),mirror=str(mirror),before_sha256=hashlib.sha256(old).hexdigest(),after_sha256=sha(p),preamble_preserved_except_short_date=True))
(H/'data/manuscript-edits.json').write_text(json.dumps(edits,indent=2)+'\n')
handoff=f'''# Round 196 complete; pause requested after publication

The user explicitly requested a pause after this round. Publish and pause the goal. Do not start round197 until she explicitly resumes. Read milestones/196-quotient-cycle-cuts/MATHEMATICAL_NOTE.md and data/completion.json.

The specific paired47-edge forest's safe quotient was searched for50 vertices with bounded seed-orbit omissions. At most4 omissions with a fixed root is INFEASIBLE(7.469s); free endpoints is INFEASIBLE(51.688s) after three36-vertex cycle cuts. The free-end model has no hidden root restriction. The initial degree model permits one path and disjoint cycles. Add every recorded dynamic_cycle_cut when reproducing a terminal model.

The first six-omission run stopped RESOURCE_LIMIT. {wide_sentence}
The strongest necessary restriction is at least{lower} omitted and{lower+2} added seed orbits, equivalently at least{2*lower} omitted and{2*(lower+2)} added actual vertices from the paired forest. It is not an attained minimum and does not count either labelled component separately. No new Q9 record or global bound follows.

Five Lean modules pass with11 theorem reports: finite maximum, no contained nonempty finite set with two distinct internal neighbours, and the exact three36-vertex quotient cycle exclusions. CycleData196 contains the concrete quotient and cycle data. Final solver infeasibility is not replayed in Lean. Two failed elaboration attempts and a rejected low-memory startup are preserved. Accepted artifacts are immutable.

On resumption, do not repeat the unchanged six-omission query if unresolved. A direct endpoint/block search in the safe quotient or another observed involution is available. A100-vertex paired face still needs a compatible95-vertex opposite three-path forest for194 edges. Retain the full quotient contact graph and forbid both endpoints of double-lift edges; merely deleting those edges is unsound.

Round195 supplied the dimensional construction and quotient lifting; round194 excludes a single block replacement through44 edges followed by endpoint addition for the131 saved191-edge snakes, while repeated-move closure remains through33. Archived235 rebuild is pending;233/234 remain conditional. Whole-manuscript review next at200.

Preserve the D:/Codex/2026-10-13/new-chat/outputs editor manuscripts, mirrored in E:/Snake-in-a-box/paper. Authors and hypersetup remain unchanged. Preserve unrelated .gitignore and milestone50 critical-family edits. Keep one heavy worker,1GiB startup free memory,768MiB reserve,256MiB Lean limit and60s proof checks. All research processes must be terminal before publication.
'''
handoff=polish(handoff)
(R/'handoff/CURRENT_STATUS.md').write_text(handoff,encoding='utf-8',newline='\n')
(R/'handoff/NEXT_AGENT_PROMPT.md').write_text('Research pauses after round196 at the user\'s request. Resume only after explicit authorization, then inspect the repository and saved evidence.\n\n'+handoff,encoding='utf-8',newline='\n')
p=R/'README.md';old=p.read_text();p.write_text(f'''# Current result after round 196

The paired-path construction now has a restricted computational exclusion: the chosen50-vertex safe quotient path must omit at least{lower} seed orbits. The four-omission free-end query was excluded using three36-vertex cycle cuts, each checked in Lean. Final solver infeasibility remains outside Lean. No new Q9 record or global bound follows.

The user requested a pause after this round. Read [round196](milestones/196-quotient-cycle-cuts/README.md), [the argument](milestones/196-quotient-cycle-cuts/MATHEMATICAL_NOTE.md), [handoff](handoff/CURRENT_STATUS.md), and [frontier explanation](paper/snake9_frontier_explanation.tex).

## Earlier checkpoints

'''+old,encoding='utf-8',newline='\n')
for p in [H/'MATHEMATICAL_NOTE.md',H/'README.md']:
 p.write_text(polish(p.read_text()),encoding='utf-8',newline='\n')
print('Saved round196; necessary omitted orbits',lower,'Lean modules',len(accepted),'reports',sum(r['reports'] for r in accepted),'wider status',wider['status'])
