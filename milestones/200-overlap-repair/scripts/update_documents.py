from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
trim=json.loads((H/'data/trim-census.json').read_bytes());assert trim['status']=='COMPLETE' and trim['maximum_forest_vertices']==92
proof=json.loads((H/'data/CollisionRepair200-audit.json').read_bytes());assert proof['status']=='PASS'
catalogue=json.loads((H/'data/catalogue-d4.json').read_bytes());assert catalogue['status'] not in ['RUNNING','WITNESS']
excluded=sum(r['status']=='INFEASIBLE' for r in catalogue['rows']);remaining=15-excluded
if catalogue['all_infeasible']:
 finding='All fifteen inverse-pair representatives are infeasible in the native model. Therefore every 100-vertex repair of two isometric copies of this parent requires at least five omissions in total, and hence at least three additions. This finite exclusion has no Lean contradiction certificate.'
else:
 finding=f'The native catalogue currently excludes {excluded} of the fifteen inverse-pair representatives at four total omissions; {remaining} representatives remain unresolved. The two minimum-intersection cases are among the exclusions. No complete four-omission exclusion is claimed.'

p=D/'snake9_research.tex';s=p.read_text(encoding='utf-8');before_main=hashlib.sha256(p.read_bytes()).hexdigest();preamble=s[:s.index('\\begin{document}')]
def edit(old,new):
 global s
 assert s.count(old)==1,(old[:90],s.count(old))
 s=s.replace(old,new)
edit('Write $G=24T+\\sum_{x\\in S}\\sigma_{12}(x)$. The following reduction uses\nonly the three explicit premises',
     'Write $G=24T+\\sum_{x\\in S}\\sigma_{12}(x)$ and\n$L=\\sum_q r_{12}(q)\\in\\mathbb Z_{\\ge0}$, and let $W$ denote the\nwindow-weight total. The following reduction uses the three premises')
edit('$L\\le95$ to domination have now been checked', '$\\sum_q r_{12}(q)\\le95$ to domination have now been checked')
edit('The useful local target for $012034$ is consequently share at least 18,\nrequiring exclusion of share at most 17. That local theorem remains open.',
     'For this earlier boundary-twenty-one comparison, the sufficient local\ntarget for $012034$ is share at least 18, requiring exclusion of share\nat most 17. That local theorem remains open. The current\nboundary-twenty-four profile in Section~\\ref{sec:floor14-loss} requires\nonly share at least 15 for this shape, together with its other stated\npremises.')
edit('Windows not yet examined are admitted, so the minimum cycle mean of this automaton is a valid lower bound on the average internal count.',
     'Windows not yet examined are admitted. The minimum cycle mean controls long-run average counts; finite snakes require the boundary terms in the potential summation below.')
edit('Further mergers retained five or four of the 26-cycles and replaced the remaining selected vertices by one path of 66 or 92 edges.',
     'Further merger searches retained five or four of the 26-cycles and sought a replacement path of 66 or 92 edges.')
edit('and no double-lift restrictions. Its quotient is nonbipartite.\n\nFor both one-contact cases,',
     'and no double-lift restrictions. Its quotient is nonbipartite.\nHere one contact counts one unordered pair $\\{u,h(u)\\}$ of selected\nvertices. For these fixed-point-free maps, one contact means\n$|S\\cap h(S)|=2$, consistent with Section~\\ref{sec:symmetry199}.\n\nFor both one-contact cases,')
edit('are included. Replacing them by $\\alpha(S),\\beta(T)$ changes the relative\nmap to $\\alpha^{-1}f\\beta$, which still ranges over the full family.',
     'are included. More precisely,\n\\[\n|\\alpha(S)\\cap f(\\beta(T))|\n=|S\\cap(\\alpha^{-1}f\\beta)(T)|.\n\\]\nThe maps on the right still range over every cube isometry.')
edit('or improve the current interval $191\\le a(9)\\le235$.','or improve the project interval $191\\le a(9)\\le235$, whose upper bound retains the archived-proof qualification.')
edit('This conditional estimate is weaker than the upper bound 235 in Theorem~\\ref{thm:upper235}.','This conditional estimate is weaker than the archived upper bound 235 in Theorem~\\ref{thm:upper235}.')
edit('The later six-centre proof in Section~\\ref{sec:upper-proof} establishes the current interval $191\\le a(9)\\le235$.',
     'The later archived contributor six-centre argument in Section~\\ref{sec:upper-proof} supplies the project interval $191\\le a(9)\\le235$, with the complete independent rebuild still pending.')

abstract=r"""Let $a(9)$ denote the maximum edge length of an induced path in the
nine-dimensional binary hypercube. An explicit checked construction gives
$a(9)\ge191$. The project retains an archived contributor argument for
$a(9)\le235$; its complete independent rebuild remains pending.

For a snake of length $m$, singleton-square count $T$ and empty-square
count $s_0$, we prove the exact identity
$T+2s_0+35(m+1)=9214$. Local singleton-count restrictions, endpoint
occurrence bounds and integer-share identities retain the contribution
of empty squares. Six and seven consecutive internal counts have sums
at least fourteen and sixteen. The stronger boundary gives
$39m+2s_0\le9192$ under the archived count-only argument, so a
235-edge snake would have at most thirteen empty squares.

For the retained share comparison, the sufficient pending local profile
is $(15,14,14,14)$ on four specified transition shapes. Together with
the remaining coverage, reference-exclusion and potential premises,
it would prove $a(9)\le234$. A separate contributor comparison targets
233 and retains unresolved certificate and interpretation requirements.
These conditional comparisons are distinguished from completed local
theorems and numerical calculations on finite graphs.

The constructive analysis studies how lower-dimensional paths can be
joined across coordinate faces. It includes checked joining and
replacement identities, restrictions on moving endpoints, and a concrete
pair of separated 47-edge paths in $Q_8$. Symmetry reduces one quotient
search to three endpoint classes. More generally, two parent paths with
sets $S,T$ can be placed in opposite faces without cross-edges exactly
when $S\cap f(T)=\varnothing$ for their relative cube isometry $f$.
A complete native census finds that two independently trimmed copies
of the specified 50-edge $Q_7$ parent yield at most 92 separated vertices,
even when all cube isometries are allowed. This restriction motivates
changes to the parent shapes. Generic counting deductions are checked
in Lean; the numerical placement censuses retain their separate scope.
No longer $Q_9$ snake or improved unconditional numerical bound is
obtained. The optimum and the conjectured value 196 remain unresolved.
"""
a=s.index('\\begin{abstract}')+len('\\begin{abstract}');b=s.index('\\end{abstract}',a);s=s[:a]+'\n'+abstract+s[b:]
addition=r"""
\subsection{The exact limit of trimming two copies of one parent}
\label{sec:repair200}

Let the two full parent paths have 51 vertices each. For a fixed relative
isometry $f$, write $C=|S\cap f(S)|$. If $D$ original vertices are removed
in total from the two copies to obtain disjoint retained sets, then
\[
C\le D.
\]
Indeed, each common vertex must be removed from at least one copy, and
one deletion removes at most one such coincidence. Equivalently, the
coincidences form a matching between the two lists of parent positions.
The same inequality holds when new vertices are subsequently added,
provided the final sets are disjoint. The Boolean counting deduction
has been checked in Lean.

For trimming alone, the retained total is $102-D$. A result of at least
92 vertices therefore has $D\le10$ and $C\le10$. This reduces a complete
search over all 645120 cube isometries to the 1363 maps with at most ten
coincidences. For each such map, there are 66 ways to remove at most ten
vertices from the two ends of the first parent. Its retained vertices
forbid a specified list of positions in the second parent. The longest
permitted second subpath is exactly the largest gap between those
forbidden positions. This exhausts every potentially competitive pair
of contiguous subpaths, including unequal lengths and different trims.

The native census examines 89958 first intervals and obtains the exact
maximum 92. It is attained by retaining positions $5,\ldots,50$ in
both copies for the map exchanging coordinates $(1,4)$ and $(3,6)$
and translating by 126. Thus even arbitrary relative isometries do not
improve the earlier 92-vertex direct-trimming construction from this
particular parent. The saved 96-vertex forest uses a changed parent path
and lies outside this restricted family. The complete numerical census
has no Lean replay.

The two minimum-intersection placements also admit short direct bounds.
Their coincidences occur at position pairs $(38,43),(43,38)$ and
$(4,38),(38,4)$, respectively. For retained intervals $[a,b)$ and $[c,d)$,
with endpoints between 0 and 51, forbidding both coincidences gives
$(b-a)+(d-c)\le89$ in the first case and at most 92 in the second.
These interval implications have been checked in Lean; the identification
of the concrete coincidence positions is supplied by the saved native data.

For a coupled repair with additions, let $A$ count new vertices in total.
A 100-vertex target satisfies
\[
100=102-D+A,\qquad D=A+2.
\]
This identity follows by partitioning each original and final set into
retained, removed and added vertices, and is checked in Lean. A repair
with $D\le4$ can start only at one of the sixteen relative isometries
with $C\le4$. Fourteen are involutions; the other two are inverses and
give equivalent repair problems after exchanging the parents and
applying the inverse isometry. There are therefore fifteen cases.

CATALOGUE_FINDING

The connected repair models allow both paths and all endpoints to move,
with 49 to 51 vertices per path and 100 in total. They impose no symmetry
relation between the final paths. For each of the two minimum-intersection
placements, allowing six total omissions remains unresolved after
60 seconds. These computations concern repairs of the specified parent
copies. They give no upper bound for arbitrary $Q_9$ snakes and no
opposite-face completion. Exact inputs and outcomes are retained in
research record~\cite{research200}.

""".replace('CATALOGUE_FINDING',finding)
marker='\\section{Construction experiments and their scope}\\label{app:experiments}';assert s.count(marker)==1;s=s.replace(marker,addition+marker)
bib=r"""
\bibitem{research200}
I. Hironaka, T. Ma and S. Zhan,
\emph{Collision counting, coupled repairs and manuscript review},
research record 200, 13 November 2026. Complete trimming census,
repair models, counting proofs and source-review reports:
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/200-overlap-repair}.

"""
s=s.replace('\\end{thebibliography}',bib+'\\end{thebibliography}');assert s[:s.index('\\begin{document}')]==preamble
p.write_text(s,encoding='utf-8',newline='\n')

p=D/'snake9_frontier_explanation.tex';s=p.read_text(encoding='utf-8');before_front=hashlib.sha256(p.read_bytes()).hexdigest()
s=s.replace('Research state after round 199','Research state after round 200').replace('research records 175--199','research records 175--200')
old='The involution quotient from the preceding work has three endpoint\nclasses, represented by 10, 2 and 0.'
new='A different involution gives the quotient used in the current endpoint\nsearches. In coordinates 0 through 6, let $h$ exchange 1 with 4 and\n3 with 6, then translate by 126. Add $x\\leftrightarrow h(x)$ to the\nordinary $Q_7$ edges. Its $Q_8$ extension has minimum displacement three\nand no double-lift restrictions. This quotient has three endpoint\nclasses, represented by 10, 2 and 0.'
assert s.count(old)==1;s=s.replace(old,new)
old='The generic path-image, layer-separation and representative-change\narguments pass Lean, with five theorem reports. The complete numerical\ncensuses remain native computations, without a Lean replay.'
new=r"""The generic path-image, layer-separation and representative-change
arguments pass Lean. The complete numerical censuses remain native
computations, without a Lean replay.

The trimming family now has an exact native limit. Two independently
trimmed copies of the published 51-vertex parent give at most 92
separated vertices, over all cube isometries. To see why the search is
complete, let $C$ count shared vertices and $D$ count deleted parent
vertices. Each shared vertex requires a deletion, so $C\le D$.
A retained total of at least 92 forces $D\le10$. Only 1363 isometries
have $C\le10$. For each, all 66 first-parent trims of cost at most ten
are examined; the best second interval is the largest gap avoiding
their collisions. The 89958 resulting cases attain 92 and never exceed it.
The 96-vertex forest found earlier changes the parent shape and is
therefore outside this trimming family.

For a repaired pair with additions, let $A$ count added vertices.
A 100-vertex target obeys $D=A+2$. Together with $C\le D$, this leaves
exactly sixteen starting isometries for repairs with $D\le4$, or fifteen
cases after identifying inverse maps. CATALOGUE_FINDING
The overlap-cover inequality, repair balance and interval bounds for
the two minimum-overlap cases pass Lean. The catalogue outcomes remain
native solver results. Six-omission searches in those two placements
remain unresolved after 60 seconds each.
""".replace('CATALOGUE_FINDING',finding)
assert s.count(old)==1;s=s.replace(old,new)
old='The full-bank exclusion remains native. The manuscript-wide review completed in round 190 remains separate\nfrom the pending certificate and proof rebuilds.'
new='The full-bank exclusion remains native. The manuscript-wide source review\ncompleted in round 200 corrects a historical merger claim, distinguishes\nthe two symmetry quotients, and clarifies finite-walk boundary terms.\nIt is separate from the pending certificate and proof rebuilds.'
assert s.count(old)==1;s=s.replace(old,new)
p.write_text(s,encoding='utf-8',newline='\n')
records=[]
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
 p=D/name;q=R/'paper'/name;q.write_bytes(p.read_bytes());records.append(dict(editor=str(p),mirror=str(q),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
(H/'data/document-mirrors.json').write_text(json.dumps(records,indent=2)+'\n',encoding='utf-8',newline='\n')
(H/'data/manuscript-review.json').write_text(json.dumps(dict(main_before_sha256=before_main,frontier_before_sha256=before_front,main_lines_reviewed=[1,8964],frontier_lines_reviewed=[1,961],review_reports=['logs/review-current.md','logs/review-history.md','logs/review-construction.md'],corrections=['Historical component mergers were unresolved search targets, not constructed paths.','Explicitly introduced the different quotient used for triangle-based endpoint classes.','Qualified finite-walk means by their boundary terms.','Separated old floor18 from current floor15 target.','Defined loss and window total at first use.','Explained one unordered contact versus two intersection vertices.','Made the direction of representative transport explicit.','Retained archived235 qualifications.','Updated abstract and present construction frontier.'],scope='Complete source reading distributed across three bounded reviewers, with consequential findings checked against source records by the main agent. No independent rebuild of archived proofs or replay of all finite certificates.'),indent=2)+'\n',encoding='utf-8',newline='\n')
print('UPDATED_DOCUMENTS_AND_FULL_SOURCE_REVIEW',excluded,'catalogue cases excluded')
