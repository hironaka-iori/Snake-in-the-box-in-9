"""Update both existing manuscripts with the complete width44 reduction."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
assert json.loads((H/'data/coverage44.json').read_bytes())['status']=='COMPLETE_NATIVE_EXCLUSION'
assert json.loads((H/'data/TemplateFacts227-audit.json').read_bytes())['status']=='PASS'
section=r'''\subsection{Reduction to two lower-dimensional paths}
\label{sec:lowerpair227}
The remaining width-44 cases can be reduced by enumerating their small
upper-face portions first. This separates the choice of coordinate
crossings from the long path search inside $Q_8$.

\begin{proposition}[Fixed upper portions]
\label{prop:fixedupper227}
Write $Q_n=Q_{n-1}\times\{0,1\}$, and let $\pi$ delete the final coordinate.
Suppose a replacement starts and ends in the upper face and crosses the
last coordinate exactly twice. It consists of an upper induced path $A$,
a lower induced path $B$, and an upper induced path $C$.
These pieces assemble to an induced path precisely when $A$ and $C$
are disjoint and nonadjacent, and their projections meet $B$ only at
the two prescribed joining endpoint pairs. A separate lower path $P$
is disjoint and nonadjacent to this replacement precisely when $P$ and
$B$ are disjoint and nonadjacent and $P$ avoids $\pi(A\cup C)$.
\end{proposition}
\begin{proof}
The face is constant between successive coordinate crossings, giving
the stated decomposition. Within a piece, inducedness is already known.
Between the two upper pieces, separation excludes repetitions and chords.
Between opposite faces, adjacency is exactly equality of the projections;
the two prescribed endpoint coincidences therefore supply exactly the
intended joining edges. The same distinction proves the assertion about
$P$. Conversely, any further coincidence, same-face edge or repeated
vertex would violate inducedness or separation. The actual three-piece
constructor is covered by the previously checked two-crossing theorem;
the present finite template extraction is a separate native calculation.
\end{proof}

If the complete replacement has 44 edges and $A,C$ contain $r,s$
vertices, respectively, then $B$ has $44-r-s$ edges. A one-crossing
replacement has just one upper piece and obeys the corresponding formula
with the other piece absent. Thus each upper choice specifies exact
lower endpoints, an exact lower length, and forbidden projections.
The resulting task is to find two induced lower paths in the prescribed
domains, disjoint and nonadjacent to each other. Equality of the two
endpoint pairs, lengths and literal domains identifies duplicate tasks.
Containment of both domains, with endpoints and lengths fixed, permits
the smaller task to be excluded by excluding the larger one.

For the seven cases isolated in Section~\ref{sec:residual226}, the first
lower path runs from 18 to 224 in 43 edges and is followed by vertex 480.
The second upper domain has 13 or 14 vertices. Exhausting its induced
prefixes and suffixes gives 18 configurations. These form six exact
lower-task groups; one group is contained in another after deleting
vertex 212 from both domains. Five representative tasks remain:
\[
\begin{array}{c|c|c}
\text{second lower endpoints}&\text{second lower edges}&
\text{two domain sizes before anchor pruning}\\\hline
(35,201)&33&(107,106)\\
(35,208)&32&(107,106)\\
(35,212)&39&(107,106)\\
(35,208)&38&(106,105)\\
(35,201)&35&(105,104)
\end{array}
\]
All five native queries are infeasible. Two of these tasks occur in
all seven index contexts. Substituting the same lower paths produces
the identical full vertex sequence in those contexts: their different
boundaries merely assign unchanged upper vertices to different portions
of the representation. This is an exact redundancy of the construction
description, without a claim of a new cube symmetry.

The other 35 unresolved contexts have both first anchors in the lower
face. Their total replacement crossing budget is one or two. First-path
parity makes its crossing count even. Budget one forces allocation
$(0,1)$. For budget two, the second anchors are upper and their allowed
upper domain contains fewer than 45 vertices; zero second crossings
cannot support a 44-edge path. Thus allocation $(0,2)$ is forced.
The first path consequently stays entirely in $Q_8$ and has 44 edges.
The second upper portions give 230 configurations, 79 exact task groups
and 52 representatives after domain containment. Every one of the 52
native queries is infeasible.

Consequently all 42 cases left by the preceding round are excluded.
Together with its prior 259 exclusions, this covers all 301 maximal
width-44 contexts. Padding smaller replacements with unchanged original
vertices gives the exclusion for two blocks of at most 44 edges each.
The seed, endpoint 24, retained outside indices, length preservation and
four coordinate crossings remain fixed. No 192-edge witness or global
upper bound follows from this restricted exclusion.

The new literal face conditions, two seven-member task equalities and
domain containment have passed Lean kernel checks. Their extraction from
the saved data remains native. All 57 solver queries terminate as
infeasible at their first solve, with no cycle cuts. The model requires
the correct selected counts, parity counts, endpoint degrees and
cross-path separation; it permits disconnected cycles in addition to
the endpoint paths. Infeasibility of this relaxation therefore excludes
the intended paths. Its contradictions and the complete finite upper
enumerations have no Lean certificates. The independent direct search
processed 5,157,314 first prefixes before its time limit and proved no
exclusion; its preserved frontier is superseded by the native cover.
Future construction searches must change the scope, for example by
allowing wider blocks, another endpoint or another seed~\cite{research227}.

'''
short=r'''The restricted exclusion now covers two replacement blocks of at most
44 edges. The earlier width-43 cover and boundary-change argument left
42 of the 301 maximal width-44 contexts open. The final reduction fixes
the short upper-face portions and solves the remaining path-pair problems
inside $Q_8$.

The justification is direct. An induced path starting in the upper face
and crossing that coordinate exactly twice has an induced upper prefix,
one contiguous induced lower path and an induced upper suffix.
The two upper pieces must be disjoint and nonadjacent. Across opposite
faces, adjacency is equality of the lower projections, so the lower path
must avoid every upper projection except its two joining endpoints.
A separate lower path must avoid all those upper projections and must
be disjoint and nonadjacent to the lower excursion. These conditions
are sufficient as well as necessary, by checking pairs within and between
the three pieces. The general gluing constructor was already checked
in Lean.

In seven contexts the first lower path has 43 edges from 18 to 224,
followed by 480. Enumerating the second upper portions gives 18
configurations, which reduce to five representative lower-path tasks.
All five are natively infeasible. Two task groups occur in all seven
contexts and give exactly the same full vertex sequence when assembled;
the differing interval boundaries are duplicate representations.

In the other 35 contexts the first anchors are lower. Endpoint parity
and the total crossing budget force zero first crossings: with budget
two, the second path must use both crossings because its upper domain
has fewer than the required 45 vertices. The first lower path now has
44 edges. Complete upper enumeration gives 230 configurations, 79 exact
groups and 52 representatives after domain containment. All 52 native
queries are infeasible. The 42 new exclusions complete the 301-context
cover; smaller blocks are included by padding with unchanged vertices.

The new concrete face conditions, repeated task equalities and one
domain containment passed Lean kernel checks. Data extraction, upper
enumeration, domain preparation and the 57 solver contradictions retain
their separate native status. An earlier two-minute direct search
remained incomplete; its checkpoint is preserved and superseded by this
cover. These results concern one fixed seed, endpoint 24, two
length-preserving blocks and four coordinate crossings. They give no
new snake or global optimality conclusion~\cite{research227}.

'''
bib=r'''\bibitem{research227}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Fixed upper portions and exact
lower-dimensional replacement tasks}. Research milestone 227,
15 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/227-shared-q8-construction}.

'''
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
    p=D/name;before=(H/'data'/(name+'.before.txt')).read_bytes();assert p.read_bytes()==before
    text=before.decode('utf-8').replace('Research state after round 226','Research state after round 227')
    if name=='snake9_research.tex':
        old='two-block search through length 43 is excluded natively; width 44\nretains 42 unresolved contexts. Seven share one explicit induced-path\nconstruction problem in an eight-dimensional subgraph.'
        assert old in text;text=text.replace(old,'two-block search through length 44 is excluded natively. Fixing small\nupper-face portions reduces the final 42 cases to 57 lower-dimensional\npath-pair queries, all infeasible.',1)
        text=text.replace('The port queries exclude four complete contexts; 42 width-44 contexts\nremain unresolved.','The port queries excluded four complete contexts; at that stage, 42\nwidth-44 contexts remained unresolved.',1)
        text=text.replace('Seven surviving contexts all require the first alternative. They share','The seven selected surviving contexts all required the first alternative. They share',1)
        anchor=r'\section{Verification scope and remaining problem}\label{sec:verification}';assert text.count(anchor)==1;text=text.replace(anchor,section+anchor,1)
        old='width-44 exclusions retain native solver dependencies.';assert old in text;text=text.replace(old,old+'\nSection~\\ref{sec:lowerpair227} completes the native width-44 cover through\nfinite upper portions and reduced $Q_8$ path-pair queries. The new literal\ntemplate facts are kernel checked; the enumeration and solver contradictions\nremain native.',1)
    else:
        text=text.replace('milestones through round 226','milestones through round 227')
        start=text.index('The restricted exclusion now reaches two blocks of at most 43 edges.')
        end=text.index(r'\section{Remaining questions}',start);text=text[:start]+short+text[end:]
        text=text.replace('The current route varies both faces in a four-crossing construction.','The completed two-block search excludes widths through 44 for the chosen\nendpoint and seed. Wider blocks, another endpoint or another seed are\nthe next construction choices.',1)
    text=text.replace(r'\end{thebibliography}',bib+r'\end{thebibliography}',1)
    p.write_bytes(text.encode('utf-8'));(R/'paper'/name).write_bytes(p.read_bytes())
print('UPDATED_EXISTING_MANUSCRIPTS227')
