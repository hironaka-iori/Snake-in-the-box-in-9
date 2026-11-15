"""State the current constructive deduction in the existing manuscripts."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
s=json.loads((H/'data/search-summary.json').read_bytes());assert len(s['width44_unresolved'])==42
for name in ['Residual226','ResidualCapacity226','ZeroFace226','FaceCounts226','BoundaryContraction226']:
    assert json.loads((H/'data'/(name+'-audit.json')).read_bytes())['status']=='PASS'
section=r'''\subsection{Residual capacity, boundary changes and a common eight-dimensional path}
\label{sec:residual226}
The two replacement intervals considered here have at least one retained
index between them. Thus their complete selected paths, including anchors,
must be disjoint and nonadjacent. After selecting any prefix of the first
path, remove its vertices and neighbours from the second allowed graph.
A compatible second path must lie entirely in the component containing
its initial anchor. That component must also contain the terminal anchor,
enough vertices for the prescribed length, and enough vertices of each
alternating parity. The justification is induction along the second path:
every allowed adjacent step stays in the component. Path injectivity
then supplies the size inequalities. Extending the first prefix only
deletes more vertices, so a shortage cannot be repaired. These general
containment, capacity and monotonicity statements have passed Lean.

A path with zero crossings of a coordinate stays in its initial face.
Induction over coordinate changes proves this, and injectivity bounds
its size by the available vertices of that face. This implication has
passed Lean. In 24 of the 25 formerly unresolved width-43 contexts,
the second anchors are in the upper face, which contains only 13 or
14 allowed vertices, whereas the replacement needs 44. The concrete
24 face counts have also passed kernel checks. The second path must
therefore use two crossings, forcing allocation $(0,2)$; its zero-crossing
alternative is impossible. The 24 resulting native queries are infeasible.
The remaining context has intervals $[2,45]$ and $[131,174]$ and allocation
$(0,1)$. Its first path starts at 17 and must next visit 19 or 49.
Both branches are infeasible. Together with the prior 269 exclusions,
this covers all 294 contexts. The specified two-block construction is
therefore computationally excluded through width 43.

\begin{proposition}[Necessary boundary changes]
\label{prop:boundary226}
Fix an original path and the complete-path requirements of a construction.
Suppose every candidate differing only within two replacement intervals
of at most $K$ edges has been excluded. If a candidate succeeds with two
intervals $[a,b]$ and $[c,d]$, each of $K+1$ edges, then at least one
replacement changes both original vertices immediately beside its anchors:
\[
\bigl(q_{a+1}\ne p_{a+1}\ \land\ q_{b-1}\ne p_{b-1}\bigr)
\quad\text{or}\quad
\bigl(q_{c+1}\ne p_{c+1}\ \land\ q_{d-1}\ne p_{d-1}\bigr).
\]
\end{proposition}
\begin{proof}
If each block retains one of these vertices, shorten that block at the
corresponding end. The new anchor still equals its original vertex,
and the complete candidate is unchanged. Both intervals now have $K$
edges, contradicting their exclusion. In the present application, a trim
cannot move blocker 7 or 143 onto an anchor: retaining its original vertex
would create a chord to endpoint 24. Thus the shortened candidate remains
within the covered family. The outside-agreement contraction and its
conditional contrapositive have passed Lean. The width-43 exclusion used
in this application retains its native numerical status.
\end{proof}

For an induced replacement, selecting an original anchor-neighbour forces
it into the adjacent path position. Hence the proposition is encoded by
requiring at least one block to omit both of its original anchor-neighbours.
Together with coordinate parity and face capacity, this excludes 46 of
the 92 previously open width-44 contexts, leaving 46 initially unresolved.

The 11 remaining contexts whose first anchors are in different faces
have first anchors 18 and 480. Crossing parity and, where needed, the
second-face shortage force exactly one first crossing. The component
of 480 in the allowed upper-face graph is precisely $\{480,488\}$.
Consequently the upper suffix is either $(480)$ or $(488,480)$.
Their lower crossing vertices are 224 and 232, requiring first lower-face
paths of 43 and 42 edges respectively. These two cases are exhaustive.
The port queries exclude four complete contexts; 42 width-44 contexts
remain unresolved.

Seven surviving contexts all require the first alternative. They share
exactly the same 109-vertex lower-face domain, endpoints 18 and 224,
and required length 43. Appending 480 then gives the first replacement.
This reduces their common construction task to one induced-path search
in $Q_8$, coupled to seven possible second replacements. A shared prefix
may be rejected only when all seven compatible second graphs fail.
No such compatible pair or 192-edge snake has yet been obtained.

The native direct searches remain incomplete. A block-chain refinement
removes vertices that cannot lie on a simple path between the second
anchors: an excursion into an off-chain block would repeat its attachment
vertex. Bounds on successive block segments add along that chain; adjacent
entry and exit vertices force a one-edge induced segment, and otherwise
bipartite colour counts bound its length. These written arguments support
the native pruning, without a complete Lean verification of the graph
decomposition or search traversal. All numerical exclusions above remain
restricted to the specified seed, endpoint 24, retained outside positions
and four total crossings~\cite{research226}.

'''
short=r'''The restricted exclusion now reaches two blocks of at most 43 edges.
Of the 25 cases left by the preceding search, 24 have only 13 or 14
available vertices in the second anchors' face, whereas that path needs
44 vertices. Zero crossings would keep it in that face, so the only
possible allocation is $(0,2)$. The zero-crossing implication and the
concrete face counts have passed Lean. All 24 native queries are infeasible.
The final case permits only $(0,1)$; its first step from 17 must go to 19
or 49, and both branches are infeasible. All 294 width-43 contexts are covered.

This exclusion constrains width 44. At least one replacement must change
both original vertices immediately beside its anchors. Otherwise shorten
each interval at an unchanged neighbour: the full candidate stays the
same and both intervals now have 43 edges, contradicting their exclusion.
The interval-contraction argument has passed Lean. Its numerical premise
remains the native width-43 calculation. Using this restriction and face
capacity leaves 46 width-44 cases open; a further crossing-port division
excludes four, leaving 42 unresolved.

Seven surviving cases share a concrete lower-dimensional task: construct
a 43-edge induced path from 18 to 224 in one fixed 109-vertex subgraph of
$Q_8$, then cross to 480. Their first upper suffix is forced to be $(480)$;
the alternative $(488,480)$ has been excluded. The same lower path must
then admit one of seven compatible second replacements. No such pair
has been found. A common-prefix search can address all seven contexts,
rejecting a prefix only if every second context is impossible.

For separated replacement intervals, a selected first prefix removes
itself and its neighbours from every second allowed graph. Any compatible
second path stays in its anchor's remaining component and needs enough
vertices of both parities. Extending the prefix only shrinks that graph.
These general statements have passed Lean; native component enumeration,
block-chain pruning and search traversal retain separate verification
limits. The finite exclusions give no global optimality conclusion
or longer snake~\cite{research226}.

'''
bib=r'''\bibitem{research226}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Residual capacity, boundary changes
and shared eight-dimensional replacement paths}. Research milestone 226,
15 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/226-connected-replacement-search}.

'''
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
    p=D/name;before=(H/'data'/(name+'.before.txt')).read_bytes();assert p.read_bytes()==before
    text=before.decode('utf-8').replace('Research state after round 225','Research state after round 226')
    if name=='snake9_research.tex':
        anchor=r'\section{Verification scope and remaining problem}\label{sec:verification}';assert text.count(anchor)==1;text=text.replace(anchor,section+anchor,1)
        text=text.replace('two-block search through length 42 is excluded natively; width 43\nretains unresolved cases.', 'two-block search through length 43 is excluded natively; width 44\nretains 42 unresolved contexts. Seven share one explicit induced-path\nconstruction problem in an eight-dimensional subgraph.',1)
        anchor='a native calculation, including the complete two-allocation split.';assert anchor in text
        text=text.replace(anchor,anchor+'\nSection~\\ref{sec:residual226} adds checked residual capacity, zero-face\ncounts and interval contraction. The completed width-43 cover and the\nwidth-44 exclusions retain native solver dependencies.',1)
    else:
        text=text.replace('milestones through round 225','milestones through round 226').replace('The replacement frontier after round 225','The current replacement frontier')
        start=text.index('The restricted exclusion now reaches two blocks of at most 42 edges.')
        end=text.index(r'\section{Remaining questions}',start)
        text=text[:start]+short+text[end:]
    text=text.replace(r'\end{thebibliography}',bib+r'\end{thebibliography}',1)
    p.write_bytes(text.encode('utf-8'));(R/'paper'/name).write_bytes(p.read_bytes())
print('UPDATED_EXISTING_MANUSCRIPTS226')
