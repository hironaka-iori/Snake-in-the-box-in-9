"""Record the constructive round in the existing editor sources and mirrors."""
from pathlib import Path
import hashlib, json, re
H=Path(__file__).resolve().parents[1]; R=H.parents[1]
D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(b): return hashlib.sha256(b).hexdigest()
def once(s, old, new):
    assert s.count(old)==1, old[:100]
    return s.replace(old,new,1)
proof=json.loads((H/'data/FourCrossings223-audit.json').read_bytes())
assert proof['status']=='PASS'
rows=[]
for budget in [4,8,12]:
    result=json.loads((H/'data'/f'joint-d{budget}.json').read_bytes())
    run=json.loads((H/'data'/f'joint-d{budget}-execution.json').read_bytes())
    assert run['status']=='ACCEPTED_NATIVE_RESULT' and result['status'] in ['INFEASIBLE','UNKNOWN']
    rows.append(f"{budget} & \\texttt{{{result['status']}}} & {result['seconds']:.3f}\\\\")
table='\n'.join(rows)
section=r'''\subsection{Joint four-crossing construction}
\label{sec:coupled223}
The lower-dimensional examples suggest optimizing the components in both
faces together. The displayed constructions have component lengths
\[
18+24+6+2=50,\qquad 8+25+10+25+26+4=98.
\]
The final summands count crossings. In the second example, two 25-edge
paths occupy 52 vertices of one $Q_7$ face, exceeding the 51 vertices
available in a single longest $Q_7$ path. Compatibility between separated
components is therefore essential construction data.

\begin{proposition}[Five-component joining]\label{prop:five-join223}
Let $P_0,\ldots,P_4$ be oriented induced paths in $Q_n$, with edge
lengths $\ell_0,\ldots,\ell_4$. Consecutive paths intersect exactly at
the terminal vertex of the first and the initial vertex of the second.
Assume that every nonconsecutive pair assigned to the same face is
disjoint and nonadjacent, and every nonconsecutive pair assigned to
opposite faces is disjoint. Placing the paths in faces $0,1,0,1,0$
and joining the four consecutive pairs produces an induced path in
$Q_{n+1}$ of length $\sum_{i=0}^{4}\ell_i+4$.
\end{proposition}
\begin{proof}
Within each component, the selected adjacencies are precisely its path
edges. The same-face hypotheses exclude every contact between different
components in that face. Opposite-face cube vertices are adjacent exactly
when their projections agree. The intersection hypotheses therefore give
exactly the four intended crossing edges and no others. The ordered
concatenation has no repeated vertex and has precisely its consecutive
adjacencies. Its edge count is the sum of the five component lengths
plus four. Singleton outer components are allowed.
\end{proof}
The indexed constructor underlying this proposition has passed Lean,
using the existing append and layer constructions. This checks the
assembly implication under its compatibility premises. It does not
supply components of the required lengths or certify solver infeasibility.

\paragraph{Joint selection of both faces.}
The chosen 191-edge seed has five consecutive component lengths
\[
46,83,32,13,13,
\]
and face occupancies 94 and 98. Its normalized endpoints are 0 and 88,
and coordinate 8 is the crossing direction. All 512 vertices are
available to a new selection. The target has 193 vertices, four
crossings and endpoint 0; the other endpoint and all four port locations
are variable. At least one original vertex must be removed in each face.
No face occupancy or component-exchanging symmetry is imposed.

A 192-edge path from 0 ends at an even vertex, and four crossings put
that endpoint in the lower face. Its colour counts are 97 even and
96 odd vertices. The old endpoint 88 can remain internally, but cannot
remain the final endpoint. For a selected vertex $v$, the model imposes
\[
\sum_{w\sim v}x_w=2-e_v,\qquad e_v\le x_v,
\]
with exactly two endpoint indicators. The degree equality is imposed
only when $x_v=1$. Each vertical-edge indicator is the conjunction of
its two endpoint selections, and their sum is four. All coordinate
squares exclude selection of all four corners. A disconnected feasible
selection can contain cycle components; each observed cycle is excluded
by requiring at least one of its vertices to be absent. A construction
is accepted only after connectedness and all unordered adjacency pairs
are checked.

\paragraph{Restricted computational results.}
Let $d$ be the number of omitted seed vertices. The new selection must
add $d+1$ vertices because the seed has 192 vertices and the target has
193. The recorded runs are:
\begin{center}
\begin{tabular}{rll}
Maximum $d$ & Native outcome & Seconds\\\hline
TABLE223
\end{tabular}
\end{center}
The four-omission result excludes only the specified seed alignment,
retained endpoint, crossing coordinate and both-face changes. It gives
a computational requirement of at least five omissions in that class,
without a Lean contradiction certificate. Larger unknown queries remain
unresolved. No new snake or global numerical bound is obtained.
Models, execution records, the checked constructor and independent
source reviews are retained in milestone 223~\cite{research223}.

\paragraph{Endpoint-directed construction.}
If a vertex $w$ is the endpoint of an induced path and an adjacent
vertex $u$ is retained, every other neighbour of $w$ must be absent.
Indeed, any selected neighbour occupies the unique preceding path
index. This uniqueness and its exclusion consequence have passed Lean
for actual indexed paths in an irreflexive undirected graph.
For the chosen seed, retaining 88 and making 80 the new endpoint
therefore requires deletion of 208: the exclusive-or differences are
$80\mathbin{\mathrm{xor}}88=8$ and
$80\mathbin{\mathrm{xor}}208=128$, each a single coordinate bit.
Vertex 208 is an old crossing port, so this construction necessarily
changes a port. The twelve-omission query with these endpoint choices
remains unknown after 75 seconds. The generic endpoint result is
checked separately from these elementary coordinate calculations and
the unresolved search.

'''.replace('TABLE223',table)
frontier=r'''\section{Joint construction across four crossings}
The selected constructive route places three paths in one $Q_8$ face
and two in the other. It follows the saved lower-dimensional patterns
\[
18+24+6+2=50,\qquad 8+25+10+25+26+4=98.
\]
The second pattern places 52 vertices in one face as two paths, more
than a single longest $Q_7$ path can occupy. This is why both faces and
their joining endpoints should be optimized together.

Five oriented paths in alternating faces join to an induced path when
consecutive projections meet only at their joining endpoint,
nonconsecutive same-face components are disjoint and nonadjacent, and
nonconsecutive opposite-face projections are disjoint. Indeed, a crossing
edge exists exactly when two projections coincide; these conditions
leave precisely the intended path edges. The resulting length is the
sum of the five lengths plus four. This assembly constructor has now
passed Lean under those premises; existence of large compatible
components is still the main difficulty.

The chosen 191-edge seed has component lengths $46,83,32,13,13$.
Both face selections and all four crossing locations are variable in a
search for 192 edges. Endpoint 0 is retained and the other endpoint is
free. Parity forces the new endpoint to be even, and four crossings
place it in the starting face. Keeping both old endpoints would be
incompatible with the target length.

The native query allowing at most four seed omissions, with at least
one in each face, is infeasible. Thus a successful change in this
restricted class needs at least five omissions and six additions.
This exclusion has no Lean contradiction certificate. The eight- and
twelve-omission queries are unresolved at their recorded time limits;
neither provides an impossibility result. No longer snake has been
obtained. The checked joining theorem and the computational records
have separate scopes~\cite{research223}.

An endpoint-directed variant retains the old endpoint 88 internally
and seeks endpoint 80. Since both 88 and the old crossing vertex 208
are adjacent to 80, vertex 208 must be removed. Otherwise the proposed
endpoint has two selected neighbours. The general endpoint exclusion
argument has passed Lean. The corresponding twelve-omission search
remains unresolved after 75 seconds. This gives a concrete way to
force a crossing change without fixing the rest of either face.

'''
bib=r'''\bibitem{research223}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Joint four-crossing construction
and five-component joining}. Research milestone 223, 15 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/223-coupled-four-crossings}.

'''
records={}
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
    before=(H/'data'/(name+'.before.txt')).read_bytes()
    assert (D/name).read_bytes()==before and (R/'paper'/name).read_bytes()==before
    text=before.decode('utf-8')
    text=once(text,'Research state after round 222','Research state after round 223')
    if name=='snake9_research.tex':
        text=once(text,r'\section{Verification scope and remaining problem}',section+r'\section{Verification scope and remaining problem}')
        text=once(text,'The paper separates written proofs, checked implications, native',
                  'A checked five-component constructor supports a joint four-crossing\nsearch. The first small neighbourhood is computationally excluded;\nlarger neighbourhoods remain unresolved, with no new construction.\n\nThe paper separates written proofs, checked implications, native')
        text=once(text,'The round-220 full-source review corrects historical proof references,',
                  'The five-component assembly in Section~\\ref{sec:coupled223} now\nhas a checked indexed constructor. Its restricted native search results\nretain separate verification limits.\nThe round-220 full-source review corrects historical proof references,')
    else:
        text=once(text,r'\section{Remaining questions}',frontier+r'\section{Remaining questions}')
        text=once(text,'Further construction work can use a different parent isometry class,\na shorter parent with a sufficiently long compatible partner, or multiple\ncrossings.',
                  'The current route varies both faces in a four-crossing construction.\nDifferent parent classes and shorter compatible parents remain alternatives.')
        text=text.replace('milestones through round 222','milestones through round 223')
    text=once(text,r'\end{thebibliography}',bib+r'\end{thebibliography}')
    assert re.search(r'\\author\{[^\n]*',text).group()==re.search(r'\\author\{[^\n]*',before.decode('utf-8')).group()
    if name=='snake9_research.tex':
        assert re.search(r'\\hypersetup\{.*?\n\}',text,re.S).group()==re.search(r'\\hypersetup\{.*?\n\}',before.decode('utf-8'),re.S).group()
    after=text.encode('utf-8')
    (D/name).write_bytes(after); (R/'paper'/name).write_bytes(after)
    records[name]=dict(before_sha256=sha(before),after_sha256=sha(after))
(H/'data/manuscript-edits.json').write_text(json.dumps(records,indent=2)+'\n',encoding='utf-8')
print('UPDATED_EXISTING_SOURCES_AND_MIRRORS')
