from pathlib import Path
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def once(s,a,b):
    assert s.count(a)==1,a[:100]
    return s.replace(a,b,1)
main=(D/'snake9_research.tex').read_text(encoding='utf-8');short=(D/'snake9_frontier_explanation.tex').read_text(encoding='utf-8')
main=once(main,'Research state after round 230, 16 November 2026','Research state after round 231, 16 November 2026')
main=once(main,'the scope of its checked components are stated separately.','the scope of its checked components are stated separately. A contraction\nof one parity class gives an exact Hamiltonian-path construction criterion\nand excludes all 97-vertex majority classes obtained by enlarging one\nparity class of the saved seed bank.')
main=once(main,r'Sections~\ref{sec:replacement225}--\ref{sec:facevisits230} give the',r'Sections~\ref{sec:replacement225}--\ref{sec:colour231} give the')
addition=r'''\subsection{Contracting a fixed parity class}\label{sec:colour231}
The preceding replacement family retains much of the original order.
A different reduction permits complete reordering and unrestricted changes
to the other parity class.

\begin{proposition}\label{prop:colour231}
Let $U$ be a nonempty set in one parity class of $Q_n$. Form a labelled
graph on $U$: each opposite-parity vertex $z$ with exactly two neighbours
in $U$ labels an edge joining those neighbours. There is an induced path
whose vertices in the first parity class are exactly $U$ and whose two
endpoints lie in $U$ if and only if this graph has a Hamiltonian path.
The induced path has $2|U|-2$ edges.
\end{proposition}
\begin{proof}
An induced path of the required kind alternates between $U$ and the
opposite class. Each intervening vertex is adjacent to its predecessor
and successor in $U$, and to no other member of $U$, since an additional
adjacency would be a chord. The order of $U$ therefore gives a Hamiltonian
path in the labelled graph.

Conversely, interleave a Hamiltonian ordering of $U$ with the labels of
its successive edges. A physical label cannot repeat: its unordered pair
of neighbours is fixed, whereas a simple Hamiltonian path cannot use
the same pair twice. The interleaving has distinct vertices. Same-parity
pairs are nonadjacent, and the exact neighbour condition for each label
permits only consecutive cross-parity adjacencies. It is therefore induced.
There are $|U|$ first-class vertices and $|U|-1$ labels. For $|U|=1$,
the singleton path gives the same conclusion.
\end{proof}

Parallel labels may be collapsed for the Hamiltonian existence question:
any one label for a selected pair has the same neighbour relation within
$U$. Lean checked the indexed interleaving constructor and converse
statements about exact adjacency, injectivity, disjointness and
same-parity nonadjacency. Identifying the cube colour classes and
generating the finite graphs remain separate steps.

For a constructive target of 192 edges, take a 96-vertex parity class
from a saved 191-edge seed and add one same-parity vertex. All 131 saved
seeds were checked. Their 262 parity classes give 145 distinct labelled
sets. Each admits 160 possible additions, giving 23,200 descriptions,
23,127 distinct 97-vertex sets, and 73 exact duplicates. No claim of
complete isometry reduction is made. Their associated simple graphs have
17,271 isolated-vertex obstructions and 5,807 cases with more than two
degree-one vertices. A Hamiltonian path cannot satisfy either condition.

All 49 surviving graphs are natively infeasible in a circuit model with
one mandatory dummy vertex. Removing that vertex from a circuit through
every vertex is exactly a Hamiltonian path. Independently reconstructed
graphs and models agree with the saved coverage and outcomes. In 34 cases,
a separator $S$ of size one or two leaves more than $|S|+1$ components,
which is impossible after deleting $S$ from a Hamiltonian path. Eleven
more have endpoint-sensitive separator certificates: graph leaves force
the two endpoints, and either endpoint deletion reduces the available
path-piece count or their common component requires two separate pieces.
These give written elementary explanations of 45 cases. The remaining
four retain their native solver evidence; the finite certificates and
solver contradictions are outside the checked constructor.

Thus the specified 97-vertex majority classes cannot occur in a
192-edge snake. Endpoints, order, coordinate crossing counts and the
opposite vertex class were free throughout this search. The conclusion
does not exclude retaining a 96-vertex \emph{minority} class: then the
opposite class contains both endpoints, which have exactly one neighbour
in the fixed class. That distinct construction case is the next target.
No longer snake or global bound follows~\cite{research231}.

'''
main=once(main,r'\section{A numerical conjecture and its limitations}',addition+r'\section{A numerical conjecture and its limitations}')
marker='Full-source reviews at rounds 220 and 230 check the written argument,'
main=once(main,marker,r'''Section~\ref{sec:colour231} adds four checked interleaving and converse
results and a native majority-class survey. Its graph extraction,
separator certificates and numerical exclusions retain the stated limits.
A bounded review of contributor revision \texttt{5309471b} finds a
231-target chain whose arithmetic is $4763m\le1104764$, but its inspected
interface retains plain/H8, share, contextual-refutation and floor
premises. No completed unconditional 231 final assembly or final theorem
audit was found in that review~\cite{research231}; the maintained interval
is unchanged.
'''+marker)
short=once(short,'Research state after round 230','Research state after round 231')
section=r'''\section{Reorder one colour class freely}
Cube vertices have even or odd parity according to their number of one
bits. Neighbours always have different parity. Choose a set $U$ of one
parity. Each opposite-parity vertex with exactly two neighbours in $U$
can act as a connection between those two vertices.

Make a graph of these connections on $U$. A path visiting every vertex
of this graph exactly once, a Hamiltonian path, expands into a snake by
inserting the corresponding connection vertex between each pair.
There are no chords: each inserted vertex has precisely its two intended
neighbours in $U$, and same-parity vertices are never adjacent.
Conversely, every snake with both endpoints in $U$ and this exact parity
class gives such an ordering. The resulting length is $2|U|-2$.
Lean checked the general interleaving construction and converse adjacency
and distinctness statements. The finite cube-data extraction remains separate.

For 192 edges, $|U|=97$. The 131 saved 191-edge snakes have 145 distinct
96-vertex parity classes. Adding every possible new same-parity vertex
gives 23,127 distinct candidate sets. Simple degree obstructions remove
23,078, leaving 49 associated graphs. All 49 Hamiltonian searches are
infeasible. Small separators give additional elementary explanations for
45 of them: deleting a few vertices leaves too many disconnected pieces
for a single path, sometimes after accounting for its forced endpoints.
The four remaining cases retain their native solver evidence.

This excludes every candidate whose 97-vertex majority class contains
one entire saved 96-vertex class. It allows a completely new order,
new endpoints and unrestricted opposite-parity vertices. Keeping the
96-vertex minority class is a different case: its opposite-parity
endpoint vertices need only one neighbour in the fixed class. That case
remains the next construction target~\cite{research231}.

'''
short=once(short,r'\section{Remaining questions}',section+r'\section{Remaining questions}')
old='A useful next preparation is to compare extension endpoints across\ninequivalent seeds and count the retained vertices that conflict with\neach extension. Fewer or more closely placed conflicts may require less\nstructure to change; this expectation is unproved. Wider blocks and\nchanged block lengths remain construction choices.'
short=once(short,old,'The parity-class comparison above supplies a broader exclusion while\nleaving the fixed-minority construction open. Wider blocks, changed\nblock lengths and changes to both colour classes remain possible.')
short=once(short,'milestones through round 230','milestones through round 231')
bib=r'''\bibitem{research231}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Parity-class contraction and
Hamiltonian construction searches}. Research milestone 231,
16 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/231-endpoint-exchanges}.

'''
for name,text in [('snake9_research.tex',main),('snake9_frontier_explanation.tex',short)]:
    text=once(text,r'\end{thebibliography}',bib+r'\end{thebibliography}')
    p=D/name;p.write_text(text,encoding='utf-8',newline='\n');(R/'paper'/name).write_bytes(p.read_bytes());print('UPDATED',name)
note=H/'logs/colour-contraction-proof.md';s=note.read_text(encoding='utf-8')
s='Compilation update: the saved source passed the guarded Lean compiler with four standard-axiom reports. See data/ColourContraction231-audit.json. The preparation-time statements below are historical.\n\n'+s
note.write_text(s,encoding='utf-8',newline='\n')
