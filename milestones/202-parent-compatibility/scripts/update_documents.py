from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1]
EDITOR=Path('D:/Codex/2026-10-13/new-chat/outputs')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,s):p.write_bytes(s.replace('\r\n','\n').encode('utf-8'))

section=r'''
\subsection{Controlled reflections of the whole snake}
\label{sec:controlled202}
An automorphism of a finite snake is either identity
or reversal: an endpoint has only two possible images, and distance
along the path from that endpoint determines every other image.
A transformation into a different cube embedding allows more freedom.
The following map acts on every selected vertex and has an exact
criterion preserving every pair relation of the entire snake.

Choose two coordinates and write a cube vertex as $(z,u)$, where
$z\in Q_{n-2}$ and $u\in\{00,01,10,11\}$. For
$\epsilon\in\{0,1\}$, let $\tau_\epsilon$ interchange the two
words of parity $\epsilon$ and fix the other two. Thus $\tau_1$
exchanges $01,10$, while $\tau_0$ exchanges $00,11$; both are square
reflections. For a Boolean function $f$ on $Q_{n-2}$, define the
\emph{controlled square reflection}
\[
F_f(z,u)=(z,\tau_\epsilon^{f(z)}(u)).
\]
It is an involution on the entire cube, although it need not preserve
the entire cube graph. Controlled swaps already occur in reversible
logic, including the Fredkin gate~\cite{fredkin}; no historical novelty
is claimed for the operation.

\begin{theorem}[Whole-snake preservation criterion]
\label{thm:controlled202}
For a selected set $S\subseteq Q_n$, let $B$ be the set of base words
$z$ for which some $(z,u)\in S$ has $u$ of parity $\epsilon$.
The map $F_f$ preserves adjacency and nonadjacency for every pair
in $S$ if and only if $f$ is constant on each connected component
of $Q_{n-2}[B]$. Under this condition, an ordered snake
$(v_0,\ldots,v_L)$ maps to the snake $(F_f(v_0),\ldots,F_f(v_L))$.
\end{theorem}
\begin{proof}
In a common base fibre, both vertices receive the same square isometry.
Distinct base fibres at distance at least two cannot supply an edge.
Across neighbouring base words $z,w$, adjacency means that the two-bit
words agree. Equal selectors preserve this equality. Different selectors
reverse it whenever both words have parity $\epsilon$, since there are
only two such words and the reflection interchanges them. Words of
different parities cannot become equal, and both inactive words are fixed.
Thus a pair relation changes exactly when neighbouring members of $B$
receive different selectors. Constancy on edges is equivalent to constancy
on components. Involutivity also preserves distinctness of all vertices.
\end{proof}

The active base set $B$ does not change under these maps. A subset
of its components can therefore be selected for reflection, and
composition takes the symmetric difference of the chosen subsets.
Reflecting all components agrees on $S$ with the ordinary global
square reflection. Complementary subsets give cube-isometric images.
If $B$ has at most three components, the unchanged image and the
single-component images consequently cover all choices up to cube
isometry. At four components, choices of two components require
additional consideration.

If this controlled map preserves the same snake as a set and acts
nontrivially, it agrees on that snake with the global square reflection.
Indeed, its restriction must be reversal. Every moved vertex changes
exactly two bits, so an even number of vertices is impossible: reversal
would exchange the adjacent middle pair. With an odd number of vertices,
every noncentral vertex moves and hence lies on the active diagonal.
The two neighbours of the centre are exchanged and share a base word.
Their common cube neighbours lie on the inactive diagonal, so the
centre is also fixed by the global reflection. The two maps therefore
agree on every selected vertex. This distinguishes a new embedding
from an additional intrinsic symmetry of the same snake.

\paragraph{A concrete whole-snake transformation.}
The two 13-edge $Q_5$ paths
\[
\begin{split}
P={}&(0,1,3,7,15,14,10,26,18,22,20,28,29,25),\\
P'={}&(0,1,3,7,15,14,10,26,18,22,20,21,29,25)
\end{split}
\]
are related by the controlled reflection in coordinates 0 and 3,
with $\epsilon=1$ and the single active base component encoded by 20.
It exchanges 21 with 28 and fixes the other $Q_5$ vertices.
Both complete paths and the positionwise image relation pass Lean.
The Hamming-distance matrices disagree under both forward and reversed
alignment, also checked in Lean, so the two paths are not cube-isometric.
For example, the distance between positions 1 and 11 changes from four
to two. Preservation of the whole path does not require preservation
of every Hamming distance.

\paragraph{Consequences for the saved parents and witness bank.}
The native census examines every coordinate pair and both diagonal
parities. All active graphs are connected for the saved $Q_6$, $Q_7$
and $Q_8$ representatives, over 30, 42 and 56 choices respectively.
Every admissible map in this family therefore acts on each of those
snakes as identity or a global square reflection. This conclusion is
restricted to those representatives.

For the 131 saved 191-edge $Q_9$ snakes, the 9432 pair/parity choices
give 9248 connected active graphs, 144 graphs with two components and
40 with three. Their 408 single-component images represent 111 cube
isometry classes, all already in the saved bank. Every resulting path
was checked in full by the native calculation.

These finite results imply closure of the bank's cube-isometry classes
under arbitrary iterations of the controlled reflections. Complementary
subsets cover every one-step choice because there are at most three
components. Cube isometries transport the move family: a coordinate
permutation transports the selected pair, and a translation in one
chosen coordinate exchanges the two parity cases. Both cases were
included. Thus each step remains in the bank's classes, and induction
handles any finite number of steps, with changing coordinate pairs.
This is no classification of all 191-edge snakes and no global bound.

Lean checks the preservation criterion in an arbitrary product graph
$G\square Q_2$, constructs the whole image path, and checks the
composition, complement and compatibility deductions. The concrete
census remains native. Its closure consequence additionally uses the
written component and equivariance arguments above; no full-bank Lean
replay is claimed. Exact inputs and evidence are in~\cite{research202}.

\paragraph{A sharper parent restriction.}
For the 195-edge, three-crossing predecessor in
Section~\ref{sec:crossing-deletion201}, one internal vertex must be
omitted from each 98-edge parent: the three crossings leave exactly
two components in each face. If their deletion indices are $i,j$,
and their base-colour imbalances are $\delta_P,\delta_Q\in\{-1,1\}$,
the final colour balance gives
\[
\delta_P(1-(-1)^i)=\delta_Q(1-(-1)^j).
\]
Hence $i,j$ have equal parity; if odd, the parent endpoints have the
same base colour. In the saturated $C=5$ one-addition case, the new
endpoint attaches at an original endpoint of one parent. Both exposed
neighbours of its omitted vertex are then crossing ports. The retained
opposite copy of that omitted vertex joins them into an entire two-edge
component in the other face. That other parent's deletion index is
therefore 3 or 95. Both indices are odd and the parent endpoint colours
agree. This is a written geometric deduction; its complete Lean assembly
and existence of the construction remain open.

'''

front=r'''
\paragraph{A symmetry acting on the whole snake.}
Choose two coordinates, write a vertex as $(z,u)$, and let
$\tau_\epsilon$ interchange the two square words of parity
$\epsilon$, fixing the other two. For a Boolean selector $f$, define
\[
F_f(z,u)=(z,\tau_\epsilon^{f(z)}(u)).
\]
This is a single involution defined on every cube vertex. For a snake,
collect the base words $z$ having a selected word of parity $\epsilon$.
Then $F_f$ preserves every edge and every nonedge of the entire snake
exactly when $f$ is constant on each component of the cube graph on
those base words. The reason is that a selector change across adjacent
base words reverses equality of the two active square words, changing
an edge into a nonedge or conversely. All other pairs keep their status.
Lean checks this criterion and constructs the full induced image path.

The components can be reflected independently. Reflecting a subset or
its complement gives images related by a global square reflection.
With at most three components, the unchanged image and the individual
component images therefore cover every choice up to cube isometry.
A checked 13-edge $Q_5$ example changes one selected vertex and gives
a whole snake inequivalent under cube isometries, including reversal.

The saved 98-edge $Q_8$ parent has a connected active graph for all
56 coordinate-pair/parity choices. This particular family therefore
cannot change its shape beyond ordinary cube symmetries.
For the 131 saved 191-edge $Q_9$ snakes, all 9432 choices have at most
three components. The 408 single-component images all belong to the
existing bank. Complement symmetry and invariance under cube isometries
then imply closure under arbitrary iterations of these maps. These
finite census premises remain native computations.

A self-symmetry preserving the same finite snake as a set is identity
or reversal. Within this controlled-reflection family, a nontrivial
self-map agrees on the whole snake with a global square reflection.
More varied embeddings are possible, as the checked example shows.
Thus the definition is useful, but this family does not escape the
saved $Q_9$ bank or produce a new $Q_8$ parent from the saved one.

The parent analysis also sharpens the saturated $C=5$ case above.
The 195-edge predecessor has one omission in each parent. Their indices
have equal parity. In the one-addition case with $C=5$, at least one
omission lies exactly three edges from an original parent endpoint,
so its index is 3 or 95. Both indices are odd. The short reason is
that the two exposed ports and the retained opposite copy of the
omitted vertex form a complete two-edge component in the other face.
This last conclusion has a written proof and remains necessary only.

'''
records={}
for name in ['snake9_research.tex','snake9_frontier_explanation.tex']:
    p=EDITOR/name;mirror=R/'paper'/name;assert p.read_bytes()==mirror.read_bytes()
    s=p.read_text(encoding='utf-8');before=sha(p)
    author=re.search(r'\\author\{[^\n]*\}',s).group();hyper=re.search(r'\\hypersetup\{.*?\n\}',s,re.S)
    if name=='snake9_research.tex':
        anchor=r'\section{Construction experiments and their scope}\label{app:experiments}'
        assert s.count(anchor)==1 and 'sec:controlled202' not in s
        s=s.replace(anchor,section+anchor)
        anchor='and sharply restricts such constructions of a 196-edge snake.\n'
        assert s.count(anchor)==1
        s=s.replace(anchor,anchor+'Controlled square reflections give a whole-snake preservation criterion\nand a checked example beyond cube isometry. Their native census also\nidentifies a closed family within the saved 191-edge witness bank.\n')
        bib=r'''\bibitem{fredkin}
E. Fredkin and T. Toffoli,
\emph{Conservative Logic}, International Journal of Theoretical Physics
21 (1982), 219--253, Section 2.
\url{https://doi.org/10.1007/BF01857727}.
\bibitem{research202}
I. Hironaka, T. Ma and S. Zhan,
\emph{Controlled reflections and whole-snake compatibility},
research record 202, 14 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/202-parent-compatibility}.
'''
        s=s.replace(r'\end{thebibliography}',bib+r'\end{thebibliography}')
    else:
        s=s.replace('Research state after round 201','Research state after round 202')
        s=s.replace('research records 175--201','research records 175--202')
        anchor=r'\textbf{7. What is proved, and what remains.}'
        assert s.count(anchor)==1
        s=s.replace(anchor,front+anchor)
    assert author in s
    if hyper:assert hyper.group() in s
    write(p,s);mirror.write_bytes(p.read_bytes())
    records[name]=dict(before_sha256=before,after_sha256=sha(p),editor=str(p),mirror=str(mirror),identical=True,author_preserved=True,hypersetup_preserved=True)
write(H/'data/document-edits.json',json.dumps(records,indent=2)+'\n')
print('UPDATED_BOTH_EXISTING_DOCUMENTS')
