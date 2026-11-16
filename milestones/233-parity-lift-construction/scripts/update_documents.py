from pathlib import Path
H=Path(__file__).resolve().parents[1];R=H.parents[1];D=Path('D:/Codex/2026-10-13/new-chat/outputs')
def once(s,a,b):
    assert s.count(a)==1,a[:100]
    return s.replace(a,b,1)
main=(D/'snake9_research.tex').read_text(encoding='utf-8')
short=(D/'snake9_frontier_explanation.tex').read_text(encoding='utf-8')
main=once(main,'Research state after round 232, 16 November 2026','Research state after round 233, 16 November 2026')
main=once(main,'finite evidence.\n\nWritten proofs,','finite evidence. A parity lift gives a universal closed-neighbour\nconstruction criterion, while a local deletion obstruction excludes\nnear-doubling by deleting from the saved parents of lengths 26, 50 and 98.\n\nWritten proofs,')
section=r'''\subsection{Parity lift and the limits of deleting from one base path}
\label{sec:parity233}
Let $c(x)$ be the parity of $x\in Q_n$ and let $N[y]$ denote its closed
neighbourhood. For $S\subseteq Q_n$, select
$U=\{(x,c(x)):x\in S\}$ in $Q_{n+1}$. These vertices have even parity.
Every odd vertex is uniquely $(y,1-c(y))$, whose neighbours in $U$
project exactly to $N[y]\cap S$. Equality of the base vertices gives
a vertical edge; base adjacency gives an edge within one face.

\begin{proposition}\label{prop:projection233}
For $k\ge2$, a snake of $2k-2$ edges exists in $Q_{n+1}$ if and only if
some $k$-vertex subset $S\subseteq Q_n$ has a Hamiltonian path in the
graph whose labelled edges are the two-element sets $N[y]\cap S$.
\end{proposition}
\begin{proof}
Each such Hamiltonian ordering lifts by inserting the indicated odd
labels. Distinct consecutive pairs cannot reuse one label, whose
selected-neighbour pair is fixed. Both lifted parity classes are
independent, and every label has exactly its intended two neighbours.
Thus Proposition~\ref{prop:colour231} gives an induced path of $2k-2$
edges. Conversely, an even-length snake has $k$ vertices in its endpoint
parity class. Flip the last coordinate if that class is odd. Every even
vertex $(x,b)$ satisfies $b=c(x)$, so projection is injective on the
class and gives a $k$-set $S$. Its intervening odd vertices supply exactly
the required labelled Hamiltonian path.
\end{proof}

In particular, a 192-edge snake in $Q_9$ is equivalent to a suitable
97-set in $Q_8$. The Hamiltonian requirement retains the full difficulty
of the existence problem. The representation is universal; restricting
$S$ to vertices of one old induced path is an additional hypothesis.
The map $x\mapsto(x,c(x))$ is not a cube isometry.

If the base path has $m$ edges and $r$ vertices are deleted, a successful
lift would have $2m-2r$ edges. The numerical pattern with $r=1$ gives
$26\to50$, $50\to98$ and $98\to194$; $r=0$ and $r=2$ would give 196 and
192 from a 98-edge parent. The complete zero-, one- and two-deletion
survey used the saved parents of lengths 13, 26, 50 and 98. Its 6763
cases comprise 6698 isolated-vertex exclusions, 27 excess-leaf
exclusions, two disconnected graphs, eight native infeasible queries,
and 28 verified paths. Those paths all lie in $Q_6$: two have 24 edges
and 26 have 22. All 6657 cases from the parents in dimensions 6, 7 and 8
have an isolated vertex. These are complete covers of the four saved
parents, with no exhaustive claim over other parent paths~\cite{research233}.

\begin{lemma}\label{lem:deletion233}
Let $I$ be the isolated vertices of the closed-neighbour contraction on
a base set $P$. If deleting $D\subseteq P$ leaves a Hamiltonian
contraction with at least two vertices, then
\[
 I\subseteq\bigcup_{d\in D} B_2(d),\qquad
 |I|\le\sum_{d\in D}|I\cap B_2(d)|,
\]
where $B_2(d)$ is the Hamming ball of radius two in the base cube.
\end{lemma}
\begin{proof}
Consider $x\in I$ outside every displayed ball. It is retained. A label
$y$ incident to $x$ lies in $N[x]$, so every vertex of $N[y]$ is within
distance two of $x$. None is deleted. Its selected-neighbour set is
unchanged and cannot become a two-element set incident to $x$.
Therefore $x$ remains isolated, contrary to a Hamiltonian path on at
least two vertices. The cardinality inequality follows by counting
the covering incidences; overlaps can only increase the sum.
\end{proof}

The saved $Q_8$ parent has $|I|=69$, and each allowed deletion covers
at most 17 members of $I$. Four deletions cover at most $68<69$, so
at least five are necessary. Its entire deletion-only lift family has
length at most $196-10=186$. For the saved $Q_7$ parent, the corresponding
counts 37 and 12 require at least four deletions and give a restricted
ceiling of 92. For the saved $Q_6$ parent, any pair of deletions covers
at most nine of ten initially isolated vertices; at least three are
required, giving a restricted ceiling of 46. These necessary conditions
do not assert attainability or bound arbitrary snakes in the larger cubes.

A retained label is eligible exactly when it has one retained base
neighbour. For an induced base path these labels are the ends of
nonsingleton retained components. There are at most $r+1$ components
after $r$ deletions, hence at most $2(r+1)$ eligible retained labels.
Each used retained label contributes one vertical crossing, while
labels outside the retained set contribute none. The resulting lifts
therefore have at most $2(r+1)$ crossings.

Four new checked statements establish exact lift adjacency, injection
and disjointness, independence, and the retained-label characterization.
Two further checked statements establish transfer of an unchanged
two-neighbour witness and preservation of isolation. Cube projection,
radius-two interpretation, incidence counting and the component bound
remain written bridges. Independent finite reconstruction covered all
6763 graphs, all 36 circuit models and all 28 witnesses. The eight native
infeasibility reports were not replayed as Lean certificates.

The next constructive family replaces one vertex of a saved minority
class, with its opposite class and ordering free. It has not been
searched. This permits additions outside the old base path while
retaining the exact contraction criterion.

'''
main=once(main,r'\section{A numerical conjecture and its limitations}',section+r'\section{A numerical conjecture and its limitations}')
marker='Full-source reviews at rounds 220 and 230 check the written argument,'
main=once(main,marker,r'''Section~\ref{sec:parity233} adds six checked general lift and local-deletion
statements. Its whole-cube and counting bridges remain written, and
the four-parent finite cover retains its native verification scope.
'''+marker)
short=once(short,'Research state after round 232','Research state after round 233')
short=once(short,'The next route allows one vertex of the minority class to change, with\nthe other class still free. This enlarged family has not been exhausted.','A possible next route replaces one vertex of the minority class, with\nthe other class still free. This family has not been searched. The\nfollowing round first examines a smaller family built from old paths.')
section=r'''\section{Why the simple dimensional lift fails}
Project the even vertices of $Q_9$ onto their first eight coordinates.
The missing bit is forced by parity, so every chosen even class is
equivalent to a subset $S\subseteq Q_8$. An odd vertex over $y$ sees
exactly the selected vertices in the closed neighbourhood $N[y]$.
Whenever $N[y]\cap S$ has exactly two vertices, join them by an edge
labelled $y$. A Hamiltonian path, which visits every vertex of $S$
once, then lifts to a snake of $2|S|-2$ edges. Extra adjacencies are
excluded by the exact two-neighbour condition. Conversely, every
even-length snake has this representation, after a coordinate flip
if needed. Thus 192 edges are equivalent to finding a suitable
97-vertex subset of $Q_8$.

One proposed source of $S$ was an old $m$-edge snake with $r$ vertices
deleted. It would give $2m-2r$ edges. With $r=1$ the arithmetic reproduces
$26\to50$ and $50\to98$, then predicts $98\to194$ if the required path
exists. The full survey of zero, one and two deletions found that every
case from the saved 26-, 50- and 98-edge parents has an isolated vertex
in its contraction. Such a vertex cannot belong to a Hamiltonian path
with other vertices. The numerical pattern therefore does not describe
this construction for those parents.

There is also a short explanation that covers more deletions. An
initially isolated vertex can change only if a vertex within Hamming
distance two is deleted; otherwise every potentially useful label sees
the same selected neighbours. For the saved 98-edge parent, 69 vertices
are initially isolated, and one deletion can affect at most 17 of them.
Four deletions cover at most $4\cdot17=68$. Hence at least five are
necessary, so this entire family has length at most $196-10=186$.
For the saved 50- and 26-edge parents, corresponding finite covering
arguments require at least four and three deletions respectively.
These are restrictions on specific construction families; they do not
give upper bounds for arbitrary snakes~\cite{research233}.

Six new general Lean statements support the lift and local-deletion
arguments. The whole-cube projection and counting bridges are written
proofs. The independent finite audit checked all 6763 graphs, 36 circuit
models and 28 successful shorter witnesses. Eight native infeasibility
reports remain separate from Lean. No longer $Q_9$ snake was found.
The useful next family allows additions as well as deletions in a saved
parity class, while leaving the opposite class and ordering free.
Research pauses after round 233.

'''
short=once(short,r'\section{Remaining questions}',section+r'\section{Remaining questions}')
short=once(short,'milestones through round 232','milestones through round 233')
bib=r'''\bibitem{research233}
I.~Hironaka, T.~Ma, and S.~Zhan. \emph{Parity lift and deletion obstruction}.
Research milestone 233, 16 November 2026.
\url{https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/main/milestones/233-parity-lift-construction}.

'''
for name,text in [('snake9_research.tex',main),('snake9_frontier_explanation.tex',short)]:
    text=once(text,r'\end{thebibliography}',bib+r'\end{thebibliography}')
    p=D/name;p.write_text(text,encoding='utf-8',newline='\n');(R/'paper'/name).write_bytes(p.read_bytes())
    print('UPDATED',name)
for note,module in [('parity-lift-proof.md','ParityLift233'),('isolation-deletion-proof.md','IsolationDeletion233')]:
    p=H/'logs'/note
    p.write_text(f'Compilation update: all reports passed the guarded Lean compiler. See data/{module}-audit.json. Preparation-time statements below are historical.\n\n'+p.read_text(encoding='utf-8'),encoding='utf-8',newline='\n')
