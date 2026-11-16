Compilation update: all reports passed the guarded Lean compiler. See data/IsolationDeletion233-audit.json. Preparation-time statements below are historical.

# Locality of repairing an isolated contracted vertex

`IsolationDeletion233.lean` is prepared source with two intended axiom reports. It imports only `Std` and has not been compiled. No compiler, solver, or tests were run. The accepted or currently compiling parity-lift source was not changed.

## General preservation lemma

Let (C(y,x)) mean that label (y) is adjacent to selected vertex (x). The label type may differ from the selected-vertex type. Let (S'\subseteq S) be the retained and original selected sets.

A contracted edge between distinct vertices (x,z) is witnessed by a label (y) whose complete selected-neighbour set is exactly (\{x,z\}). The Lean statement expresses this by

\[
\forall v,\quad \bigl(v\in S'\ \text{and}\ C(y,v)\bigr)
\quad\Longleftrightarrow\quad v=x\ \text{or}\ v=z.
\]

This includes membership of both endpoints and both required adjacencies. It excludes any third selected neighbour.

The first proposed theorem assumes that every old selected neighbour of (y) is retained. Any old neighbour is then covered by the displayed equivalence, while any endpoint belongs to the old set because (S'\subseteq S). Thus exactly the same label already witnessed the same edge before deletion.

The second theorem assumes that (x) has no contracted-edge witness in (S), and that for every label (y) incident to (x), all of (y)'s old selected neighbours are retained. An alleged contracted edge at (x) after deletion supplies such a label. The first theorem transfers its exact two-neighbour witness back to (S), contradicting isolation.

The conclusion rules out all edges incident to (x). When (x\in S'), it states that (x) remains isolated in the retained contracted graph. If (x\notin S'), the witness is already impossible because it requires endpoint membership. No metric, finite cardinality, graph traversal, or assumed Hamiltonian obstruction is hidden in the Lean premises.

## Radius-two consequence for the parity lift

For the parity lift, take the base graph to be undirected and

\[
C(y,x)\quad\Longleftrightarrow\quad y=x\ \text{or}\ R(y,x).
\]

If (C(y,x)) and (C(y,v)), then (x) and (v) are joined in the base graph by a walk of at most two edges, through (y), allowing either edge to have length zero. Symmetry supplies the reversed first edge. Consequently, if no deleted vertex is within base distance two of (x), every old selected neighbour of every label incident to (x) is retained. The general preservation lemma applies.

Let (I) be the set of initially isolated vertices of the contracted graph on (S), and let (D\subseteq S) be deleted. Suppose the retained contracted graph has a Hamiltonian path and at least two vertices. It has no isolated retained vertex. Every (x\in I) must therefore lie within distance two of some (d\in D). This includes a deleted (x), since its distance from itself is zero. The assumption of at least two retained vertices is essential: a singleton graph has a Hamiltonian path despite its lone vertex being isolated.

This radius-two translation and the Hamiltonian-path consequence are written deductions here. The new Lean source proves the general local-retention argument, without a distance library or an extraction of the cube's radius-two sets.

## Hitting-set consequences

For each initially isolated (x), its possible repair deletions are the allowed deletion candidates within distance two of (x). A successful deletion set must meet every such set. If (t) of these repair sets are pairwise disjoint, at least (t) deletions are necessary. An empty repair set excludes the entire permitted deletion family immediately.

Counting incidences between initially isolated vertices and deletions gives

\[
|I|\leq\sum_{d\in D}|I\cap B_2(d)|.
\]

In particular, for a nonempty finite deletion set of size (r),

\[
|I|\leq r\max_{d\in D}|I\cap B_2(d)|.
\]

A uniform bound $q$ over all allowed deletion candidates yields the necessary condition $|I|\leq rq$, including the empty-deletion case. These are finite counting consequences of coverage; overlapping repair sets can make the bound weak. They do not claim that deleting a nearby vertex repairs isolation, or that removing all isolated vertices suffices for a Hamiltonian path.

Finite certificates must separately verify the complete original contracted graph, its isolated set, the permitted deletion candidates, and the closed radius-two memberships used in the bound. The witness-transfer lemma remains valid for a restricted label collection only when the same collection is used before and after deletion, or every later label is included in the earlier isolation statement. Adding previously unconsidered labels after deletion would invalidate that premise. No numerical experiment or certificate is asserted by this source preparation.

## Universal scope of the closed-neighbour construction

Every even-parity vertex of $Q_{n+1}$ is uniquely of the form $(x,\operatorname{parity}(x))$. Its last bit is forced by its first $n$ bits. Consequently every subset of that parity class is the parity lift of a unique arbitrary set $S\subseteq Q_n$. An odd-parity subset can be moved to this representation by flipping the last coordinate of the entire cube.

For $k\geq1$, an induced path of $2(k-1)$ edges has $k$ vertices in its endpoint parity class and $k-1$ in the other class. After the possible coordinate flip, project the endpoint class to a $k$-set $S$. Every intervening label has exactly its two path neighbours in the selected endpoint class, since any additional selected neighbour would be a chord. The exact parity-lift adjacency identity therefore gives a labelled Hamiltonian path in the closed-neighbour contraction on $S$.

Conversely, such a Hamiltonian path lifts to an induced path of $2(k-1)$ edges by the accepted colour-contraction constructor, with the exact selected-neighbour and distinct-label conditions. If the contracted graph records a physical label for each edge, a simple Hamiltonian path cannot reuse a label: each label has one fixed unordered pair of selected neighbours, while the consecutive unordered pairs of an injective Hamiltonian ordering are distinct. The case $k=1$ gives a singleton path and needs no labels.

Thus the closed-neighbour Hamiltonian criterion is universal when $S$ ranges over arbitrary $k$-subsets of $Q_n$. Restricting $S$ to an old induced base path with deletions is the extra constraint in the current experiments. Failure of that restricted family does not exclude arbitrary sets or the target snake length. This equivalence and the parity-class representation are written arguments here; the new deletion module establishes only the general locality implication.

The parent reported separate native audit counts of 69 initially isolated vertices with at most 17 covered by one allowed deletion for the saved $Q_8$ parent, 37 with at most 12 for the saved $Q_7$ parent, and 10 with at most 6 for the saved $Q_6$ parent. Substitution in the incidence inequality requires at least 5, 4, and 2 deletions respectively. These are necessary counts, not sufficient constructions. Their finite graph and radius-two certificates are owned by the separate audit; this preparation did not independently verify those arrays. The parent also reported three pairwise disjoint repair sets for vertices 7, 40, and 91 of the saved $Q_8$ parent, giving a separate three-deletion obstruction.
