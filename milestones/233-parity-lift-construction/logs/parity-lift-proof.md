Compilation update: all reports passed the guarded Lean compiler. See data/ParityLift233-audit.json. Preparation-time statements below are historical.

# Parity lift and its contracted graph

`ParityLift233.lean` is prepared source with four intended axiom reports. It has not been compiled. No compiler, solver, or tests were run, and no older source was changed. The only research import is the accepted `LayerJoining` adjacency definition.

## Exact adjacency

Let (R) be a base adjacency relation with a proper Boolean colouring (c): an edge implies different colour values. Put a selected base vertex (x) at ((x,c(x))), and use the opposite label ((y,\neg c(y))) for a base vertex (y). Then

\[
\operatorname{LayerAdj}\bigl((y,\neg c(y)),(x,c(x))\bigr)
\quad\Longleftrightarrow\quad y=x\ \text{or}\ R(y,x).
\]

If (y=x), the two lifts have different last coordinates and form a vertical edge. If (R(y,x)), proper colouring gives (c(x)=\neg c(y)), so the lifts lie in the same face and inherit the base edge. Conversely, the product adjacency definition has only these two cases. The proposed first theorem proves this identity for a general proper Boolean colouring, without assuming symmetry or cube geometry.

The two lift maps are injective and have disjoint images. Proper colouring also makes each image an independent set: a same-face edge would require equal colours on a base edge, and a vertical edge within one image would require equal base vertices with different values of the same colouring. These are the second and third proposed theorems.

For cube parity, the selected lifts all have even total parity, and the opposite labels all have odd total parity. The map (x\mapsto(x,c(x))) is not a cube isometry. In particular, adjacent base vertices have lifted distance two. The construction uses its exact label adjacency above.

## The finite construction to verify

Let (P) be an induced base path of (m) edges, and delete a set (D\subseteq V(P)) of (r) vertices. Write (S=V(P)\setminus D). The chosen lifted class has (m+1-r) vertices. Each opposite label (y) sees exactly

\[
\bigl(\{y\}\cup N(y)\bigr)\cap S
\]

under projection. A label is eligible as an internal contracted edge precisely when this set has two distinct vertices. Build the labelled multigraph using these exact two-neighbour sets; different labels may produce parallel edges.

A Hamiltonian path in this graph, with distinct physical labels, lifts by the accepted colour-contraction constructor to an induced path of

\[
2(m+1-r)-2=2m-2r
\]

edges. The class independence and disjointness proved here supply the corresponding generic premises. Exact label neighbour sets, the Hamiltonian ordering, and label distinctness still have to be supplied. In particular, the numerical equalities

\[
2\cdot26-2=50,\qquad 2\cdot50-2=98
\]

do not establish that the historical longer snakes arise from this lift. They motivate finite checks of the specified construction. For a 98-edge parent, (r=0,1,2) would give 196, 194, and 192 edges respectively, if the required Hamiltonian path exists.

## Retained labels and vertical crossings

For (y\in S), the label already sees its own lift. Proper colouring excludes a base loop at (y), so it has exactly two selected lifted neighbours if and only if (y) has exactly one neighbour in (S) in the base graph. `retained_label_two_neighbours_iff` proves this with an explicit distinct second neighbour and an exact neighbour-set equivalence. It does not rely on a numerical degree calculation or an assumed lifted path.

Because the original (P) is induced, neighbours within (S\subseteq V(P)) are precisely retained consecutive path neighbours. Therefore the eligible retained labels are exactly the endpoints of nonsingleton retained components. A singleton component contributes none: its retained vertex has no retained base neighbour and its label has only one selected lifted neighbour.

Deleting (r) vertices from a path leaves at most (r+1) nonempty components. Thus at most (2(r+1)) retained labels are eligible internally. This component-counting statement and its connection to literal path indices are written arguments here, not additional checked theorems in the new source.

Each selected retained label in a Hamiltonian lift uses exactly one vertical edge, namely the edge to its own lift. Its other incident edge comes from a base edge and stays in one face. A selected label (y\notin S) has no vertical edge to a selected lift; both its incident edges stay in one face. Consequently the number of vertical crossings in this construction is exactly the number of selected retained labels, and is at most (2(r+1)). This counts internal labels in the construction with both endpoints in the chosen lifted class. It does not automatically apply to the separate construction using opposite-colour endpoint labels.

## Verification boundary

The proposed Lean statements establish the general label adjacency, injection and disjointness, independence, and retained-label two-neighbour characterization. They do not construct a Hamiltonian path, verify a saved base snake, prove the deletion-component count in Lean, or certify native graph extraction or exhaustive search.

The finite experiment must retain the complete closed-base-neighbourhood intersection for every label. Omitting any selected neighbour could admit a chord. Any candidate must be lifted and independently checked as a complete cube-vertex sequence. A restricted infeasibility result would concern only the chosen parent and deletion set, unless complete coverage of a larger family is separately established. No new snake length, optimality result, or novelty claim is made by this preparation.
