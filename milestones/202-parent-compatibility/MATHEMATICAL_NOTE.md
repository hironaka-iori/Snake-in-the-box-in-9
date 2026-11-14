# Round 202: a controlled symmetry of the whole snake

The previous round made progress: it established two-parent counting restrictions, updated both manuscripts, and published commit15f42e90. The user resumed the goal, then asked for a more complicated symmetry applicable to the whole snake. This round addresses that request with an exact global preservation criterion, rather than assuming that local substitutions preserve the rest of a path.

Three Lean modules pass with21 theorem dependency reports. No longer Q9 snake or new global numerical bound is obtained.

## Definition and scope

Choose two coordinates and write a cube vertex as (z,u), where z contains the other n−2 bits and u is the chosen two-bit word. Fix epsilon in {0,1}. Let tau_epsilon be the square reflection that interchanges the two words of parity epsilon and fixes the other two:

\[
\tau_1(01)=10,\quad\tau_1(10)=01;
\qquad\tau_0(00)=11,\quad\tau_0(11)=00.
\]

For a Boolean function f on the base cube define the **controlled square reflection**

\[
F_f(z,u)=(z,\tau_\epsilon^{f(z)}(u)).
\]

This is one map on every vertex of the whole cube. It is its own inverse, since z is unchanged. A nonconstant f can fail to preserve the full cube graph. Its restriction to an entire snake will be permitted only when it preserves adjacency and nonadjacency for every pair of selected vertices.

The operation belongs to the established controlled-swap family; the single-control swap is the Fredkin gate. Fredkin and Toffoli, Conservative Logic (1982), section2 and Figure2, provide the relevant prior art: https://gwern.net/doc/cs/hardware/1982-fredkin.pdf . The paper was inspected through the web tool after the Princeton mirror returned403. No claim of historical novelty is made for the operation or this application; the literature search was limited.

## Exact whole-snake criterion

For a selected set S, let B contain those base words z for which S has at least one vertex (z,u) with u of parity epsilon. Use the ordinary cube edges between the vertices of B.

**Theorem.** F_f preserves adjacency and nonadjacency for all pairs in S if and only if f is constant on each connected component of this graph on B. Consequently, if S is the vertex set of the ordered snake (v_0,...,v_L), then (F_f(v_0),...,F_f(v_L)) is an induced path of the same length.

Proof. Vertices in a common base fibre receive the same square isometry. Base words at distance at least two cannot produce an edge before or after the map. Across neighbouring base words z,w, two full vertices are adjacent exactly when their two-bit words agree. If f(z)=f(w), equality is preserved. If f(z) differs from f(w), equality is reversed for every pair of active diagonal words, because the diagonal has exactly two words. An active word cannot equal an inactive word, and inactive words are fixed. Thus adjacency changes precisely when neighbouring active fibres receive different choices. Constancy along edges is equivalent to constancy along every component. Involutivity ensures distinct selected vertices remain distinct.

The Lean theorem covers an arbitrary base graph G in G square Q2 and constructs the entire induced image path from the edge-wise compatibility premise. It includes every nonconsecutive pair; it is not a collection of local edge checks. The component formulation follows by propagation along a graph path and remains a written reformulation of that checked edge criterion.

## Composition and genuine self-symmetry

The active base set B is unchanged by every controlled reflection. If B has r components, one may choose independently which components to reflect. Composition takes the symmetric difference of the selected component sets. There are2^r distinct actions on the ordered selected vertices; some unlabelled image sets may coincide. Reflecting all components is the ordinary global square reflection. A chosen subset and its complement therefore give cube-isometric images.

At r≤3, the unchanged image and the single-component images represent all choices up to that global reflection. This fails as a coverage argument at r=4, where two-versus-two component choices appear. Lean checks composition, complement, compatibility stability and the arithmetic reduction at three components. The finite component interpretation is written explicitly here.

A self-symmetry of a fixed snake is a narrower notion. An automorphism of a finite path is identity or reversal: it maps endpoints to endpoints, and distance from a chosen endpoint determines every vertex. For this controlled-reflection family, a nontrivial self-map can occur only when the snake has an odd number of vertices, and it then agrees on the entire snake with the ordinary global square reflection.

To prove this sharper assertion, every moved vertex changes exactly two bits. Reversal of an even-vertex snake exchanges the adjacent middle pair, which has displacement one, so that case is impossible. For an odd-vertex snake, reversal fixes only the central vertex. All other vertices must lie on the active diagonal and be moved by tau_epsilon. The neighbours of the centre are exchanged; their common neighbours are the two inactive words in their common square fibre. Thus the centre is also fixed by the global reflection, proving agreement everywhere on the snake. These self-symmetry statements are written proofs, without a new Lean assembly in this round.

This distinction is essential. Controlled reflections can transform a whole snake into a different geometric embedding. They do not create an additional intrinsic automorphism beyond reversal.

## A checked whole-snake example

In Q5, take

\[
P=(0,1,3,7,15,14,10,26,18,22,20,28,29,25).
\]

Choose coordinates0 and3, epsilon=1, and reflect the active component whose remaining bits encode20. The map exchanges21 with28 and fixes the other Q5 vertices. The entire image path is

\[
F(P)=(0,1,3,7,15,14,10,26,18,22,20,21,29,25).
\]

Lean checks distinctness and every adjacency pair for both14-vertex paths, the image equality at every position, and failure of Hamming-distance preservation under both possible path alignments. Therefore these two snakes are not related by a cube isometry, even allowing reversal. For example, the distance between positions1 and11 changes from4 to2. This is a concrete whole-snake transformation beyond a uniform coordinate relabelling, although it changes only one selected vertex in this example.

## Complete finite census and its limit

The native census examines every coordinate pair and both parities for the saved Q5,Q6,Q7,Q8 seeds and all131 saved191-edge Q9 snakes. It constructs all active base components, applies each individual component switch, checks the complete resulting path, and compares canonical transition sequences under translation, coordinate permutation and reversal.

| Input | Pair/parity choices | Component counts |
|---|---:|---|
| Saved Q5 seed |20|18 connected,2 with two components|
| Saved Q6 seed |30|all connected|
| Saved Q7 seed |42|all connected|
| Saved Q8 seed |56|all connected|
|131 saved Q9 snakes |9432|9248 connected,144 with two components,40 with three|

For the saved Q6,Q7,Q8 seeds, every admissible transformation in this family therefore agrees on the snake with identity or a global square reflection. This is a restriction on these representatives, not on all optimal lower-dimensional snakes.

The Q9 census produces408 single-component images across184 disconnected active graphs. They represent111 cube-isometry classes, all already in the131-snake bank. Twenty bank representatives have connected active graphs for every pair/parity choice;71 have maximum component count two and40 have maximum three. The four Q5 images bring the total checked single-component images to412.

The census also implies closure under all component subsets and arbitrary iterations, with the following proof. Every active graph has at most three components, so complements reduce all one-step choices to the original or a single-component image. The move family is invariant under cube isometries: coordinate permutations transport the pair and base graph, while translating one chosen bit exchanges the two parity cases. Both parities were included. Therefore every one-step image of any cube copy of a bank member belongs to the same union of bank classes. Induction gives closure under any finite sequence, even if the coordinate pair changes between steps.

The general preservation and group deductions are Lean-checked. The9432-case census and its finite membership premises remain native computation, with pinned input hashes and source. The final bank-closure conclusion combines those finite premises with the written equivariance and induction argument; no full-bank Lean replay is claimed. It supplies no classification of all191-edge snakes. This move family alone therefore cannot provide a new isometry class beyond the saved bank when starting there.

## Additional parent restriction retained from the proof review

The195-edge, three-crossing predecessor of round201 must omit exactly one internal vertex from each98-edge parent. Three crossings divide the final path into two face components on each side; deleting two isolated internal vertices from one parent would instead produce three components on one side and one on the other.

Let i,j be the deletion indices, and let delta_P,delta_Q be the parents' base-colour imbalances, each equal to+1 or−1. The two layered faces have opposite colour conventions. The predecessor has196 vertices and equal colour counts, so

\[
\delta_P(1-(-1)^i)=\delta_Q(1-(-1)^j).
\]

Thus i,j have equal parity. If they are odd, the original parent endpoints have the same base colour.

In the saturated C=5 one-addition196 case, round201 forces the new endpoint to attach to an original parent endpoint, say one of P. That endpoint is not an old crossing port, because its newly added opposite copy was outside Q. Both exposed neighbours of the omitted P vertex must therefore be ports. The omitted projection has a retained opposite copy in Q; it joins these two ports into a complete two-edge component, since a crossing port can have at most one within-face neighbour. Deleting one vertex at index j of a98-edge parent leaves pieces of lengths j−1 and97−j. Hence j=3 or95. Both deletion indices are odd, and the parents' endpoint colours agree. This is a necessary condition, not an existence result. It is a written geometric proof with no new Lean assembly in this round.

The independent review also records a conditional free-involution restriction: if the two parents are exchanged by a fixed-point-free cube involution of minimum displacement at least two, a one-deletion196 construction must arise by deleting a vertex from an induced198-cycle with the parents' two original endpoints shared. The involution must preserve cube parity. Its hypotheses and proof remain in logs/independent-proof-review.md; this restricted case is not a global bound.

## Evidence and continuation

ControlledSymmetry202 has10 accepted reports, ControlledGroup202 has8, and WholeSnakeExample202 has3. The first module had a failed attempt caused by missing decidability instances; the example had a failed attempt caused by tokenizing a missing space as inequality. Their source snapshots, execution plans and failed compiler outputs are retained. Every accepted receipt matches its source, imported objects and successful compiler log, with only the permitted standard axioms.

Contributor branch research/unconditional-241 advanced to e4b85bb1f447e19a6533fbabe18244b1473c846c. Its latest inspected entry reports3098/3127 certificate modules built, including two remotely built modules installed locally. Its source explains changed memory scheduling and remote transfer. These are contributor reports; no independent rebuild or merge was performed. Archived235 still awaits independent rebuilding, and233/234 retain pending premises.

The goal remains active. The controlled two-coordinate family is now characterized sufficiently to avoid repeating it on the saved Q8 seed or expecting it to escape the Q9 bank. A future whole-snake symmetry should change a larger coordinate block or impose a different global geometric constraint; it must receive an equally explicit all-pair preservation proof. The independently sharpened C=5 parent condition offers a second proof route. No success prediction for196 follows from this round.
