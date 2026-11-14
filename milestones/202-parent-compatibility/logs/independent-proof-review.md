# Round 202 independent proof review

This report contains written proofs and source-based deductions. No solver, compiler, numerical census, or manuscript edit was performed. The final priority is the controlled diagonal transformation of an entire selected snake. Parent-compatibility deductions from the initial assignment are retained below.

## 1. Exact criterion for a controlled diagonal transformation

Choose two cube coordinates and write a vertex as (s,z), where s is the chosen two-bit word and z contains all other coordinates. Fix epsilon in {0,1}. Let tau interchange the two words of parity epsilon and fix the other two words. Thus tau is a square reflection: it swaps 01 and 10 when epsilon=1, and swaps 00 and 11 when epsilon=0. For a Boolean function f on base words define

F_f(s,z) = (tau^(f(z))(s), z).

This is an involution on the whole cube because its base word is unchanged. It need not be a cube automorphism.

For a selected vertex set S, let B consist of the base words z for which S contains at least one vertex (s,z) of two-bit parity epsilon. Then F_f preserves adjacency and nonadjacency for every pair of vertices in S if and only if f is constant on each connected component of the cube graph induced by B.

Proof. Within one base fibre, the same square automorphism acts on both vertices. For distinct fibres whose base distance is at least two, adjacency is impossible before and after transformation. For neighbouring base words z,w, adjacency is equivalent to equality of their two-bit words. If f(z)=f(w), equality is preserved. If the selectors differ, equality is reversed for every pair of active diagonal words: there are exactly two such words and tau interchanges them. Thus any selected active vertex in each fibre witnesses failure. Inactive words are fixed; an active word can never equal an inactive word. This proves both necessity and sufficiency.

The criterion preserves the entire ordered snake, including all chords being absent. It is stronger than merely asking whether the image set happens to admit some differently ordered path.

## 2. Selector subsets, complement symmetry, and iteration

The active base set B is invariant under every F_f. If it has r components, admissible transformations on S are indexed by subsets J of those components. Composition corresponds to symmetric difference of subsets. Selectors outside B have no effect on S.

Let T be the global square reflection tau applied in every base fibre. This is an ordinary cube isometry. For complementary subsets,

F_(J complement)(S) = T(F_J(S)).

Consequently, when r<=3, the unchanged set and every single-component switch represent all selector choices up to cube isometry. For r=3, each two-component subset is complementary to a singleton and the full subset is complementary to the empty subset. For r=2 the same conclusion is immediate; r=0 or 1 gives no additional isometry class. At r=4, two-component subsets introduce cases not covered by this argument.

This conclusion concerns at most 2^r images; it does not require the images to be distinct as unlabelled sets. The component count is a parameter of this particular S, coordinate pair and parity, not a universal bound for all snakes.

The move family is equivariant under cube isometries. A coordinate permutation transports the chosen pair and the base coordinates. A translation changes epsilon by the xor of its two chosen-coordinate bits, and induces a base translation. The active base graph and its connected components are transported accordingly. Therefore both parity choices must be covered if canonicalization permits arbitrary cube translations. Path reversal does not change the selected set and causes no additional issue.

Conditional closure statement. Suppose a finite bank has been exhaustively checked for every coordinate pair and both parities; every resulting active graph has at most three components; and every single-component image is cube-isometric, possibly after path reversal, to a bank representative. Then the union of the bank's symmetry classes is closed under all admissible controlled diagonal transformations and under arbitrarily many iterations, even when the coordinate pair changes at each step. Proof: complement symmetry covers every one-step selector choice; equivariance covers every cube image of a bank representative; induction covers any finite sequence.

The supplied native census is evidence for the finite premises. This review does not independently reproduce it or identify it as Lean-checked. If only a subset of bank representatives, pairs, parities or components was inspected, the closure conclusion must be restricted accordingly.

## 3. Self-symmetry of the same snake

If F_f preserves S as a set and preserves all its pair relations, its restriction is an automorphism of the finite induced path. Such an automorphism is the identity or reversal: fixing an endpoint fixes every vertex by distance from it.

There is a sharper statement for these diagonal maps. A nontrivial restriction to S can occur only when S has odd vertex count, and its action on S then agrees with the global square reflection T.

Proof. Every vertex moved by F_f changes exactly the two chosen bits, so its Hamming displacement is two. Reversal of an even-vertex path exchanges the two adjacent middle vertices, which is impossible. For odd vertex count, reversal fixes only the middle vertex and moves every other selected vertex. All noncentral vertices are therefore active diagonal vertices. The two neighbours of the centre are interchanged and differ exactly in the chosen two bits. Their common cube neighbours are the two inactive diagonal words in that same base fibre; hence the centre is inactive and is also fixed by T. All other selected vertices are moved by tau, so F_f and T agree on S. Each half of the snake has a constant active two-bit word and traverses the same base path in opposite directions.

Thus this family can give new embeddings of a whole snake, while a nontrivial self-map of the same embedding has the stated ordinary reflection form. These two uses of the word symmetry should remain distinct in the manuscript.

## 4. The 195-edge predecessor has one deletion in each parent

Assume the round-201 equality setting: two 98-edge Q8 parents P,Q, two isolated internal deletions, no additions, and a final induced 195-edge Q9 path with three crossings. The face restrictions of a path with three crossings consist of exactly two nonempty components in each face. Deleting d isolated internal vertices from a parent produces d+1 nonempty components. Therefore exactly one deletion belongs to each parent.

Let their indices be i,j, measured from either endpoint; their parity is unchanged by reversing a 98-edge parent. Let delta_P and delta_Q, each +1 or -1, denote the parents' base-colour imbalances. The initial layered union has imbalance delta_P-delta_Q. The final 196 selected vertices are balanced, so

delta_P(1-(-1)^i) = delta_Q(1-(-1)^j).

Thus i,j have the same parity. If both are odd, delta_P=delta_Q, so the original parent endpoints have the same base colour. Even i,j give no further colour restriction by this equation alone.

## 5. A stronger restriction in the C=5 one-addition case

Additionally assume the round-201 one-addition construction of 196 edges, with H=0 and initial overlap C=5. The sole addition is a final endpoint; removing it gives the predecessor above. Round 201 proves that its attachment vertex must be an original parent endpoint. The added opposite copy was outside the original parent union, so this attachment is not a crossing port.

Suppose it attaches to an original endpoint of P. The P-piece containing that endpoint has one crossing at its other, deletion-exposed endpoint. The other P-piece has two crossings, at both of its endpoints. Hence both neighbours u,v of the deleted P vertex x are crossing ports.

Overlap equality C=D+k implies that x has a retained opposite copy in Q. In that face, x is adjacent to both u and v. Each port already has a cross-face edge and can have at most one within-face neighbour. Therefore the entire Q component containing these vertices is precisely u-x-v, a path of length two. Since Q has only one internal deletion, that deletion must be at index 3 or 95.

The preceding parity identity now forces both deletion indices to be odd and the parent endpoint colours to agree. Thus every C=5 one-addition construction in this setting has at least one omission exactly three edges from an original parent endpoint. This is necessary, with no existence assertion. It uses the written geometric consequences of round 201 and is not claimed as an assembled Lean theorem.

## 6. Free involutive parent symmetry restricts one-deletion constructions

Assume Q=g(P), where g is a fixed-point-free cube involution with d(v,g(v))>=2 everywhere, both parents have 98 edges, and deleting exactly one layered vertex with no additions yields a 196-edge snake.

The overlap P intersect Q is g-invariant and therefore has even cardinality. Round 201 allows C in {1,2} for an endpoint deletion and C in {2,3} for an internal deletion, so C=2. Write the overlap as {a,g(a)}.

For an internal deletion, both overlaps survive and are the two endpoints of the intact Q parent. Applying g shows that they are also the two original endpoints of P.

For an endpoint deletion, the deleted endpoint is one overlap a and the surviving crossing is g(a). That surviving vertex must be an endpoint of the shortened P. It is either the other original endpoint, or the neighbour exposed by deleting a. The latter would give d(a,g(a))=1, contrary to the displacement assumption. Again the original endpoint sets of P and Q coincide with the overlap.

Therefore every such symmetric one-deletion construction has exactly the two common original endpoints, exchanged by g. Since a 98-edge path has equal-coloured endpoints, g must preserve cube parity. The original layered union is an induced cycle of length 198, and the final snake is obtained by deleting one of its vertices. This eliminates the genuinely exposed-port alternatives for this symmetry class. A parity-reversing free involution of displacement at least two cannot realize the construction. No impossibility result is proved for the remaining parity-preserving case.

Sources inspected: milestones/201-crossing-deletion/MATHEMATICAL_NOTE.md and handoff/CURRENT_STATUS.md. The controlled-map and census details were supplied by the coordinating agent. Only this review file was created.
