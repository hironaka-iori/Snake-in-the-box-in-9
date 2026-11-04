# Strengthening the undominated-corner bound

Status: written proof and a finite Boolean check; full actual-cube Lean assembly pending.

Claim. In Q9, for a nontrivial induced path, every vertex with no selected neighbor belongs to at least six empty squares. Consequently such a vertex contributes at least 72 to rounding loss, and L <= 71 implies that every cube vertex has a selected neighbor.

Proof. Translate the vertex to zero. It is unselected, since every selected path vertex has a selected neighbor. All nine unit vertices are absent. Form a simple graph H on the nine coordinate directions: ab is an edge precisely when the weight-two vertex {a,b} is absent. Thus |E(H)| is exactly the number of empty squares at zero.

There cannot be two isolated vertices of H. If a,b were isolated, the selected vertex {a,b} could only have weight-three selected neighbors. Every candidate {a,b,k} would have three selected pair neighbors, contradicting maximum selected degree two. This is the previously established pair/triple argument.

Suppose H has at most five edges. If H has one isolated vertex c, its other eight vertices have positive degrees and their degree sum is at most ten. At most two can have degree at least two, so at least six have degree one. For every degree-one vertex a, with unique neighbor a', the selected vertex {c,a} has only one possible selected neighbor, {c,a,a'}. Minimum degree forces it. Three such distinct vertices already contradict the two-endpoint property. Therefore H has no isolated vertex.

The degree sum is now at least nine and at most ten, and is even. It equals ten. Exactly one vertex has degree two and the other eight have degree one. Therefore H is the disjoint union of a three-vertex path and three isolated edges.

Take any two isolated edges A={a,a'} and B={b,b'}. The four cross-pair vertices {a,b}, {a,b'}, {a',b}, {a',b'} are all selected. A selected neighbor of a cross-pair must be a triple. The only possible triples are obtained by adding the partner of either coordinate: any other triple would have three selected pair neighbors. The four possible triples together with the four cross-pairs form an eight-cycle, alternating pair and triple vertices. Every included triple already has its two cross-pair neighbors selected and so cannot have any additional selected neighbor of weight four. Thus these selected vertices have no selected neighbors outside this eight-cycle.

At least one triple must be absent, since an induced path contains no cycle. Every cross-pair must retain a neighbor, since the path has no isolated vertex. The remaining graph is a nonempty disjoint union of paths and therefore contains at least two degree-one vertices. These are genuine endpoints of the whole snake, since the component has no selected edges to the outside.

Three isolated edges give three different choices of two edges. Their cross-pair and triple vertex sets are disjoint: the support of every vertex identifies the two coordinate blocks it meets. Each choice therefore forces at least two distinct endpoints, for a total of at least six. This contradicts the two endpoints of a nontrivial path. Hence H has at least six edges.

All remainder terms are nonnegative, and a degree-zero center contributes 12 times its empty-square count. This proves the stated 72 threshold under the written geometric argument.

Verification boundary. The finite check enumerates the 16 possible selections of the four triple vertices of a fixed eight-cycle. It verifies that keeping every cross-pair nonisolated and excluding the full cycle forces at least two degree-one cross-pairs. It does not establish the cube interpretation, graph classification, or global loss identity. Those require the arguments above and their pending Lean counterparts. No unconditional numerical upper bound is claimed.
