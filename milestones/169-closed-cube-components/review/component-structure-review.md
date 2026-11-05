# Independent challenge of the component-structure strengthening

Verdict: the written component argument is sound for the missing-pair graph at an undominated center of a nontrivial induced path in Q9. No counterexample or missing geometric assumption was found. It strengthens the written conclusion to at least eight empty squares. This review does not certify Lean assembly or the global loss identity.

## Exact closed subset

Translate the center to zero. Nontriviality implies every selected vertex has a selected neighbor, so zero itself is absent; undominatedness means all unit vertices are absent. Let H be the simple graph on all nine coordinates whose edges are precisely absent pair vertices.

Take distinct connected components A and B of H. Every pair with one coordinate in A and one in B is selected, since an H edge cannot join two different components. Define the candidate subset S to contain:

- all these cross-pair vertices;
- all triple vertices consisting of an H edge within A and one coordinate in B;
- all triple vertices consisting of an H edge within B and one coordinate in A.

This definition does not assert that every candidate triple is selected. Closure applies to S intersected with the actual selected path. This distinction is necessary in the Lean statement.

For a selected cross-pair {a,b}, any selected neighbor is a triple {a,b,k} with three distinct coordinates: repeated coordinates give absent unit vertices. If k belongs to neither A nor B, all three pair-side vertices are selected. If k belongs to A but ak is not an H edge, all three are again selected; the same argument holds in B. Each case contradicts maximum selected degree two at the triple. Therefore every selected neighbor of the cross-pair lies in S.

Every candidate triple in S has two distinct selected cross-pair neighbors. Its third pair-side vertex is its defining absent H edge. It has no other weight-two neighbors, no neighbors of weight three, and any additional neighbor has weight four. If the triple is selected, its two existing selected neighbors exclude any selected weight-four neighbor. Thus every selected neighbor of a selected triple in S also lies in S.

Consequently S is nonempty on the selected path and closed under selected adjacency. Generic path closure forces every selected vertex into S. No assumption about the sizes of A and B or the length of the snake beyond nontriviality is needed.

## Consequences for H

If a third component C existed, a pair {a,c} with a in A and c in C would be selected and outside S. Therefore a disconnected H has exactly two components.

If two distinct coordinates inside A were nonadjacent in H, their pair vertex would be selected and outside S, again a contradiction. Hence A is a clique. The same argument applies to B. Singleton components cause no exception: singleton cliques satisfy the conclusion, and the cross-pair family remains nonempty.

Thus H is either connected or the disjoint union of exactly two cliques. The assertion is a necessary condition on actual snakes, not a claim that every graph of those forms is realizable.

## Cardinal arithmetic

A connected simple graph on nine vertices has at least eight edges. If H is the union of cliques of sizes a and 9-a, where 1 <= a <= 8, its edge count is a(a-1)/2 + (9-a)(8-a)/2. By symmetry, sizes 1+8, 2+7, 3+6, 4+5 give respectively 28, 22, 18, 16 edges. Thus the disconnected case actually has at least sixteen edges, and the universal conclusion is |E(H)| >= 8.

Since zero and all unit vertices are absent, each coordinate pair determines an empty square exactly when its pair vertex is absent. Therefore |E(H)| equals the empty-square count at zero. Translation gives e(q) >= 8 at every undominated center q of a nontrivial Q9 snake.

## Loss consequence and verification boundary

If the established project loss identity assigns 12e(q) to a degree-zero center and all other terms are nonnegative, an undominated center contributes at least 96. Under those accounting assumptions, total loss L <= 95 implies every cube vertex has a selected neighbor. The geometric proof does not itself establish that loss identity or a new unconditional upper bound on snake length.

No compilation was run and no existing Lean source was changed in this review. The generic path closure result is sufficient only after the actual-cube subset, its closure, and its outside witnesses are assembled. The elementary graph connectivity and clique-count bounds also remain explicit proof dependencies.

## Exact disconnected-case length and realization

The stronger exact-length assertion is correct. If H is K_a disjoint union K_b with a+b=9 and a,b positive, there are exactly ab selected weight-two vertices, namely all cross-pairs. Closure confines every selected vertex to these cross-pairs and candidate triples. Each selected triple has exactly two selected cross-pair neighbors, so neither endpoint can be a triple. Adjacency alternates between pairs and triples. The path therefore has ab pair vertices, ab-1 triple vertices, 2ab-1 vertices in total, and m=2ab-2 edges. The unordered size splits 1+8, 2+7, 3+6, 4+5 give exactly m in {14,26,34,38}.

Every one of these lengths is realized with the claimed missing-pair graph. Arrange the ab pairs as a rectangular array indexed by their coordinates in A and B. Traverse the rows in alternating directions; the last pair in a row and the first in the next row share the same B coordinate. This gives a Hamiltonian path in the graph where two pairs are adjacent when they share one coordinate, namely the rook graph (the Cartesian product K_a and K_b).

Between each successive pair insert the triple equal to their union. Every inserted triple has exactly those two cross-pair neighbors; its third pair-side vertex lies wholly in one block and is absent. Thus it has no chord to another selected pair. Distinct pairs are not adjacent to each other, and distinct triples are not adjacent to each other, by their equal Hamming weights. Inserted triples are distinct because each identifies its unique two cross-pair sides, hence its unique traversed rook-graph edge. The resulting sequence is a simple induced path. It contains all cross-pairs and no within-block pair, so its missing-pair graph is exactly K_a disjoint union K_b. Zero and all unit vertices are absent, and zero is undominated.

Consequently the disconnected case is completely characterized by these four lengths in Q9. In particular, a snake with m>38 has a connected missing-pair graph at every undominated center. These are written deductions; this review performs no Lean compilation.
