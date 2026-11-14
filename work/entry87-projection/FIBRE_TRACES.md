# Reconstructing a path after erasing multiple coordinates

Erase d coordinates of a snake in the nine-cube. Compress each consecutive run at the same projected address to one visit. The resulting ordered list T records exactly the transitions on the retained coordinates, up to translation of the starting vertex. The number of erased transitions between visits is completely free. A repeated address in T receives a separate visit. For d ≥ 2 repeated addresses are possible.

**Reconstruction lemma.** Associate to visit i a nonempty oriented induced path inside its copy of the d-cube. Write Hᵢ for its set of fibre labels, with first label aᵢ and last label bᵢ. Concatenation gives an induced path if and only if all of the following hold.

* Consecutive projected addresses are adjacent. Their visits satisfy bᵢ = aᵢ₊₁ and Hᵢ ∩ Hᵢ₊₁ = {bᵢ}.
* Two nonconsecutive visits to adjacent projected addresses use disjoint label sets.
* Different visits to the same address use disjoint label sets with no cube edge between them.

The reconstructed path has exactly the sum of the visit sizes in vertices. To prove sufficiency, consider any two proposed full-cube vertices. At projected distance at least two they cannot be adjacent or equal. At projected distance one they are adjacent exactly when their fibre labels agree. At projected distance zero their adjacency and equality are precisely those of the fibre cube. The three conditions handle every pair from distinct visits. Within a visit the asserted induced path handles every pair. Necessity follows by applying the same three distance cases to an existing snake.

### Two erased coordinates

The fibre is a square. A visit uses one, two or three sites, giving four singleton, eight oriented edge, and eight oriented three-site patterns. Two separate visits to the same projected address must be singletons at opposite corners. Once one visit contains an edge, every remaining corner of this square is adjacent to one of the two sites in that edge. Three separate visits are impossible.

Across all 131 longest sources and all 36 unordered axis pairs, the 4,716 traces each admit a 191-edge reconstruction. **Every one of them has maximum 191 edges.** For each trace, permit every legal pattern at every visit, enforce the three compatibility conditions, and ask whether the sum of all visit sizes can reach 193. The sum is a lower threshold, so a longer lift of that same complete trace would also have been accepted. All 4,716 formulas return UNSAT. The stored original reconstruction and every relation in it were independently checked at the input, and a positive search reconstructs a full 191-edge snake. Across the traces there are 3 through 75 repeated visits per trace. The full set of refutations uses 476,405 solver conflicts, with a maximum of 572 in one trace.

[Square pattern reconstruction](square_fibers.py), [sources 0 through 44](square-fibres-0-45-45000.json), [sources 45 through 87](square-fibres-45-88-45000.json), [sources 88 through 130](square-fibres-88-131-45000.json), [independent proof export and replay](certify_square_fibres.py).

### Three erased coordinates

Each visit now has its own three-dimensional cube. The second encoding marks its first and last label and selects a subset of the eight sites. Every selected label has fibre degree plus number of marked ends equal to two. Both ends may mark one site. When the marks are distinct this forces an ordinary path and possible extra cycles. When they coincide the marked site is isolated and every remaining component would be a cycle. Excluding induced cycles therefore gives exactly one path for each visit. The three inter-visit rules then apply without change.

For entry 87, **all 84 choices of three erased axes preserve a maximum of 191 edges** at the recorded ordered trace. The search tests the seven choices containing both axes 1 and 4 first. All 84 give complete UNSAT answers, and the 191-edge source gives a matching lower bound for each. [General fibre encoding](fibre_csp.py), [seven prioritized triples](fibre-d3-87-0-7-30000.json), [other 77 triples](fibre-d3-87-7-84-80000.json). Results for other sources require their own ledgers.
