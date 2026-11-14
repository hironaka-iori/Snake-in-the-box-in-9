# Geometry of the one-chord walk

The chord of the 193-vertex walk runs from position 7 to position 192. Its suffix from 7 through 192 is therefore an induced 186-cycle: the endpoints of this suffix are adjacent, every successive pair is adjacent, and every other pair is a nonedge of the one-chord walk.

## Gluing at a vertex

Suppose two ordered induced paths meet at a designated pivot. Put the pivot at zero by translation. Keep the first path fixed and apply a coordinate permutation to the second. This exhausts all relative cube isometries identifying the two pivot copies: every cube isometry is a translation followed by a coordinate permutation, and fixing zero removes the translation. The joined ordering is induced precisely when every vertex of the moved arm outside the pivot has distance at least two from every vertex of the fixed arm outside the pivot. This also excludes accidental coincidences. All within-arm pairs retain their distances.

For entry 87, the chord endpoints must lie strictly on opposite sides of the pivot. Thus precisely pivots 8 through 191 are eligible. A complete scan of all 9! relative placements at all 184 pivots found no repair: 66,769,920 placements. Moving the shorter arm is equivalent by applying the inverse permutation to the whole assembly. See [source](pivot.cpp) and [per-pivot counts](pivot.csv).

The same conclusion holds for **every one of the 180 one-chord candidates** obtained by inserting a single transition anywhere in the 131 saved snakes and keeping candidates with distinct vertices and exactly one unwanted edge. These reduce to 176 distinct transition words up to global coordinate renaming and reversal. Across the representatives, exactly 16,132 pivots lie strictly inside their respective chord endpoints, giving 5,853,980,160 rooted relative permutations. Every placement fails. The classification by transition word is complete because translation fixes the starting vertex, after which the sequence of flipped coordinates determines every vertex. Reversal gives the same placement family with the two sides interchanged. [Enumeration](bank_pivots.py), [per-input results](bank-pivots.json).

## Two independently movable arms

Fix the middle segment from positions i through j. Place the left and right arms independently by isometries fixing their respective hinges. First exclude each arm placement with an illegal contact in the fixed middle. For the remaining placements, one condition remains: the closed radius-one neighbourhood of the left arm outside its hinge must be disjoint from the right arm outside its hinge. Necessity follows from the path order. Sufficiency follows by partitioning every nonconsecutive pair according to its segments. Lean checks this pair partition for arbitrary distance data in [ArmLemma.lean](ArmLemma.lean).

The placement checks depend on the occupied vertex sets. Two admissible placements of the same arm with equal occupied sets have identical cross-arm compatibility, so we retain one representative per set. An explicit successful ordered path can always be reconstructed from the representatives.

For all 2,304 choices with each end arm between 1 and 48 edges, 1,968 hinge pairs admitted placements of both arms against the middle. After this first filter there were 5,370,932 pairs of coordinate permutations, reduced to 6,168 pairs of occupied sets. Every pair contained a forbidden contact. [Search](two_pivot.cpp) and [per-hinge counts](two-pivot-48.csv).

## Unrestricted arms around a retained cycle arc

Delete a contiguous block of k vertices from the 186-cycle. The remaining arc has 186−k vertices. Grow both endpoints in arbitrary directions, allowing the vacated vertices to be reused. To reach 193 vertices requires exactly k+7 additional vertices. Growing the left arm first, then the right arm, covers every completion: contiguous restrictions of an induced path are induced. At any partial path a neighbour of the endpoint is admissible exactly when it is unused and has no adjacency to another selected vertex. With at least two vertices selected, this is equivalent to its closed neighbourhood intersecting the current path only in the endpoint.

All 186 starting cuts were exhausted for each k from 1 through 38. In every one of these 38 searches the largest completed path had **192 vertices (191 edges)**. Therefore no 192-edge snake contains a contiguous arc of this specific cycle of length at least **148 vertices** in its cycle order, up to reversal and cube isometry. Indeed any longer arc contains a 148-vertex arc, and the outside segments of the snake would give two arms for that arc. For k from 39 through 52, the saved run stops partway through the cuts at its 400-million-node budget. [Exact extension search](cycle_arms.cpp) and [coverage by removed length](cycle-arms-52.csv).

These exclusions measure three different ways of preserving structure. A repair may change many coordinate histories while agreeing on a long arc, or preserve several histories while changing vertices throughout.

### The 192-cycle in the bank

Each of the 180 one-chord candidates contains an induced cycle between its chord endpoints. Canonicalizing the cyclic sequence of flipped coordinates under rotation, reversal and coordinate renaming gives 23 cycle classes. Translation removes the choice of starting vertex. For a chosen cyclic order the first occurrence of each coordinate determines its canonical name. This proves that two canonical words agree precisely when the cyclic paths are equivalent up to these symmetries. All 18 occurrences of length 192 represent **one** cycle class in this bank.

For this 192-cycle, exhaustive two-end regrowth after deleting each possible consecutive block of 38 vertices reaches at most 192 vertices. All 192 cuts were exhausted. Thus no induced 192-edge snake can contain **154 consecutive vertices** of this particular cycle in its cyclic order, up to isometry and reversal. The 39-vertex deletion search stopped after 126 complete cuts at its saved budget. [Cycle census](cycle-bank.json), [classifier](cycle_bank.py), [per-length traversal](coil192-arms.csv).
