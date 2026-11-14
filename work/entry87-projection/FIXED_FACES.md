# Which full faces can a 192-edge snake retain?

**Theorem.** No 192-edge nine-cube snake has, as its entire intersection with an eight-dimensional face, an isometric copy of the saved 98-edge parent. The claim includes every cube orientation and any order on the outside vertices.

Every internal vertex of the fixed parent already has its two path neighbours. A crossing at an internal vertex is impossible. Consequently all crossings incident with this face must occur at its two endpoints. At least one is needed to reach 193 vertices. There are therefore just three configurations: one crossing at either endpoint, or crossings at both. The [two single-crossing cases](PARTNER93.md) are already excluded by separate checked certificates.

### Two crossings

Let P run from 0 to 78 in the fixed face. The opposite face must contain 193−99=94 vertices, including both endpoint copies. Exactly 159 addresses are available: the 157 outside P and the two endpoint addresses. The 94 selected vertices of that face must form two arms, one anchored at each endpoint and with no cross-contact between the arms. Either arm may consist solely of its root.

For the restriction used in the proof, give each selected outside vertex an indicator for being an endpoint of the whole snake. Exactly two indicators are true. At a selected nonroot, within-face degree is two minus its endpoint indicator. At a root the known crossing supplies one neighbour, so within-face degree is one minus its endpoint indicator. All selected internal and terminal adjacencies are counted. Both roots are even. Along each rooted arm the number of even vertices minus odd vertices is zero or one according to its length. Since the total outside vertex count is even, the total imbalance is zero or two. Thus there are either 47 or 48 even vertices outside. These are necessary restrictions for every possible split of the two arms.

Every subgraph of an induced path is acyclic. The exact formula therefore prohibits the simultaneous selection of vertices of each listed 4-, 6- or 8-cycle in the available four-dimensional faces and their lower-dimensional subfaces. Each actual vertex list is checked to have induced degree two at every member. Even a union of disjoint cycles would suffice to justify a clause. All 1,552 clauses are necessary. The initial formula was already contradictory; the run added no dynamical connectivity clause. The exported proof was checked, trimmed, and checked again. Its core needed 11,859,407 resolution steps. [Two-crossing encoder](two_crossings.py), [proof receipt](two-crossings-totalizer-1-checked.json).

Together the three refutations prove the theorem. A possible 192-edge snake could have a different 98-edge face path, another face shape, or cross differently when its face is disconnected.

### Faces extracted from the published 191-edge bank

Twenty-five of the 131 bank paths use a coordinate exactly once. In every such instance the two faces carry paths of 96 and 94 edges. Normalize the rooted transition sequence of each face starting at the crossing. Coordinate names are determined by first occurrence. This gives five rooted 96-edge face classes and five rooted 94-edge classes, each represented by five of the bank occurrences. They supply ten existing path shapes with an exhibited one-crossing join of length 191.

Test each of these ten shapes at each endpoint for a single-crossing 192-edge extension, allowing the partner its complete permitted base graph and an unrestricted far endpoint. For a 96-edge face the partner needs 95 edges, and for a 94-edge face the partner needs 97 edges. Every one of the **20** root formulas was refuted and both the original and compacted proofs verified. There were no dynamic component cuts in any refutation. [Bank extraction and reproducer](bank_partner.py). Receipts begin with `partner93-bank` and contain `checked`. The matching formulas and proof cores begin with `partner-proof-bank`. These 20 conclusions concern single crossings; the first theorem above concerns every crossing configuration for the separate, original 98-edge parent.
