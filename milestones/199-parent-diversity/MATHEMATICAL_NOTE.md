# Round 199: symmetry placements beyond involutions

## Result and scope

Symmetry now serves two separate purposes: reducing a fixed quotient to three endpoint cases, and enumerating all relative placements of lower-dimensional parent paths. The second purpose does not require an involution. This distinction broadens the construction search while giving exact exclusions for the saved parent families.

The complete native placement censuses found no separated 100-vertex face among the six unordered pairings of three saved 50-vertex Q7 parent classes, or among the fourteen pairings of the published 51-vertex parent with saved 49-vertex parents. Every possible relative cube isometry was included. These are restricted computational exclusions, with no Lean replay of their numerical census. They are not a classification of all Q7 paths. No new Q9 witness or global bound was obtained.

## Arbitrary isometries suffice for separated components

Let P and Q be induced paths in Q7 with vertex sets S and T. For any cube isometry f, put P in the face with last coordinate zero and f(Q) in the face with last coordinate one. Within each face inducedness is preserved. Between faces, two vertices are adjacent exactly when their seven-dimensional projections coincide. Consequently, these two Q8 paths are separated exactly when

$$S\cap f(T)=\varnothing.$$

Neither equality of the parent shapes nor the condition f squared equals the identity is necessary. This does not supply an involution quotient: the global map (y,b) to (f(y),1-b) has square (f squared(y),b), and the earlier quotient arguments require that square to be the identity.

The generic path-image construction, embedding in a layer, and exact cross-layer separation equivalence are checked in IsometricPlacement199. The check also covers changing parent representatives and reversing their order, with the inverse-map assumptions stated explicitly. Five theorem dependency reports pass; no admitted statements occur.

## Exhaustive relative placement of a fixed parent pair

Every Q7 cube isometry has the form f(v)=pi(v) xor t, with a permutation pi of the seven coordinates and a translation t in Q7. For each pi the program computes

$$c_\pi(t)=\#\{(u,v)\in S\times T:u\oplus\pi(v)=t\}.$$

This equals the size of S intersect (pi(T) xor t). Each intersection vertex determines exactly one pair because pi is bijective. Thus a zero entry is exactly a separated placement. All 5040 coordinate permutations and all 128 translations give 645120 placements per parent pair. A minimum of two means that every placement overlaps, and at least one placement has exactly two common vertices.

Independent normalization of the two parents is valid here. If S and T are replaced by alpha(S) and beta(T), the relative map changes to alpha inverse composed with f composed with beta, which still ranges over all cube isometries. Reversing the ordered parent pair replaces f by its inverse and preserves intersection size. Hence unordered pairs suffice. With an involution-only family, independent normalization of different parents is generally invalid; conjugation preserves that family only when the same change of coordinates is applied on both sides.

The saved paths are deduplicated by their transition words: rename coordinates in order of first appearance and take the smaller of the normalized word and its reversal. Equality of these words is equivalent to cube isometry of the paths, allowing path reversal. A translation fixes the initial vertex, and the coordinate correspondence fixes every subsequent vertex. Conversely, an isometry between paths must preserve their order or reverse it. Unused coordinate names can be extended to a permutation.

## Parent bank and exact finite exclusions

The published 50-edge Q7 seed has 51 vertices. Ordered extension starts from its first 24 vertices, in each orientation. Every next vertex is a neighbour of the current endpoint, unused, and nonadjacent to all earlier vertices except the current endpoint. This visits every induced extension of the fixed prefix.

At target 50 vertices, the searches exhaust 62453 and 88240 nodes and produce three isometry classes. At target 49 vertices, they exhaust 62451 and 88239 nodes and produce fourteen classes. The scope is these two fixed prefixes. Two further searches with a 16-vertex prefix stop at 3000001 nodes each; their two saved classes already occur in the three-class bank. They do not exclude additional parents.

| Parent sizes, vertices | Distinct parent pairs | All relative placements per pair | Minimum intersection |
|---|---:|---:|---|
|51 and 51, published parent twice|1|645120|2|
|50 and 50, three-class bank including self-pairs|6|645120|2 in every case|
|51 and 49, published parent and fourteen-class bank|14|645120|2 in twelve cases; 3 in two cases|

The complete scans cover 21 distinct parent-pair cases. The three 50-vertex parents also fail the smaller 6512-involution census. The full isometry calculation strengthens that finite exclusion. The 51-plus-49 alternatives show that merely allowing unequal component lengths does not repair any of these saved candidates.

These calculations have native execution records, input hashes, explicit permutation/translation coverage and intersection histograms. They have no Lean contradiction certificate. The generic placement reasoning is checked separately; this separation is essential when interpreting the result.

## Searches outside the finite parent bank

The quotient from round 198 has endpoint representatives 10, 2 and 0. Three connected circuit searches for 50 quotient vertices, with no seed constraint, return UNKNOWN after 45.062, 45.016 and 45.000 seconds respectively. This exhausts their allotted time, not their search spaces. No one of the three cases is excluded.

The stronger parent-diversity query fixes the published 51-vertex path and searches for any 49-vertex induced path in its complement. The allowed graph has 77 vertices and 141 edges. A circuit through one dummy vertex enforces one connected path, and all selected ordinary edges are included. There is no restriction on the second parent's shape, symmetry or overlap with a seed. This query returns UNKNOWN after 60.000 seconds.

If the complement query succeeds, the two paths give a 100-vertex Q8 face. A four-crossing Q9 completion would still need 93 vertices in the other face for 192 edges, 95 for 194, or 97 for 196. A pair of separated components alone supplies none of those Q9 lower bounds.

## Interpretation and next work

Changing the symmetry alone cannot improve any completely scanned parent pair in the table. A useful continuation must change the parent shapes, allow the quotient path to use matching steps, or change the face arrangement. The complement query gives a precise way to vary the second parent without prematurely assuming it is congruent to the first.

The next round should examine the geometry of the minimum-overlap placements and repair both parents together, or derive stronger information about long paths in the 77-vertex complement before spending more time on the same unresolved circuit model. The full-isometry census should be reused to remove equivalent candidates. A whole-manuscript review is due at round 200.

The contributor branch advanced to 0cb8450707e481db49b6204587e45db9ae0df589 with four new replay-log entries. Their generation records were inspected and archived; they were not independently rebuilt or merged. They do not change this round's bound status. Research remains active.
