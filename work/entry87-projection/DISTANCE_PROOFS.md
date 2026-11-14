# Three projection exclusions from distances in the six-cube

For each case below, fix the listed three coordinate histories of entry 87's 193-index target and allow all six others to vary. A run is a maximal interval with constant free word, as forced by the indexed changes in the retained vertices. Adjacent runs have free words at distance one. The search allows the first and last vertices to vary within their fixed projections.

| Retained coordinates | Runs | Sizes of even and odd families of distinct words | Solver conflicts in the checked run |
|---|---:|---:|---:|
| 0, 1, 3 | 81 | 32, 32 | 3,477 |
| 0, 3, 4 | 91 | 31, 30 | 91,661 |
| 1, 3, 4 | 89 | 30, 31 | 518,552 |

Every case is impossible. Together with the previous four proofs and the [six-neighbour counting proof](PARITY_NEIGHBORS.md) for coordinates 0, 1, 2, this excludes eight of the 84 retained triples for entry 87.

### Distance constraints

For runs i,j write D(i,j) for a superset of the feasible free distances. A walk through j−i successive edges gives the parity and the upper bound j−i. Every indexed pair constrains the free distance because full distance is retained distance plus free distance. For consecutive positions that sum is one. For nonconsecutive positions it is at least two.

Suppose two legs of a triangle have lengths a,b in a d-cube. Their coordinate-change sets intersect in s coordinates. The third length is a+b−2s, with max(0,a+b−d) ≤ s ≤ min(a,b). Repeatedly intersect the allowed lengths for each pair with the lengths possible through each intermediate run. This operation preserves every lift. Whenever zero disappears for all pairs from a same-parity family, its words must be distinct. If the family has 32 members, it uses every word of its parity. If it has k members, exactly 32−k words are absent.

For each case the checked Boolean formula chooses one allowed six-bit word per run. It enforces the distance restrictions, chronological first-use symmetry, distinctness and the corresponding number of missing words in each recorded family. First-use normalization is possible by translating the first word to zero and naming the six coordinates in order of first appearance. This preserves all the fixed coordinates. Any lift supplies a satisfying assignment.

### Independent checks

[Distance verifier](verify_distances.py) reconstructs its own intervals from the literal 193 positions. It examines all position pairs, closes the sets in a different iteration order, and obtains composition possibilities by enumerating the 64 actual cube vertices. It compares every resulting distance mask and checks every anchor pair. [Proof generator](certify_triangles.py) builds the formula, runs CaDiCaL, checks its DRAT proof, extracts a smaller proof and checks this again against the full formula. The compressed formula, compressed extracted proof, and hash receipt for each case use the prefix `triproof-` followed by the six free bits. All three extracted proofs returned `s VERIFIED`.

The ongoing construction problem asks for any induced 192-edge path in the nine-cube. These eight exclusions concern the specified entry and indexed coordinate histories.
