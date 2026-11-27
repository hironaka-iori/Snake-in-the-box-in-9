# Opposite arms of a 98-edge parent

Let the fixed arm start at the crossing vertex, translated to zero. The other face may contain any induced path from zero disjoint from the remaining fixed vertices. These conditions are necessary and sufficient. Projected equality at any other site gives a second edge between the faces. Adding the crossing gives a joined length of 99 plus the number of edges in the opposite arm. A join of length at least 192 therefore has a rooted 93-edge opposite prefix.

## Published inputs

Carlson's Appendix C.2, printed page 148, gives 99 node labels in circular order. For a printed label $j$, the reflected Gray word of $j-1$ gives a binary cube vertex. The saved transition word on Rokicki's record page is explicitly attributed to Carlson. The Snakepits data contain another construction from an annealer, as an unordered array of 99 selected vertices. Tracing the degree-two graph from its smaller numerical endpoint recovers the ordered path. Coordinate maps and direct adjacency counts are recorded in the input file. The published optimality theorem concerns length 98. [Carlson's dissertation](https://www.ou.edu/content/dam/CoE/CS/Thesis_Dissertations/2016/Spring%2016/Carlson%20-%20Dissertation.pdf) · [Rokicki's record table](https://www.minortriad.com/snake/) · [Snakepits data](https://github.com/Math-AI-Caltech/Snake-in-the-Box/blob/46c765399353a588ea50444a5d6610f53102b1c2/Snakepits/witnesses.jsonl) · [Östergård and Pettersson](https://doi.org/10.1007/s00373-014-1423-3)

## Reconstructing a long parent

For either ordering $v_0,\ldots,v_n$ of an archived seed, omit $e$ original vertices from the free end. Retain the two ordered blocks $v_e,\ldots,v_i$ and $v_j,\ldots,v_n$, with $e\le i<j$. Allow any new path between $v_i$ and $v_j$, and any new free end before $v_e$, subject to a total of 99 distinct vertices and all induced-path conditions. The parameters bound $e$ and $j-i-1$. Endpoints within a block can coincide when the block is a singleton. For adjacent blocks the joining edge is forced. Replacement sites may include previously omitted sites. An original 97-edge path has endpoints of opposite parity. A length-98 replacement must move at least one of its endpoints.

The first traversal builds the interior from the left block and then the free end. The second first fixes the free-end length, builds that end, then bridges backward from the right block. At every step a new vertex adjacent only to its predecessor among the fixed sites preserves the induced path. At the final bridge site exactly two contacts are required, one with the current tip and the other with the destination. The Hamming distance to the destination is a lower bound on the number of remaining steps. For every valid completion these rules retain each of its partial constructions in both orders. The two traversals compare the complete sets of literal paths and the numbers of embeddings before quotienting by coordinate changes.

A separate reconstruction selects explicit omitted original sites at arbitrary positions. An occupancy-set traversal grows a degree-at-most-two forest, and a traversal of ordered retained blocks explicitly builds its gaps. The two must agree for every omission mask. This second neighbourhood can omit separated vertices without retaining a single long consecutive interval.

## Reconstructing the opposite arm

At a fixed crossing, the construction keeps every vertex of the 98-edge parent. The opposite-side repair preserves two pieces of an earlier valid partner, including the crossing, and rebuilds an interior segment and its free end. Positive paths are checked in the nine-dimensional cube.

The unrestricted search imposes the two parity-class sizes for a prescribed length, degree conditions on selected sites, and a selected starting point. A disconnected cycle cannot lie in an induced path and can be excluded by its vertex set. For a prescribed initial segment, earlier sites and all their neighbours are removed except its last vertex. Translating that last vertex to zero converts the remaining problem to a rooted search. Every fixed-prefix contradiction is replayed from the regenerated formula. A whole-crossing ceiling uses complete coverage of legal initial segments. Any excluded initial segments imported from Round 249 retain their original formula and proof references.

## Exact distance from the 98-edge path

For the fixed set $S$ of 99 occupied vertices, the formula at distance $d$ selects exactly $99-d$ vertices in $S$ and exactly $d$ outside it. Two selected endpoints have selected degree one. Every other selected vertex has selected degree two. The square and three-dimensional face bounds hold for every induced path. If a satisfying set has more than one component, all components except the path are cycles and each can be excluded. A connected solution is traced in its literal coordinates, verified directly, and excluded by the clause forbidding that full occupied set. UNSAT after these exclusions certifies that every solution at that distance has been listed. For radii 1 to 8 the solver needed no cycle exclusions. Seven formulas certify empty spheres directly. The formula for radius 7 proves exhaustion after one verified path.

The orbit calculation first permutes the eight coordinate bits, then translates in reflected Gray order. Each of the $8!$ permutations and $2^8$ translations occurs once. The distance is $99$ minus the intersection size. The identity is the only isometry preserving the occupied set, and the nearest nonidentity image agrees vertex for vertex as a set with the solution at radius 7.

## Independent checks

The site-distance replay regenerates the exact formulas, checks the proof-file hashes and searches the supplied LRAT derivations for valid contradictions. The endpoint replay independently rebuilds the forbidden opposite sites and the allowable first moves. It checks all 16,290 vertex pairs of each 180-edge witness. The final summary verifies the explicit isometry and compares both constructions, up to reversal and cube isometry, to all consecutive windows in the archived 190- and 191-edge path banks.
