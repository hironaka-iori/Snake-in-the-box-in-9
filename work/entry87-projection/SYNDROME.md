# Recovering an entire parity class from neighbour counts modulo two

For a set S of vertices of one parity, define D(S) to be the opposite-parity sites having an odd number of neighbours in S. This changes the coordinates of the search space. A single edit of D(S) changes all nine neighbours of that site in S.

**Inversion lemma.** In every odd-dimensional cube, D(D(S)) = S. In a two-step walk from x back to x there is one choice for the flipped coordinate in each of the d directions. A vertex at distance two from x has exactly two two-step walks from x, since the unequal directions may be taken in either order. No other vertex is reachable in exactly two steps. Modulo two, the d walks retain x and all the pairs cancel. The argument works on arbitrary vertex sets.

Both D and its inverse preserve symmetric difference. Thus allowing r syndrome changes means selecting r arbitrary opposite sites T and replacing the anchors by S symmetric-difference D(T). Every such perturbation is represented exactly once. In odd dimension |D(T)| and |T| have the same parity because each element of T contributes an odd number of incidences. Relative to a 96-anchor source, odd r can therefore reach the larger 97-anchor class of a 192-edge snake. Even r can reach its smaller 96-anchor class.

[Lean proof](CubeSyndrome.lean) derives linearity and the square of this operator by splitting the cube into two faces. The cross terms occur twice and cancel. In dimension zero the operator is zero, so its square alternates between zero in even dimension and the identity in odd dimension. This formalizes the inversion lemma in every dimension.

### Distance from the 131 actual bank snakes

Every 191-edge bank snake has 96 vertices of each parity. Across its 262 labelled sides, there are 145 distinct coordinate sets. Use each side in turn and permit an entirely new order and an unrestricted opposite parity. For r=0, keep the source set and ask whether it can be the smaller class of a 192-edge target. All 145 fail the [Hamilton characterization](PARITY_SETS.md). For the positive radii the exact counts are below.

| Number of changed syndrome sites | Distinct indexed trials | Target size attained | Pass degree and connectivity |
|---:|---:|---:|---:|
| 1 | 37,120 | 4,493 | 0 |
| 2 | 4,732,800 | 383,194 | 0 |
| 3 | 400,710,400 | 36,353,232 | 0 |

Consequently **for every bank snake, the syndrome of each parity class of any 192-edge snake differs from the corresponding bank syndrome at four or more sites**. This compares labelled sets in one coordinate frame. Since the target is arbitrary, the same lower bound applies after any cube isometry of either path.

This is distinct from a bound on changes of the original vertices. Four independent changes of checks may move many vertices, and shared neighbours can cancel. The native census tests the precise final cardinality before rebuilding the affected support graph. A hypothetical path must give a connected graph with maximum two leaves, with any forced endpoint of the smaller class marked by a private witness. All three positive radii already fail these necessary tests. [Rank-three enumerator](syndrome.cpp), [input reconstruction](syndrome.py), [radius one](syndrome-1-0-131.json), [radius two](syndrome-2-0-131.json), [radius three](syndrome-3-0-131.json).

### All checks in any four-dimensional face can be changed

Allow any subset of the eight same-parity sites of any Q4 coordinate face to change. A lower-dimensional support may be contained in several faces, so the exact survey deduplicates supports as coordinate sets. For support sizes 4, 5, 6, 7 and 8 there are respectively 255,360, 225,792, 112,896, 32,256 and 4,032 distinct supports of a given parity. A translation by one bit puts either parity into the same catalogue. The 630,336 supports applied to 145 distinct reference sets give 91,398,720 trials. Of these, 6,089,026 attain the required anchor count and only two pass the first degree test. Both yield degree contradictions in the reconstructed Hamilton graph.

Combined with the radius-three proof, **the changed syndrome sites on each parity must span at least five coordinate directions**. Indeed their smallest coordinate face fixes precisely the coordinates in which the sites all agree. The entire even or entire odd class of a held-out four-face can span only its four directions. All orders on both parities were free. [Support catalogue generator](syndrome_face.py), [native scan](syndrome_face.cpp), [literal reconstruction](run_syndrome_faces.py), [results and exceptional supports](syndrome-faces-0-145.json).

### Distance on the original vertices

There is also a direct statement about the larger parity class. Relative to either 96-member parity set of any known 191-edge snake, a 97-member parity class of a 192-edge target omits at least two original sites. Keeping all 96 and adding one gave 23,200 trials on distinct base sets. Removing one and adding two gave 177,062,400 trials. All 53 and 661 survivors of the initial filter, respectively, were excluded by graph reasoning. Of these, four and 23 needed explicit binary edge decisions. An independent Hamming-distance implementation verifies their small certificates and those for the unchanged smaller sets. [Enumerator](source_growth.py), [simple additions](source-growth-0-0-131.json), [one deletion and two additions](source-growth-1-0-131.json), [proof trees](source-growth-1-0-131-trees.json), [verifier](growth_proofs.py).
