# A computer-assisted upper bound of 231 edges for a nine-cube snake

An induced path in the nine-dimensional cube has at most **231 edges**. The repository includes an induced path with 191 edges. Together these give **191 ≤ a(9) ≤ 231**. The upper bound follows from a statement about disjoint paths in one lower dimension.

### The 117-vertex obstruction

Write Qₙ for the graph of binary strings of length n, with two strings adjacent when they differ in one position. A linear forest is an induced subgraph whose components are paths. A one-vertex component is allowed.

**Finite lemma. Every induced linear forest on 117 vertices of Q₈ has at least 14 components.**

Suppose a nine-cube snake contains 232 edges. Each edge changes one of nine coordinates. Some coordinate changes at most floor(232/9)=25 times. Cutting the path at those edges makes at most 26 runs. The runs alternate between the two eight-dimensional faces, so each face contains at most 13 runs. Because the path is induced, a run has no chord and separate runs in the same face have no edge between them. Among the 233 vertices one face contains at least 117. Repeatedly removing a tip or an isolated vertex gives a 117-vertex induced forest with at most 13 components. This contradicts the lemma. Every longer snake contains an induced 232-edge prefix.

### Proof of the finite lemma

A forest with 117 vertices and at most 13 components has at least **104 edges**. A seven-dimensional face contains at most 64 of its vertices. Indeed, an exhaustive check of the 65,536 subsets of a four-cube gives a maximum of eight vertices for an induced linear forest; partition a seven-cube into eight disjoint four-cubes.

First fix a seven-face whose population is between 61 and 64. The first four rows of the table give every possible shape up to translation and coordinate permutation. For each shape the opposite seven-face is free. The certificates exclude a total of at least 104 edges at total population 117. Thus every face has at most 60 vertices. Since opposite faces partition the 117 vertices, every face has at least 57.

Now count incidences between edges and the sixteen seven-faces. An edge changes one coordinate and lies in one face perpendicular to each of the other seven. The faces count at least 7×104=728 edge incidences. Sixteen faces each having at most 45 edges would account for only 720. Hence one face has at least **46 internal edges**. The last four rows give every such shape at the remaining populations. Again each excludes 104 edges with the opposite face free. This proves the lemma.

| Vertices in the fixed seven-face | Shapes | Scope |
|---:|---:|---|
| 64 | 6 | All forests |
| 63 | 18 | All forests |
| 62 | 192 | All forests |
| 61 | 1,630 | All forests |
| 60 | 147 | At least 46 edges |
| 59 | 212 | At least 46 edges |
| 58 | 256 | At least 46 edges |
| 57 | 339 | At least 46 edges |

### How the finite checks work

The seven-cube census joins two six-dimensional faces. It fixes the denser face up to cube isometry and enumerates placements of the other. The degree checks include the edge at every common address. A graph traversal removes cyclic joins. The symmetry group fixing the first face yields the true multiplicities. The final canonicalizer checks each orbit size against its stabilizer. Two implementations of the join, one testing pairs directly and one indexing allowed intersections, gave identical edge-rich catalogues for 57 through 59. Independent counts obtained by adding and deleting one vertex also agreed for every edge-rich shape at 57 through 60. [Enumeration](near_full_faces.cpp), [canonicalization](seven_face_classes.cpp), [cross-population checks](edge-rich-extension-audit.json).

For a fixed lower face F and an upper selection U, the total edge count is e(F)+e(U)+|F∩U|. The integer certificates bound this quantity by adding inequalities on small blocks. Every local pattern used in a bound is enumerated explicitly. The verifier checks the integer weights and charges any uncovered positive coefficient in full. Template certificates allow a family of lower faces to vary together. The remaining fixed cases use resolution proofs. The auditor reconstructs the clauses from the actual fixed vertices, verifies any cycle exclusions, and passes the proof to a separate checker. [Fixed-face inequalities](forest_orbit_weights.py), [template inequalities](variable_facet_weights.py), [resolution reconstruction](facet_resolution.py), [final case list](edge-window-117-104-all.json), [integer certificates](edge-window-117-104-all.weights.gz).

### Reproduction

From this directory, with Python, NumPy, SciPy, python-sat and a DRAT checker installed, run `python verify_q9_density.py --checker PATH_TO_DRAT_TRIM`. This checks the four-cube maximum, the 62–64 case proofs, the archived 117-vertex inequalities and the final resolution proofs. It also verifies every one of the 18,336 vertex pairs in the 191-edge lower-bound witness. To export the replay inputs directly from an immutable Git commit, run `python checkout_density_proof.py COMMIT OUTPUT_DIRECTORY` and repeat the verification under `OUTPUT_DIRECTORY/work/entry87-projection`. [Replay program](verify_q9_density.py), [clean export](checkout_density_proof.py).

To reconstruct the edge-rich census, compile `near_full_faces.cpp` and `seven_face_classes.cpp` with C++20. The enumerator's arguments `2 richedges 5 7 46` and `2 richfast 5 7 46` produce the direct and indexed marked lists. Pass each marked input and its output filename to the canonicalizer. The unrestricted 59–64 source catalogues are generated by the same enumerator with `2 streammarked 5`. [Dense-face construction](DENSE_SEVEN_RIGIDITY.md), [incidence argument and counts](EDGE_RICH_FACES.md).
