# Upper enumeration and shared-task review

The saved finite upper enumeration and the six task groups match an independent reconstruction. No solver, compiler or software test was run. This review enumerated only the small upper-face graphs and compared immutable saved data. It establishes no compatible lower pair.

## Enumeration checked

Read the complete `prepare_companions.py` source and all saved companion records. Checked their source pins and all seven copied context rows against `regions44.json`. Independently generated upper paths by increasing path length, checking each extension against every pair of path vertices, then reconstructed every permitted prefix/suffix combination and both projected lower domains. All 18 configuration records match, including their endpoint, length, projection and interval fields.

| Context | Upper vertices | Prefixes | Suffixes | Prefix nodes | Suffix nodes | Configurations |
|---|---:|---:|---:|---:|---:|---:|
| 194 | 13 | 1 | 2 | 9 | 4 | 2 |
| 195 | 13 | 1 | 2 | 8 | 5 | 2 |
| 196 | 13 | 1 | 2 | 7 | 6 | 2 |
| 197 | 13 | 1 | 2 | 6 | 7 | 2 |
| 198 | 13 | 1 | 2 | 5 | 8 | 2 |
| 199 | 13 | 1 | 2 | 4 | 9 | 2 |
| 201 | 14 | 1 | 6 | 2 | 26 | 6 |

The enumeration is complete for the stated first suffix `[480]` and a second path with exactly two coordinate-8 crossings. Such a second path consists of an upper prefix, one lower segment, and an upper suffix. Each upper piece is induced, avoids the other endpoint, and ends at an available vertical port. The two upper pieces are disjoint and mutually nonadjacent. The enumerator records every possible port-ending prefix and continues extending it, so stopping earlier at a port does not hide longer alternatives.

For upper pieces containing respectively $l$ and $r$ vertices, the lower segment has $44-l-r$ edges. Including both vertical crossings, the whole second replacement has 44 edges and 45 vertices. The two port projections are distinct, as coincident projections would repeat the same upper vertex. Cross-face adjacency is exactly equality after projection by subtraction of 256. Removing all upper projections from the first lower domain, and all nonport projections from the second lower domain, imposes exactly the relevant vertical-contact prohibitions. Removal of vertex 480 and its neighbors from the second domain ensures compatibility with the fixed first upper suffix.

The common first lower problem has 43 edges from 18 to 224; appending 480 gives its 44-edge replacement. A simple lower path ending at 224 has no other vertical neighbor of 480. The first and second lower paths must additionally be disjoint and mutually nonadjacent in $Q_8$. The source does not establish that such a pair exists.

## Exact grouping and domination

The task key consists of both literal lower-domain lists, the second lower endpoints and its edge length. The common first endpoints and length are fixed separately. Equality of this key gives exactly:

- `[0,2,4,6,8,10,12]`: second endpoints 35 and 201, length 33.
- `[1,3,5,7,9,11,13]`: second endpoints 35 and 208, length 32.
- `[14]`: second endpoints 35 and 212, length 39.
- `[15]`: second endpoints 35 and 208, length 38.
- `[16]`: second endpoints 35 and 201, length 35.
- `[17]`: second endpoints 35 and 201, length 33.

Both domains of configuration 17 equal the corresponding domains of configuration 0 with vertex 212 removed. Endpoints, lengths and lower-path compatibility requirements are identical. Every lower pair satisfying configuration 17 therefore satisfies configuration 0. Dropping configuration 17 loses no existence possibility in the combined construction search. This does not identify their upper routes, classify all full witnesses, or preserve configuration-by-configuration solution counts.

## Reconstruction in all seven contexts

For each of the first two groups, symbolic substitution of the same two lower paths into the seven saved upper arrangements and retained seed portions gives a literally identical 193-entry sequence. This was checked using distinct placeholders for all unspecified lower-path interior positions. Thus a pair solving group 0 or group 1 produces the same full sequence in each of its seven represented contexts, rather than relying on a cube symmetry.

Concretely, append 480 to the first lower path. Form the second replacement by concatenating its saved upper prefix, the lower path including both ports, and the saved upper suffix. Insert those replacements at the recorded intervals of the same seed, retain all other original positions, and append vertex 24. The original fixed portions contribute one coordinate-8 crossing, the first replacement contributes one, and the second contributes two, totaling four. Endpoints 0 and 24 have even parity, consistent with 192 edges.

This reconstruction claim assumes induced lower paths in their literal domains and their mutual disjointness and nonadjacency. It also inherits the sufficiency of the original prepared-domain restrictions for retained-vertex contacts and anchors. The resulting concrete sequence must still receive the independent full pairwise witness audit before acceptance.

## Scope qualification

Suffix `[480]` is not forced by the raw first domain alone. Its target upper component is `{480,488}`, allowing the alternative suffix `[488,480]` through lower port 232. The selected seven contexts have saved native infeasibility results for that alternative in round 226 `data/ports44-232.json`; this review confirmed their seven recorded statuses, without replaying the solver contradictions. Likewise the present enumeration takes the selected first-one/second-two crossing allocation as its stated family. It is not an enumeration of every width-44 pair or every Q9 snake. The plan's reduction to the remaining family retains its earlier native-evidence qualifications.

The upper enumerator and this finite reconstruction have no Lean traversal certificate. No deficiency was found in the inspected enumeration or proposed grouping.

## Source pins

- `scripts/prepare_companions.py`: `2e556e4d76563ae01af397f96f53daa66bd810e1197070cec887cb2912618ff0`
- `data/companions.json`: `301a7bc1fd4aac979d86729d9ecde695be39a808b9dbb6617a3e33390eade8dd`
- `data/shared-q8-plan.json`: `38b68481c0db19dee53410ac64ba25601e7d44bc35110e267e1b81f781c45eda`
- `data/regions44.json`: `c2c5b1465726c4e8c2ab142a1524e171cfeb992cb66d906475e9d1e2e766ec0b`
- Round 226 `data/ports44-232.json`: `4e854615c0e14dd818be81e97fbef8b2c733a443c32b343e0baba08481600073`
