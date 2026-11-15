# Round 230 exact-two-crossing review

Result: no blocking defect found. The inspected preparation covers the eleven selected contexts for exactly two coordinate-8 crossings. This is an independent source and finite-data review; no solver, compiler, software tests, or live-result inspection was performed.

## Inputs and crossing budget

Read `prepare_round.py`, `prepare_lower_pairs.py`, `prepare_pair_worker.py`, and the complete generated `pair_cp.py`. Checked 21 embedded hashes and byte equality of the copied `regions46.json`, `free-summary.json`, and `two-crossing-frontier.json` against round 229. Independently reproduced the generated worker's entire source from its predecessor and the specified replacements.

The source summary has 106 static exclusions, 198 native exclusions for unrestricted crossing count, and eleven open contexts:

`34, 38, 39, 40, 79, 83, 84, 124, 126, 128, 129`.

All 315 baseline rows preserve the original geometry and fields. Only these eleven receive `OPEN`; the other 304 receive `PRIOR_UNRESTRICTED_EXCLUDED`. The previous native exclusion records remain an external premise. This review verifies their copied summary and hash references, without repeating their solver-model audits.

The old `replacement_crossings` field equals four minus the retained crossing count. Subtracting two therefore gives precisely two minus the retained crossing count. Independently counted retained coordinate-8 edges for every selected context, excluding both replaced edge intervals. The appended edge from 88 to 24 changes coordinate 6 and adds no coordinate-8 crossing.

| Contexts | Retained crossings | Replacement allocation |
|---|---:|---|
| 34, 38, 39, 40 | 2 | \((0,0)\) |
| 79, 83, 84, 124, 126, 128, 129 | 1 | \((1,0)\) |

Parity and face-capacity calculations uniquely give these allocations. The input geometry and its degree/component/parity pruning are independent of the historical four-crossing field. No boundary-change condition is imported. The worker source contains no boundary restriction.

## Complete decomposition and domains

Independently enumerated the finite upper arms breadth by length, checking each arm's distinctness and nonconsecutive adjacencies. Reconstructed all upper combinations, lower endpoints, lengths, domains, and cross-part projection removals. Every saved configuration matches exactly. There are fifteen configurations, fifteen distinct groups, fifteen representatives, no domination records, and no unsupported contexts.

The four zero-crossing first replacements and every second replacement lie entirely in the lower face. Contexts 79, 83, and 84 have the single upper suffix `[488]`. Contexts 124, 126, 128, and 129 each have exactly the two suffix choices `[480]` and `[488,480]`. The corresponding first lower lengths are 46, 45, or 44 edges; all second lower lengths are 46. No singleton lower segment occurs.

For a prescribed upper arm, its projected vertices are excluded from the same lower path except at actual attachment ports. The corrected mask is retained. Independently checked that every remaining lower-to-upper adjacency within each template is an intended crossing. Projections of the other replacement's upper vertices are excluded without exceptions. The worker also removes the other lower path's mandatory anchors and their neighbours, and imposes cross-part equality/nonadjacency restrictions on every selected pair.

These are necessary constraints for the two separated induced lower paths. For a connected solution they are sufficient for the specified assembly: prepared domains already exclude retained outside vertices and their forbidden neighbours, while the upper templates and projection rules handle every cross-face contact. Both replacement sequences have 47 vertices. Substitution into the original 192-vertex seed and appending 24 gives exactly 193 vertices. Independently checked the length arithmetic and retained-plus-template crossing count for all fifteen configurations.

## Selected-vertex worker and reconstruction

The model fixes both anchors, the required selected cardinality, and the parity count. Selected anchors have degree one and other selected vertices degree two. Therefore a feasible selection consists of the anchor path and possibly separate cycles. The cycle inequality requiring at least one cycle vertex to be unselected is valid for every induced-path candidate. The loop preserves all connected candidates while excluding detected cycles.

The reconstruction includes both upper prefixes and suffixes, retains the prescribed outside seed indices, and appends 24. Before accepting a witness it explicitly checks 193 vertices, distinctness and all induced-path adjacencies, and exactly two coordinate-8 crossings. Python assertions must remain enabled. The old final four-crossing assertion was replaced in exactly one location; no other mathematical worker constraint changed beyond selecting the new input file.

The worker's default IDs are exactly 0–14. `COMPLETE_QUERY_BATCH` means all requested tasks received an outcome; any individual `UNKNOWN` or `TIME_LIMIT` remains unresolved. No current native outcomes were read during this review.

## Forced chains and prospective exact reuse

Performed only deterministic necessary simplification: remove closed neighbourhoods of the other path's mandatory anchors, delete nonanchor vertices of degree below two, and extend a path endpoint when exactly one available neighbour remains. This involves no branching path search. Removing a forced first edge reduces the required length by one and removes the old endpoint's closed neighbourhood from the other path. The original endpoint has no remaining possible contact with a nonconsecutive vertex of its own path. Each step therefore preserves existence in both directions, with the removed chain restored afterward.

The resulting forced chains are:

| Configuration IDs | Forced chain |
|---|---|
| 0, 1, 2 | First path begins \(0,1\) |
| 3 | First path begins \(0,1,9\) |
| 7–14 | First path begins \(17,49\) |
| 13, 14 | Second path begins \(52,116\) additionally |

No contradiction follows from these simplifications alone. After reaching their fixed point, three pairs have identical lower domains, endpoints, and required lengths:

| Equivalent IDs | First endpoints / edges | Second endpoints / edges | Domain sizes |
|---|---|---|---|
| 0, 4 | 1 to 232 / 45 | 34 to 195 / 46 | 105, 103 |
| 1, 5 | 1 to 232 / 45 | 36 to 78 / 46 | 110, 100 |
| 2, 6 | 1 to 232 / 45 | 52 to 76 / 46 | 109, 100 |

For each pair, the complete assembled sequence is also symbolically identical. In the earlier context the replacement begins with forced 0 followed by a lower path from 1 to 232, and original vertex 488 follows the replacement. In the later context 0 is retained outside, and 488 is the replacement's upper suffix. The seed values at indices 0, 46, and 47 are respectively 0, 232, and 488. The second interval is unchanged within each pair. This is exact assembly identity, without an assumed cube symmetry or upward transfer of a width exclusion.

Thus a later result for either member of each pair can be reused after recording this explicit reduction. The fifteen raw tasks reduce to twelve distinct tasks under this particular simplification. No worker or input was changed. No broader equivalence or exclusion is claimed.

SHA-256 of the common simplified data, serialized as compact key-sorted JSON with fields `anchors`, `edges`, and `domains`:

- IDs 0,4: `a66b68d87d8f50b974ab550d85f15c3656ab825547b6428097c0fcafe94efde6`.
- IDs 1,5: `bcd2a80e4f90f3403f53a89afabc925e91e61268730e2123cd0a13642d09296c`.
- IDs 2,6: `de5e771c67db079d87621ca25034cea91f1874e3ccd71d497c6147dc10287775`.

## Source and data pins

| Relative path | SHA-256 |
|---|---|
| `scripts/prepare_round.py` | `0aa107a78e96a86a14223afb1669d658d38017aa05065d85acbf069aaef51a41` |
| `scripts/prepare_lower_pairs.py` | `516089a87a620485891054617cc700dbe7c3c2f3800d07dfd6367953cbb7850a` |
| `scripts/prepare_pair_worker.py` | `f01e9381aa2becd24e8f307c7d240f90eb84527e6c736bef158e50e7a9a83389` |
| `scripts/pair_cp.py` | `b1388cfda53753ad4f57d219cf4432cf6064414a6cc6083dea96ecb4b5478116` |
| `data/regions46.json` | `94ea1833e98f07b3f4327b2f06056847474c75dbcda1f30cb2abe7bb4bd9cca6` |
| `data/baseline46.json` | `186f09386a3587d3c047bc463b3a011b79c2614ed4616118a52f33b0caf79726` |
| `data/free-summary.json` | `9b3273c9c0b091d05926effa0165553c7e974f78776fb69b4019de0bca9861bb` |
| `data/two-crossing-frontier.json` | `4a3d9f837bbd05eabe92b33b1614e21955e15414b466d64aba1abf4960fe28df` |
| `data/lower-pairs.json` | `943f2ba9f217fdc591684b50318ac5eb75f1b20e7c5da84c61964138bf9861a3` |

The conclusion is confined to the selected eleven contexts and exact-two-crossing target. Their possible solutions with at least eight crossings remain outside this preparation. Neither this review nor a future exact-two exclusion alone closes the unrestricted eleven-context frontier, proves a new global bound, or supplies a Lean certificate of native traversal.
