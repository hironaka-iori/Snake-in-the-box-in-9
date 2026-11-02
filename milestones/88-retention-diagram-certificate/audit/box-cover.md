# Exact rejection-box construction

## Result

The complete retained code sets factor into **505 base direction cases and exactly three history modifications**. The constructed complements agree exactly with all **791 compatible saved blocks**, all **37,084 incompatible blocks are empty**, and the accepted rows total **4,947,008**. Every comparison also agrees with the previously saved six-way membership diagram. No weights, solver jobs or Lean compilations were involved.

A further reduction is available at the level of geometry: **all 127 saved-set classes admit an exact rejection cover using boxes available in every context of the class**. The selected common covers use **82,659 class-box occurrences**, compared with **356,548 direction-box occurrences** in the stronger direct pruning run. This allows the geometric coverage check to be organized by 127 membership classes. The local-rule witnesses remain context dependent; the class payload records an example original witness and verifies availability by intersection, without materializing a witness list for every context.

These are computational data results. They do not close the Lean finite coverage premise, the reference-catalogue premises, the weight interpretation or a global upper-bound proof.

## Reproducible artifacts

- `scripts/build_boxes.py`: current generator; run with `--max-gain` to reproduce the strengthened variant and class-intersection test.
- `data/box-cover-selected-max-gain.json.gz`: selected geometry catalogue, all 505 direct covers, three history modifications, all 791 block mappings and all 127 common-class covers.
- `data/box-cover-audit-max-gain.json`: exact checks, counts, input hashes and generator hash.
- `data/box-cover-selected.json.gz` and `data/box-cover-audit.json`: preserved descending-volume baseline, unchanged by the stronger run.
- `data/box-cover-baseline-source.json`: exact baseline generator source as normalized text with recorded CRLF restoration and matching source hash.
- `data/box-cover-failure-01.json`: initial failed preparation receipt and source, preserved before correcting the filename of the existing `NumericRetention-audit.json` receipt. That failure occurred before constructing boxes.

The final successful run took 26.906 seconds. It rechecks all input hashes before writing success. The current generator source and the max-gain receipt match. The baseline used an earlier source version; its exact bytes can be reconstructed from the preserved baseline-source record. The current default mode retains descending-volume selection, while `--max-gain` selects the stronger run and writes separate files.

## Rule conversion and indexing

A box is a list of six inclusive intervals with endpoints in 1 through 6. Coordinate zero is the most significant stored count symbol. Unconstrained coordinates use [1,6]. The six-symbol code is the same base-six encoding used in milestone 87, after subtracting one from each symbol.

Each selected occurrence retains a source witness with family, exact Lean-list index, offset and reversal flag where applicable. Reference witnesses also retain the source catalogue and its index; short and interval witnesses retain original case numbers. Sum witnesses retain the explicit assignment used to create the box.

| Family | Conversion | Index and offset meaning |
| --- | --- | --- |
| Reference | Each required symbol becomes a singleton interval; remaining coordinates stay [1,6]. | Index in the ordered 1,378-entry `referenceKeys`; count offset s corresponds to direction start s+2. |
| Short cap | Each tested position receives [1,cap], intersected with any repeated constraint. | Index in `capRules ++ sumRules`; offset is the direction-window start. Reversal maps position j to L-j. |
| Short sum | Enumerate all assignments in 1..5 to the tested positions with sum at most the stated cap; each assignment gives singleton intervals. | Same short-rule index and position convention. Assignment entries retain the original rule-position order. |
| Interval | Clip actual interval endpoints to the encoded-symbol domain: lower endpoint at least 1, upper endpoint at most 6. | Index in the ten-entry `intervalKeys72`; s=0,1,2 corresponds to direction start s+2. |
| History | A single tested digit receives [1,2]. | Index in the ordered three-entry `historyRules`; history ID is retained in the witness. |

The sum expansions contain 6 assignments for case 481, 10 for case 482 and 115 for case 501. The restriction to symbols 1..5 preserves the explicit unsaturated guards; it does not interpret symbol six as an exact actual count of six. Interval clipping is valid for the inspected catalogue, whose upper endpoints are below six or equal to 21.

The direction match and bounds for every selected witness are reconstructed from its original row and checked. No box was enlarged by merging unrelated source rules. Every selected direct box therefore remains associated with one concrete original rejection occurrence.

The generator verifies the list orders against current Lean source text:

- All 22 reference chunks concatenate in the declared order. Every key literal agrees with the corresponding row of `85/data/reference-union.json`, and every pick agrees with its saved source catalogue/index.
- The 37 cap literals and three sum literals agree with the normalized rows in their exact concatenated order. This avoids using the interleaved order of the original milestone 48 cases.
- All ten interval literals agree in order with the saved applied-case list.
- History indices 0, 1 and 2 agree with signatures [139,353,177], [460,350,180] and [460,353,177], and digit indices 5, 3 and 5.

`NumericRetention.lean`, its source receipt, the relevant literal-list sources and all source JSON files are pinned in the final audit. These are executable source/data comparisons; no theorem equating the Python implementation with Lean is claimed.

## Exact factorization by history

For each direction, the base rejection union comprises all reference, short and interval boxes and corresponds to history zero. Source compatibility is checked for every one of the 37,875 direction/history pairs. For all 791 source-compatible pairs, the computed target history is also compatible. The only additional rejection boxes are:

| Direction | History | Lean history-rule index | Digit | Newly rejected codes |
| --- | --- | --- | --- | --- |
| 177 | 43 | 0 | 5 | 1,625 |
| 177 | 70 | 2 | 5 | 1,625 |
| 180 | 68 | 1 | 3 | 629 |

All other compatible histories have exactly the base direction's accepted set. The 505 base directions use 125 distinct saved membership classes; the history modifications yield the full 127 classes. The two modifications on direction 177 have the same geometry, with different signature witnesses.

The complete source graph is `72-four-count-proof-closure/critical-current/build/source-graph.npz`; its compressed SHA-256 is `b40f1ca44ad8f3269f890efe8decc60f19dabd647f11255c05df3727341c2c34`. The source metadata and raw direction, history and code hashes are verified before decoding any blocks. Complements are compared against both direct saved code slices and the independently stored roots of `87/data/coverage-membership-dag.json.gz`, SHA-256 `5ded4dbe27d3ba795e57e241289facce6444789e30edb9531a312fab58818823`.

## Pruning and its limits

The baseline already sorted boxes by descending volume before selecting boxes contributing an uncovered point. It then removed redundant selected boxes in reverse order. The stronger variant uses a priority queue with lazily recomputed uncovered-point counts, selecting a maximum current contribution with deterministic tie breaking, followed by the same reverse deletion.

| Stage | Descending-volume baseline | Maximum-uncovered variant |
| --- | ---: | ---: |
| Raw occurrences | 573,640 | 573,640 |
| After exact duplicate removal within each direction | 543,829 | 543,829 |
| After forward union selection | 365,523 | 358,672 |
| After reverse redundancy deletion | 357,917 | 356,548 |
| Distinct selected geometries, including history additions | 2,635 | 2,637 |
| Smallest direct cover | 302 | 302 |
| Largest direct cover | 965 | 963 |

Every final direct cover preserves the entire raw rejection union. Every remaining box has a saved private code which belongs to that box and no other box of the final cover. Thus no final box is contained in another selected box or removable without changing that union. This is inclusion minimality for the selected collection, not minimum cardinality among all possible source boxes.

Maximum-uncovered selection removes 1,369 additional occurrences. Its final occurrences divide into 337,437 reference, 16,331 short and 2,780 interval witnesses, plus the three separately stored history modifications. The high occurrence count is a real remaining cost; the common geometries and membership classes provide more compression than the change of greedy order.

The baseline payload is 4,208,880 compressed bytes, with 53,148,320 uncompressed bytes. The max-gain payload is 5,003,124 compressed bytes, with 66,473,584 uncompressed bytes; it is larger because it additionally contains the 127 common-class covers and their example witnesses. Box geometries are stored once in a shared catalogue and referenced by integer ID.

## Common-class cover test

For each of the 127 saved membership classes, the generator intersects the complete raw box-geometry sets available in every compatible context belonging to that class. This uses all 791 contexts; 107 classes contain multiple contexts. Common sets have between 580 and 1,649 available geometries. In every class, the union of these common boxes equals precisely the omitted code set. No rejected code is uncovered, and no accepted code is covered.

Applying the same pruning algorithm to these intersections selects 82,659 class-box occurrences, between 302 and 963 per class. This is 273,889 fewer occurrences than repeating the direct covers. The `class_intersections` payload field supplies the contexts, common-geometry count, selected box IDs, example original witnesses and exact zero-uncovered result.

This supports one geometric coverage check per membership class. It does not supply one universal source-rule witness for all contexts: the same geometric box can arise from different rule indices, offsets or orientations. Each class-selected box has an example witness from its first context; availability in every other context was checked by exact intersection. Materializing or checking those context-specific witnesses remains an input to the next Lean certificate stage.

## Next certificate boundary

The desired checked implication is one-sided: numeric acceptance implies acceptance by the assigned membership root. An exact box complement is stronger computational evidence. For a given context, each selected box must be shown to imply a concrete source rejection, and the geometric cover must be checked against the membership diagram. Combining these statements excludes every omitted code under `numericKeep`. The membership and row-index interfaces from milestone 87 can then be applied.

The box-generation stage does not instantiate or compile that implication. The
stored `Snake9.Boxes88.Witness` indices identify its original rule rows. Later
in this milestone, Lean checked the generic witness and coverage argument,
then the direction-0/history-0 pilot with 375 witnesses. See
[the pilot receipt](../data/Case000Checks-audit.json) and
[the integrated summary](../data/proof-summary.json). All-context certification
remains open. The two reference refutation premises, full-key row coverage,
column identities and later charge/potential obligations retain their existing
status. No optimum, new snake construction or improved global bound is asserted.

## Saved hashes

| Artifact | SHA-256 |
| --- | --- |
| Current generator | `3ec1d2c50d924421209ee85f9d891b703e04bf916fbb47defdf704df3a7a2a2e` |
| Max-gain audit | `e4d9023ee24c8d706cc83886ca7865c45c4b4dd6a98c1d0b1b5bbd0f59c5cd39` |
| Max-gain payload | `c81ab4d006d9f40e74b1b3ed1c655b11282e96db8bd8242975042414f7090e93` |
| Preserved baseline audit | `5c45deeb9079b7afd84b6115d31f73cd1060ce7cec4ffe2d33c2a33054c25651` |
| Preserved baseline payload | `4063dc58ec6ccdcd1236318f5d0a88e808e110c6163cfbb974caf9609f451d35` |
| Exact baseline source record | `02adcea3c5f3ba59f97bd478bae524c00c26da34cb72a2b752e411a675ce96ee` |
| Preserved initial failure/source | `2bca3e15ab3d565dea42a62413ef629e689437c1ce1739a2516016ed0e38f3c1` |
