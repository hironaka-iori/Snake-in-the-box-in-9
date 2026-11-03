# Saved actual witnesses and the seven-cycle

The screen completed on 135 source entries, representing 135 distinct exact vertex sequences. It found 0 full nine-direction count-and-shape matches and 0 seven-direction suffix count-and-shape matches to the saved conditional-floor18 seven-cycle.

| Row | Nine directions | Count symbols | Full: shape / count-and-shape | Suffix: shape / count-and-shape |
| --- | --- | --- | --- | --- |
| 0 | 012341250 | [3, 3, 5, 2, 6, 6] | 0 / 0 | 910 / 0 |
| 1 | 012301450 | [3, 5, 2, 6, 6, 3] | 0 / 0 | 910 / 0 |
| 2 | 012304530 | [5, 2, 6, 6, 3, 3] | 0 / 0 | 3048 / 0 |
| 3 | 012345230 | [2, 6, 6, 3, 3, 3] | 0 / 0 | 3048 / 0 |
| 4 | 012341254 | [6, 6, 3, 3, 3, 5] | 1 / 0 | 2618 / 0 |
| 5 | 012301430 | [6, 3, 3, 3, 5, 2] | 0 / 0 | 3048 / 0 |
| 6 | 012304235 | [3, 3, 3, 5, 2, 6] | 1 / 0 | 3048 / 0 |

Counts in a nine-transition row belong to vertex positions 3 through 8. The seven-transition suffix starts at direction position 2, so its six counts occupy positions 1 through 6. This alignment was checked against the saved generator, its five-count slice offsets, and the model description. Symbol 6 means at least 6. Count-code decoding was independently checked for all seven rows.

Both path orientations were tested after coordinate canonicalization. For a full nine-direction window, reversing the path changes which six centres occupy positions 3 through 8; the script recomputes those positions instead of merely reversing the original count list. Shape-only hits do not satisfy the count restrictions.

The additional screens found 0 four-distinct-transition windows with three consecutive counts 3,3,3; 0 centres with count 2; and 0 oriented neighbourhoods with counts 5,2,at-least-6,at-least-6. These are subsidiary local tests, not replacements for a complete cycle match.

Every distinct sequence was checked for membership in Q9, distinct vertices, and adjacency exactly at consecutive indices. This checked 2447698 unordered vertex pairs. All 25479 internal counts were computed in two independent ways: the 21 allowed opposite corners and the 36 singleton-square predicates. Identical source sequences were grouped, with every source entry and raw-file hash retained.

The JSON retains all qualifying windows, actual vertices, exact counts, orientations, global endpoints and centre-to-endpoint distances, together with per-witness summary counts and source hashes. It also contains the two actual odd witnesses from milestone133. The full count-and-shape screen is vacuous: none of these witnesses supplies a qualifying full pattern. The suffix count-and-shape screen is also vacuous.

No universal endpoint implication, local exclusion, periodic-cycle realization, or global snake-length bound follows from this finite screen. No solver, Lean process, or full-graph evaluator was run.
