# Next graph update for the 012301 exclusion

## Scope and result

This is a read-only source and saved-cycle review. No graph array, potential array, solver, or Lean compiler was loaded or run. The proposed deletion becomes justified only after the actual-snake theorem for the six-direction word `012301`, with five internal count upper bounds `(3,3,3,5,2)`, has passed its complete proof and semantic checks. The native UNSAT result alone is insufficient.

The minimal update is a new edge-deletion mask. No endpoint premise, parity premise, charge credit, or new weight is needed for this exclusion. All hypotheses already present in the milestone131 profiles remain inherited.

The new mask removes two rows of the saved conditional seven-cycle. These are two representations of one window. The saved completed four-cycle survives with unchanged weights and mean 488. Consequently, deletion alone leaves the completed profile's exact finite-graph minimum equal to 488. The conditional profile's new minimum remains to be evaluated; removing one attaining cycle does not establish a strict increase.

## Exact indexing and deletion rule

The evaluator decodes six count symbols at local vertex positions 3 through 8. Its nine-direction row therefore contains two six-direction windows for which all five internal counts are recorded:

| Placement | Directions, Python slice | Counts, Python slice | Local internal vertices |
|---|---|---|---|
| 0 | `word[2:8]` | `digits[row,0:5]` | 3 through 7 |
| 1 | `word[3:9]` | `digits[row,1:6]` | 4 through 8 |

For each placement, test both orientations. Canonicalize the six directions in their tested order; reverse the five counts whenever the directions are reversed. Delete when the canonical word equals `(0,1,2,3,0,1)` and the five tested counts are componentwise at most `(3,3,3,5,2)`.

The reversed word also canonicalizes to `012301`. This symmetry does not permit omission of the reverse count test: in chronological order its caps are `(2,5,3,3,3)`. A single `shape(...)` test combined with only the forward caps would omit valid reversed exclusions.

Every cap is below 6. A symbol 6 represents an actual count in `[6,21]`, so it cannot satisfy any cap. Thus the componentwise comparison is exact for this mask despite clipping. No interpretation of a symbol 6 as an exact count is used.

For the full graph, the mask can be assembled by the same direction-group loop used at evaluator lines 304–323. Each orientation/placement mask is combined by Boolean OR. An edge matching more than once is removed once. This operation does not add any occurrence count or charge.

## Source hooks

All line numbers refer to the pinned milestone131 files below. Preserve those files and generate the next experiment in a new milestone directory.

1. `scripts/prepare_graph.py`, lines 98–246, contains the generated evaluator suffix. Its lines 162–165 correspond to evaluator lines 347–350. Insert the new mask calculation before selection of retained IDs and change only the final selection from `keep & ~odd_reject & ~six_reject` to `keep & ~odd_reject & ~six_reject & ~short_reject`. Keep `shared` and all weight calculations unchanged.
2. `scripts/evaluate_graph.py`, lines 101–105, supplies the order-sensitive `canon` function and the reversal-insensitive `shape` function. Use `canon` for the paired direction/count orientation test. Lines 156 and 304–317 provide the existing digit indexing and direction grouping.
3. `scripts/prepare_graph.py`, lines 248–258, derives a prefix from milestone124 and appends the suffix. Change the new generator and regenerate its evaluator together. Editing a generated evaluator alone would leave its preparation source inconsistent. Retain the inherited milestone121 removal and full-weight checks at evaluator lines 256–267.
4. Before adding the new deletion, independently reproduce milestone131's exact retained-edge count, removal set, and both retained-weight hashes against its saved result. This identifies deletion from the immediate predecessor, rather than merely comparison with milestone121. Pin the predecessor generator, evaluator, result, and the final new theorem/semantic proof receipts. Record the new mask's unique removals and its intersections with predecessor removals.
5. Evaluator lines 353–359 check the archived completed 18-cycle. The new exclusion has no matches in that cycle, so this particular survival assertion and its milestone131 comparison mean `3011/6` remain valid when all preceding weights and masks are unchanged. The stored milestone121 mean `2915/6` is a different, earlier weight evaluation.
6. Retain the all-edge potential inequalities, exact attaining-cycle check, integer overflow guard, source recheck, resource gate, and preserved failure/timeout records. Their current hooks are evaluator lines 361–413 and the wrapper in `prepare_graph.py`. Report inherited assumptions explicitly; a newly proved ordinary exclusion does not discharge the other assumptions or the full graph-to-snake assembly.

## Saved-cycle comparison

The following checks used only saved JSON rows. Both placements and both orientations were tested for every row.

| Saved profile | Cycle length | Rows removed by the new exclusion |
|---|---:|---|
| milestone131 `completed` | 4 | None |
| milestone131 `conditional_floor18` | 7 | Rows 5 and 6, detailed below |
| milestone121 `completed` | 18 | None |
| milestone121 `conditional_floor18` | 4 | None from this new exclusion alone |

The last row is only a comparison with the new mask; it does not assert survival of that earlier cycle under milestone131's intervening changes.

| Seven-cycle row | Original edge ID | Placement | Tested orientation | Five counts |
|---:|---:|---:|---|---|
| 5 | 992157 | 1 | Forward | `(3,3,3,5,2)` |
| 6 | 1273862 | 0 | Forward | `(3,3,3,5,2)` |

Their position indices satisfy `5 + 1 = 6 + 0`, so these are the same physical window in the consecutive-row period. There is one such window per seven-row period, represented by two graph edges. Neither reverse test creates another match.

The milestone131 completed four-cycle consists of edge IDs `2222328`, `147674`, `2220858`, and `146782`, with weights `480`, `496`, `360`, and `616`. Its two placements have only canonical shapes `012314` and `012032`; neither orientation can equal `012301`. Its weight sum remains 1952 and its mean remains 488.

Restricting the old potential to the retained edges preserves every old potential inequality. The surviving four-cycle therefore supplies the matching upper comparison to the old lower certificate, proving that the completed graph minimum stays 488 without a new graph computation. Under the same comparison formula, even zero potential range gives `68929/293 > 235`; this deletion cannot yield the next completed integer target 234 through that formula.

For the conditional profile, the old potential still proves a graph mean of at least 496. The saved attaining seven-cycle is removed. A new attaining cycle and an all-edge potential certificate are required to determine whether the exact minimum increases. This is the useful next graph calculation once the local theorem is checked.

## Input hashes

SHA-256 values were computed from the current saved bytes during this review.

| Path relative to the repository | SHA-256 |
|---|---|
| `milestones/131-odd-pair-six-count/scripts/evaluate_graph.py` | `86386a1a117dfd9080b7360f9b99a641054fe9ea174baa9a2b532b33199e52ac` |
| `milestones/131-odd-pair-six-count/scripts/prepare_graph.py` | `ea9c46904e1ef1dcccf279cb48d235bde3662902857977d5b0fe160461595391` |
| `milestones/131-odd-pair-six-count/data/odd-pair9-six25/results.json` | `157c1cd0751b487e220b954f441670839c50078167f54c83557f43f98fb8fd2d` |
| `milestones/121-replacement-window-pressure/data/pair-graph/results.json` | `7492ff3a45178740d3253c679bcdd2f5e7907be907f055f455e739cde0b327bf` |
| `milestones/138-seven-cycle-endpoints/audit/cycle-review.md` | `a6a2c1d18c73b06ed0f45c07e65393925657fff4fc69b0b10f33e7f5dbeb0b20` |
| `milestones/138-seven-cycle-endpoints/data/cycle-review.json` | `89417a7bdd902dfd94c09520a74c931dc7a9131b8430d3cf83498f69eec7c79e` |

The local theorem's final source and receipt hashes are intentionally not supplied here: completion of that proof is outside this review. Add the verified final pins before a justified graph update is run. No new actual-snake upper bound is asserted by this note.
