# Audit of the forty recovered short rules

Reviewed 2 November 2026. This report identifies the existing closed local theorems used by milestone 70 and their precise count/index interfaces. It does not establish their new combined retained-edge theorem, replay imported dependencies, or claim a new global bound.

## Inventory and exact source matches

The enriched builder `milestones/70-proof-supported-share-model/scripts/build.py` reads three cases files and appends sum rule 501. Its `data/enriched-model.json` contains exactly 40 `additional_proved_rules`:

- Three single-count exclusions: 471, 472, 473.
- Thirty-four componentwise pair exclusions: 483 and 4901 through 4933.
- Three sum exclusions: 481, 482, 501.

The actual builder rows were compared with their current Lean directions and bounds/sum statements. All 40 match. Every selected position j satisfies 0 < j < L, where L is the number of directions in its rule. The direction lengths are four for one rule, six for 36 rules, seven for one rule, and eight for two rules.

### Single-count and sum rules

| Rule | Direction word | Selected local positions | Excluded test on actual counts | Closed theorem |
|---|---|---|---|---|
| 471 | 012304 | 4 | alpha_4 <= 1 | `CycleWindow471.refuted`; `SingletonPatterns.exclusion471` |
| 472 | 0123041 | 1 | alpha_1 <= 1 | `CycleWindow472.refuted`; `SingletonPatterns.exclusion472` |
| 473 | 01230243 | 7 | alpha_7 <= 1 | `CycleWindow473.refuted`; `SingletonPatterns.exclusion473` |
| 481 | 012301 | 1,5 | alpha_1+alpha_5 <= 4 | `JointIntervening481.sum_in_snake` gives lower bound 5 |
| 482 | 01230410 | 4,7 | alpha_4+alpha_7 <= 5 | `JointIntervening482.sum_in_snake` gives lower bound 6 |
| 501 | 012340 | 1,4,5 | alpha_1+alpha_4+alpha_5 <= 12 | `JointIntervening501.sum_in_snake` gives lower bound 13 |

All theorem names in this section are within `Snake9.LocalWindow`. The single-count builder condition is equality of the recorded symbol to one, which is covered by the stronger actual-count exclusion at most one. Its case data use the interval (0,1) at the selected position and (0,21) at every other internal vertex.

The three sum theorems are in `lean/SumWindow481.lean`, `lean/SumWindow482.lean` under milestone 48 and `lean/SumWindow501.lean` under milestone 50. Each `sum_in_snake` takes an arbitrary snake, start r, coordinate permutation P, a fitting-window hypothesis and the exact permuted directions. It has no supplied singleton-count bounds: its proof derives the universal internal bounds. Each file also contains the arbitrary-coordinate wrapper `low_count_sum` and the local contradiction `local_sum_excluded`.

### Componentwise pair catalogue

For each N, `Snake9.LocalWindow.CycleWindowN.refuted` is in `lean/CycleExclusionN.lean`; the same file also provides `excluded_in_snake`. The 49 cases additionally have `Snake9.LocalWindow.PairBasisN.exclusion` in `lean/PairBasisN.lean`. Case483 has `LowCountCompatibility.asymmetric_exclusion` in milestone48. The table lists the two actual count caps, in the same order as the selected positions.

| Rule | Direction word | Positions | Caps |
|---|---|---|---|
| 483 | 012342 | 1,5 | 3,2 |
| 4901 | 0120 | 1,3 | 2,2 |
| 4902 | 012031 | 1,4 | 2,2 |
| 4903 | 012031 | 1,5 | 2,3 |
| 4904 | 012031 | 1,5 | 3,2 |
| 4905 | 012032 | 1,3 | 3,2 |
| 4906 | 012032 | 1,4 | 2,3 |
| 4907 | 012032 | 2,4 | 3,3 |
| 4908 | 012032 | 2,5 | 3,2 |
| 4909 | 012032 | 3,5 | 2,3 |
| 4910 | 012034 | 1,3 | 3,2 |
| 4911 | 012034 | 1,4 | 2,2 |
| 4912 | 012034 | 1,5 | 2,3 |
| 4913 | 012034 | 2,4 | 2,2 |
| 4914 | 012301 | 1,5 | 2,2 |
| 4915 | 012304 | 1,5 | 2,3 |
| 4916 | 012304 | 1,5 | 3,2 |
| 4917 | 012304 | 4,5 | 2,2 |
| 4918 | 012310 | 1,2 | 2,2 |
| 4919 | 012310 | 1,3 | 3,2 |
| 4920 | 012310 | 1,4 | 2,2 |
| 4921 | 012310 | 2,4 | 2,3 |
| 4922 | 012310 | 2,4 | 3,2 |
| 4923 | 012310 | 2,5 | 2,2 |
| 4924 | 012310 | 3,5 | 2,3 |
| 4925 | 012310 | 4,5 | 2,2 |
| 4926 | 012340 | 1,2 | 2,2 |
| 4927 | 012340 | 1,5 | 2,3 |
| 4928 | 012340 | 1,5 | 3,2 |
| 4929 | 012340 | 4,5 | 2,2 |
| 4930 | 012345 | 1,2 | 2,2 |
| 4931 | 012345 | 1,5 | 2,3 |
| 4932 | 012345 | 1,5 | 3,2 |
| 4933 | 012345 | 4,5 | 2,2 |

The first pair rule 4901 is the four-direction basis word 0120, not the six-direction survey extension. Use its basis certificate or its `PairBasis4901.exclusion` directly. `SurveyCatalogue.lean` contains derived applications with longer direction words; it is unnecessary for reproducing the builder's smaller basis.

All selected component caps in this forty-rule family are 1, 2, or 3. There is no selected cap-six case. Unselected count bounds are (0,21). `SumWindow4934` and survey-only consequences are present in milestone49 but are not extra rows in this builder's forty-rule input.

## Canonical, reversal, and digit interfaces

Let r be the start of the actual nine-direction window and o the Python `offset`. A rule of length L is considered only for 0 <= o <= 9-L. Its forward direction piece is the list d_o,...,d_(o+L-1). The canonical comparison is `canon(piece)=rule.dirs`; in the reversed branch it is `canon(piece.reverse)=rule.dirs`.

A selected local position j corresponds to actual vertex r+o+j in the forward branch and r+o+L-j in the reversed branch. The builder sets

\[
t=o+j\quad\text{or}\quad t=o+L-j,
\]

and applies the rule only when every selected t lies between 3 and 8. Its six-count column is t-3. Therefore `actual_digit p r (t-3)` gives precisely the truncated actual count at r+t, with no off-by-one shift. Reversal retains the original ordered positions/caps and changes each selected coordinate to L-j; reversing the cap list in addition would double-reverse the association.

For canonical transfer, the existing `actual_canonical_frame` plus `mkPerm_spec` provides the coordinate permutation for any fitting piece. For a reverse application, use `revSnake p` with start m-(r+o)-L; its local vertex j maps to r+o+L-j in the original snake. The bounds 0<j<L, o+L<=9, and r+9<=m place all these vertices strictly inside the snake.

The sparse Refuted cases can use `canonical_interval_exclusion` for the entire L-direction window. Its full bounds list has L-1 entries. Only the selected entries need six-count digits; every other entry is discharged by 0 <= alpha <= 21. This matters for the length-eight rules: seven internal vertices exist, although only selected positions must lie in the six represented columns. The consecutive-six-count interface alone is insufficient for those longer sparse windows.

## Saturation requirements

A selected component cap c<6 transfers safely from `min(6,alpha)<=c` to `alpha<=c`. This covers all current singleton and pair rules. If this family is extended to a selected cap c=6, that implication fails: alpha=7 has clipped value six. Such a rule would need a different guard or a separate exact-count premise. The universal cap21 on unselected vertices is derived geometrically and does not create this problem.

For every sum rule, the builder requires both the clipped sum at most the rule cap and **every selected symbol below six**. This makes each selected symbol equal to its actual count. For 481 and 482, the small sum caps 4 and 5 already imply that every selected nonnegative term is below six; the explicit guard remains compatible. For 501 the guard is essential: actual counts (7,1,5) meet the proved lower bound13, whereas their clipped sum is12. This is an arithmetic counterexample to dropping the guard, not a claimed snake realization.

Milestone50's `TripleDemand.lean` already provides `Snake9.TripleReturnBudget.clipped_exact` and `exact_exclusion` expressing this distinction. The more general excess-demand theorem in that file is outside the current forty-rule deletion filter.

## Existing compiled evidence

All 1,023 source hashes in the four current `data/verification.json` receipts were independently checked against current Lean files. The receipts report status PASS and 207 printed audits in total (12+12+159+24); these counts cover the full prior rounds, including results beyond the forty rules.

For each of the forty direct interface modules (37 `CycleExclusionN` modules and three `SumWindowN` modules), a successful source-matched build record and present compiled object were verified. Reusable build directories are:

| Milestone | Existing build directory |
|---|---|
| 47 | `milestones/47-critical-singleton-patterns/build/991ed269af7a4378bac22445e1ed3112` |
| 48 | `milestones/48-low-count-compatibility/build/a5b04bafa98343e3b943c1c06151d0b5` |
| 49 | `milestones/49-six-direction-pair-catalogue/build/e9a7ff692eb14860a8f1d937622a70bc` |
| 50 | `milestones/50-three-count-return/build/c80b2812b6624e6385cd1667587e75a6` |

These directories agree with the corresponding `build/latest.txt` pointers. Their objects have not been freshly recompiled in this audit. A new combined import should pin the actual objects and their inherited imports, resolving shared module names consistently, before claiming reuse. A present object and old source-matched receipt are the evidence examined here; this report does not supply a clean-build claim.

## Remaining assembly and scope

No missing local theorem or mismatched builder row was found. The next proof obligation is the generic sparse-position transfer and an explicit finite catalogue dispatch covering all forty rules, both orientations, and the builder's represented-position condition. The three sum cases require lower-sum theorem application rather than a `Refuted` predicate for independent componentwise caps. Reference catalogue closure, history exclusions, retained-array membership, credit interpretation, and potential replay remain outside this audit. No new global numerical bound follows from these source checks.

## Receipt fingerprints

- `milestones/47-critical-singleton-patterns/data/verification.json`: `003b29a897a1fd332dc742a7f96284810f520cfbceb0b48d5e8558190a634e20`.
- `milestones/48-low-count-compatibility/data/verification.json`: `83a3b7535cedeaebec6bf967c5a8d311220dfaa62540d34065f33270cddd375e`.
- `milestones/49-six-direction-pair-catalogue/data/verification.json`: `fb119273313a0af5780c7fba30e9af12891a711c287311da9666bf6ea1e36f72`.
- `milestones/50-three-count-return/data/verification.json`: `1eac2108fc1865d5f4e5a1958fef96b8d84d34c1d5a7735b5b34c717f28837cf`.
