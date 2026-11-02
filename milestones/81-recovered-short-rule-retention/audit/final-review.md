# Independent review of recovered-rule retention

Reviewed 2 November 2026. No mathematical defect was found in the new coordinate, count, canonicalization, saturation, or reversal transfers. The checked result is preservation of actual snake windows under the forty recovered short-rule filters. Full retained-array membership, share credits, and the potential theorem remain outside this result.

## Checked modules

Present source, compiled-object, and log hashes were independently matched to successful receipts for the following eight modules. All 66 printed theorem audits use only `propext`, `Classical.choice`, and `Quot.sound`, or a subset. This review did not launch a compiler or replay the imported certificate closures.

| Module | Printed audits | Source SHA256 |
|---|---:|---|
| PositionTransfer | 5 | `fe132c16ef9ed7beb582bfef36e765c483e20dbec1be3534b3bb041ab2e4a6d0` |
| GuardTransfer | 4 | `f3982df26a89e73e4697d66d5f6786bbc6736b772900c238b8ab25810123bffa` |
| CapCatalogue | 38 | `726d4a6c10247ab4a947a4d987f3ee2c8d17172ede922957e1b80373d2ce95a6` |
| JointCountBridge | 1 | `fed68cd5ca9e6aa1bbaa4e9e2532c658d9211a5859267517fbe5715c6887fbdd` |
| JointCountTags | 10 | `803c5b8fcdf56221bc9d526c2fc1959824246080f863c23c4cdd3fdb83a98443` |
| MultiCentreCount | 1 | `07cec2508ae5c467ac129aa70a4ae136ff2d5962cc3571d1c11a61ba8d98bdc9` |
| SumCatalogue | 4 | `7e8d5c9689cf85ee71db00e5d5f309950979b12d5683240fa57a9bb47cc19238` |
| ShortRetention | 3 | `183f7f0b03d9bb037babead394915d5e06c147ea6235e1325d3f0b9985cbe886` |

## Hypotheses and coordinate positions

`oriented_window_fits` and `oriented_count` use the fitting-window hypotheses r+9 <= m and offset+L <= 9. The latter permits j <= L, including endpoints, which is valid for the reversal identity. Its application by `encoded_guard_retention` supplies the stronger catalogue condition 1 <= j < L, so the selected counts are strictly internal.

The orientation conventions agree throughout:

- Forward position: r+offset+j.
- Reverse position: r+offset+L-j.
- Reversed snake start: m-(r+offset)-L.
- Stored digit index: offset+orientedPosition(L,reverse,j)-3.

The represented-position hypothesis constrains the unsifted position to 3,...,8 before subtraction. It therefore prevents natural-number subtraction from collapsing an out-of-range index to zero. `actual_digit` gives exactly the truncated count at that position. The nine-direction canonical slice and its reversed form are matched through the already checked slice lemmas, rather than by assuming that a restricted-growth label remains unchanged after slicing.

`canonical_permutation` follows from the actual-window coordinate frame and maps each actual direction to its canonical label. It adds no coordinate choice as an unproved assumption. The sum wrappers use precisely this permutation with the original closed `sum_in_snake` theorems.

## Guard transfer and saturation

`encodedBad_to_raw` includes the necessary conditions for both branches. For component caps, `smallCaps` requires every cap to be strictly below six. For sums, `encodedBad` requires every selected digit to be below six in addition to the sum cap. These facts make the tested truncated values exact wherever an upper bound or sum contradiction needs them.

The three singletons are encoded as cap-one conditions. `digit_one_iff_cap_one` shows their equivalence to the builder's equality-to-one test, since every digit is at least one. All actual component caps in the catalogue are one, two, or three; none invokes an unsafe cap-six implication.

`caps_from_refuted` fills the full local bounds list. The selected positions receive their cap hypotheses, while unselected positions receive the universal ceiling21. Thus the length-eight cases correctly allow seven internal vertices even though only selected vertices must lie in the six stored positions. The proof does not silently require every internal vertex to be represented.

The sum501 unsaturated guard is retained. Removing it would invalidate the deduction: actual counts (7,1,5) satisfy sum13 while their clipped sum is12. This illustrates the arithmetic issue and does not assert existence of a snake realizing that tuple.

## Concrete catalogue and final theorem

`CapCatalogue` contains 37 closed cap rules, each instantiated from the corresponding `CycleWindowN.refuted`, and proves both the cap and internal-position hypotheses. `SumCatalogue` contains the remaining three rules from the closed 481, 482, and 501 lower-sum theorems. Their sum bounds are respectively 5, 6, and 13, with the builder's forbidden caps 4, 5, and 12.

`shortRules` is the concatenation of these two lists. `short_rules_length` checks length40. The final `all_short_rules_retained` quantifies over every snake, every fitting nine-direction window, every listed rule, every fitting offset, and both orientations. Once the shape and represented-position conditions hold, its encoded forbidden test is false. It has no unproved local-refutation premise. The rule order differs from the builder's original list because sums are grouped together, which is harmless for a conjunction of exclusion filters and is covered by the Boolean-mask comparison.

This is a concrete theorem about these forty filters. It is not a theorem that the resulting edge belongs to the complete saved graph. Reference catalogue filters, history exclusions, array lookup, credits, and potential assembly remain separate obligations.

## Exact-builder comparison

The comparison script was read in full. It extracts the actual enriched short-rule loop from the milestone-70 builder's Python syntax tree, executes that loop, and compares its deletion mask with a second implementation using the normalized literal Lean catalogue. It covers every supplied direction shape and every six-count code. The saved successful receipt reports:

- 505 direction shapes and 46,656 codes per shape, or 23,561,280 pairs.
- 7,927 applicable rule placements, including orientations.
- 9,102,995 pairs retained and 14,458,285 rejected by this isolated filter family.
- Mask SHA256 `1ff64848a9814704b92da43de676f5b2e75145315bdd7450d8fa46734acd9e94`.

The receipt's recorded source hashes were independently compared with current files. The first implementation uses the saved `additional_proved_rules` from milestone70. Independently of that script, this review reconstructed the rule list directly from the current47/48/49 cases files and the explicit501 rule and verified exact equality with the saved list. Thus no current input mismatch was found.

The comparison's input-provenance coverage was reported to the parent for strengthening: the original saved model and direction-table input should be pinned alongside the normalized catalogue, and the direct-source rule reconstruction should be included in the reproducible checker. The existing comparison already checks the exact isolated loop for the supplied current data; the requested strengthening makes subsequent drift detectable without this separate review.

The mask counts describe direction/count pairs before histories and the other filters. They must not be described as newly removed graph edges or new impossible global snake lengths. The comparison is an exhaustive Python check of this loop's conventions, separate from a Lean model of Python execution. No full graph rebuild was performed in this review.

## Conclusion

The checked theorem closes the forty-rule retention family under its explicit placement conditions. The reviewed statements preserve all necessary count-saturation and reversal assumptions. No new local inequality, novelty claim, stronger global bound, or exact optimum is established by this assembly step.


## Resolution of the input-provenance recommendation

The updated checker reconstructs its rule list directly from the current milestone47,48,49 cases files plus the explicit501 rule, then requires exact equality with the saved builder inputs. Its new receipt pins the checker itself, original builder, saved model, direction extension table, all three cases files, normalized rules, and the three Lean catalogue/retention sources. All eleven current input hashes were independently matched to that receipt.

The successful rerun records `reconstructed_source_rules_match: true`, the same 23,561,280 candidate pairs, 7,927 placements, and unchanged mask hash `1ff64848a9814704b92da43de676f5b2e75145315bdd7450d8fa46734acd9e94`. This closes the provenance recommendation. No outstanding defect remains from this bounded review. The exhaustive comparison and Lean checks were not rerun by the reviewer.

Updated comparison receipt SHA256: `6228259d000020c276dc123830389b877f34fad5241dba9668ab3121ff5d5d0b`.
