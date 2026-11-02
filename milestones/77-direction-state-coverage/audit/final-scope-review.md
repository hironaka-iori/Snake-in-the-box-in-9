# Final source-scope review

This review inspected the current milestone77 proof sources and available receipts without running Lean or touching the active certificate. No mathematical scope error was found in the proposed actual-direction and history-shape statements. Their completion must be determined from successful receipts for the exact source bytes below.

## Verified receipt status at review

The source, object and log hashes match successful receipts for:

| Module | Printed theorem audits | Receipt SHA256 |
| --- | ---: | --- |
| DirectionTables | 2 | `fd1942673ebc41263a315eadafffad1da8e7b75198a729062b6a88188836e065` |
| PrunedEnumeration | 4 | `9ebf2064ba60e4d4fc1a7064f5b9dbe86cce549015bcf159d07dba67b8af9fbd` |
| NumericHistory | 9 | `d184ac20db41fd280461f9bbe90226fe08ee58f22d172f8c7d1e5bb12306c27f` |

The printed axioms are confined to propositional extensionality, classical choice and quotient soundness. The two table-length declarations have no axioms. NumericHistory's repaired source is `6ce3a0d435def01ac8118296764571ddec51c6d5960c3469327c709b201e4e8d`; its current successful receipt supersedes the earlier failed attempts. Its old README and `history/data/status.json` still describe the earlier draft and must not determine current proof status.

DirectionCoverage was being checked. No successful receipt existed at inspection for DirectionCoverage, LookupTableCheck, HistoryCompatibilityData, ActualDirectionIds or HistoryShape. Their written proofs are therefore reviewed statements, not newly certified results in this report.

## What completion would establish

1. **Canonical coverage.** PrunedEnumeration proves that rejecting a non-induced prefix cannot discard an induced completion. Successful DirectionCoverage checks would establish membership in the recorded lists for every canonical induced eight- and nine-transition word, then apply this to arbitrary snake windows. These are coverage statements. They do not separately prove that every listed entry is induced; the earlier independent Python audit checked that additional table property.
2. **Exact numeric direction IDs.** ActualDirectionIds would show that each valid nine-transition window has an index below 505 and each valid eight-transition window has an index below 132. Decoding returns the corresponding canonical actual directions, so failed-lookup fallback values cannot enter these claims. Its source and target equalities use milestone74's proved slice identities.
3. **A direction-only walk.** `actual_direction_walk` would connect the source and target shape of every actual nine-word ID to consecutive eight-word states. The indexing includes the terminal eight-word state: for a snake of m edges with m≥9, there are m−8 direction edges and m−7 shape states. It contains no count symbols, history block encoding or retained graph-edge index.
4. **Recorded direction maps.** ActualDirectionIds uses the computed functions `sourceId` and `targetId`. The separate LookupTableCheck module must also succeed before invoking `recorded_maps_exact` to identify them with the saved numeric `sourceIds` and `targetIds` lists. Its round-trip and uniqueness statements preserve the exact oriented ordering; reversal classes are not graph IDs.
5. **History recognition.** The now-checked NumericHistory gives an index below 75, decoding, initial index zero, the final-symbol property for nonempty updated histories, and both directions of signature recognition. The generic signature theorem correctly assumes that the signature's proper prefix is listed; it does not assume that the three-symbol signature is itself one of the stored prefixes.
6. **The history-shape filter.** Given successful dependencies, HistoryShape would prove that every nonempty actual history index has the actual eight-word state shape. It would then identify the builder's recorded source and target compatibility values on valid actual windows. Both filters explicitly require nonzero history. The zero entry in `recordedCompatible` is an unused numeric placeholder for the original null entry, and supplies no shape constraint.

The finite Lean literals for shapes, extensions, source IDs and target IDs were compared against the previously audited ordered tables and match exactly. The compatibility source records its original milestone70 values and the zero-placeholder convention.

## Remaining graph interpretation obligations

- Identify the builder's finite numeric history update with the index of the updated longest suffix. HistoryShape defines history by reading the entire actual ID list; it does not yet show that the builder's concrete next-history selection produces that same index. The existing generic suffix and maximum-selector lemmas provide the mathematical basis for this remaining interface.
- Combine direction and history IDs with the actual truncated counts, base-six encoding and conditional state-block formula. Prove that every step has a retained edge in the exact 4,947,008-edge graph and that both endpoint encodings agree with the common state sequence.
- Discharge every exclusion guard with its local theorem, including interval saturation, reversal and history-conditioned exclusions. Direction membership alone does not prevent a real window from being removed by an incorrectly interpreted guard.
- For each recognized three-ID signature, cover every compatible eleven-transition coordinate word. The numeric history theorem does not distinguish forgotten-coordinate returns. Then prove every geometric, count-specific and count-independent credit is a lower bound for the same five actual shares; alternative credits are combined by a maximum.
- Finish pending local share certificates, check the complete finite potential and range, and compose the actual edge walk with overlap and boundary accounting. None of the milestone77 statements supplies those conclusions or a new numerical bound.

## Provenance correction

The earlier audit's apparent history-metadata hash drift compared different files. Milestone74's `source_audit.py`, lines 50 and 74, hashes milestone70's `enriched-model.json`, whose hash is `59a9d5e5f4954b86a69a72c090a9a45030f4756da577457fd94439ace46e102c`. Milestone67's `full-model.json` has hash `08fc18347eff9065d873cb8be01b4b72129e1ee939b4bf1474d04640cc8bc274`. Their relevant history values agree; this comparison is not evidence that either file changed.

## Reviewed pending source hashes

| Source | SHA256 |
| --- | --- |
| DirectionCoverage | `e4463c77964ea11ace876335a18f940c8c683dec46ee99f612cfb97a52bd996b` |
| LookupTableCheck | `b809501aeb29f2d19fdd3ca5d06c380dafd8d0529b763d969994023102e03958` |
| HistoryCompatibilityData | `2cd7533109884d91defe806fb19ec2921da746a37f3eaeaf73d7ba1425c07b8e` |
| ActualDirectionIds | `f0da81617ccbcce214f0a9aa59e57234dc2379eb3671300cfedf9fa6daceacf9` |
| HistoryShape | `07f2c3dbac1305e7838812369954e105c7e82854bd72a898e8414b881c9d427d` |

This review reuses the checked inherited objects and their matching receipts; it does not rebuild their complete dependency closure. Only this report was written.
