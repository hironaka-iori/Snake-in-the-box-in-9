# State and filter subsection: evidence and scope

The draft is `text/state-and-filter-interface.tex`. It contains four propositions with proofs and approximately 1,260 whitespace-delimited words, including displayed mathematics. The existing manuscript was read but not edited. No compiler or solver was run for this writing task.

## Placement and notation

The subsection is intended to follow the existing longest-suffix lemma in `sec:exact-history`, before the current finite-model comparison. It supplies stronger replacements for the old broad statements that direction/history/count interpretation and all exclusion lookups remain unresolved. Integration should avoid repeating the old state description and should retain the existing longest-suffix lemma.

The draft uses the paper's `alpha_i`, `b_i=min(6,alpha_i)` and `sigma_12`, with newly defined `c_r` for the five-count base-six code and `widehat c_r` for the six-count code. Canonical words themselves serve as history symbols, avoiding opaque numeric table identifiers. All fitting-window and terminal-state indices are explicit. No new citation key is introduced; the integration should cite an archival entry covering milestones 77–85 for the finite supplementary tables.

Existing cross-references used: `sec:exact-history`, `lem:longest-suffix`, and `thm:three-forced-corners`. New labels are `sec:state-filter-bridge`, `prop:actual-state-sequence`, `prop:local-filter-retention`, `prop:history-exclusion-retention`, and `prop:reference-union-retention`.

## Statement correspondence

1. **Consistent actual states.** Milestone 77, `ActualDirectionIds` and `HistoryShape`; milestone 78, `NumericTransition` and `StateWalk`. These establish coverage by the oriented shape tables, source/target identity, history updates and compatibility, count coding, and a single state sequence. There are `m-8` candidate steps and `m-7` states, including the terminal state. They do not establish exact retained-array membership.
2. **Interval and short-rule retention.** Milestone 79, `IntervalCatalogue`, `ReferenceRetention` and underlying count-slice/saturation lemmas; milestone 81, `GuardTransfer` and `ShortRetention`. The ten interval filters apply at the three fitting offsets in both orientations. The forty short filters comprise 37 cap tests and three sums. Sum exclusion requires every participating symbol below six. This is essential and is stated in the draft.
3. **Three unambiguous exclusions.** Milestone 84, `HistoryUnique` and `HistoryExclusions`, supported by the earlier generic `HistoryWindow` result and the three replayed count proofs. The three complete eleven-direction realizations are `01230432543`, `01234532013`, and `01234532053`. Their count positions relative to the eleven-direction start are 10, 8, and 10. Relative to the current nine-direction start these become 8, 6, and 8, which are the sixth, fourth, and sixth stored count symbols. The finite uniqueness table covers all 81 possible suffix label pairs below nine; actual-window coverage is proved separately. No unresolved local refutation premise remains in these history-retention statements.
4. **Conditional reference retention.** Milestone 85, `ReferenceUnion`, its 22 finite chunks, and `ReferenceInterface`. The two mathematical premises in the draft are the counterparts of `AllRefuted6K235` and `AllRefuted236`. Each must remain explicit. Compiling the key definitions and proving coverage does not supply either closed refutation proof. The union's 1,378 keys, source-index coverage and valid symbols are checked; the source/JSON audit separately verifies the intersection 641 and 2,678 oriented pairs. These data checks are distinct from the arbitrary-snake argument.

## Receipt inspection

The following current successful receipts were read. For each, its present source, compiled object and log SHA256 values were compared against the receipt and matched. This is an integrity check of existing successful runs, not a fresh compilation or a complete dependency rebuild.

| Milestone and module | Printed audits | Receipt SHA256 |
| --- | ---: | --- |
| 77 ActualDirectionIds | 10 | `552c35112352599431b6639f011f12fe1710b8c9d43841d55276fc3341d26c5c` |
| 77 HistoryShape | 9 | `220dd06eb0a26b90b375d5ec6759988e593b6e9e432f6d0275e2aa66f0e4bc26` |
| 78 StateWalk | 8 | `48bd2a78950b5d3e2a3fd2bff026e8b487f0fdff0744368e91fdf3d2cd870363` |
| 78 NumericTransition | 8 | `3e998e01df7419623bad9ae69f8d9c738e9040ad19b89f9f34e6a88ba10653da` |
| 79 IntervalCatalogue | 3 | `eb66625927e747b1f2a08848b1bb77bf3995e5c0f4843a3ba48fb13d7f2d094f` |
| 79 ReferenceRetention | 6 | `a3e085060e00754d9af8f48f50319dcc249e6d1b5cf1abdd5f6eebddb702ddc2` |
| 81 ShortRetention | 3 | `820b5e3c9c02a1303cf77bad171bad2d4fa4509b59119242e0a7b4c63db2beaf` |
| 81 GuardTransfer | 4 | `ead6d8ef1e292b51fae3e610e0ba7f7f0f313299ea7fd007c6eaf18c64d2e007` |
| 84 HistoryUnique | 3 | `231d5a585425bb6ac3de1cdd1525f14370d53faa784ee49647ed8c024b9978f0` |
| 84 HistoryExclusions | 5 | `0feca227e9fd7a9976dad7a3da0e0a68324aed3fd90488d519e3d436a43aa7bf` |
| 85 ReferenceUnion | 5 | `e748e8f47e967945f39f4f8e7aa7b0170d8a2f73a62c55e33267d9c5e202bc25` |

The milestone 84 and 85 proof summaries were also inspected. They report 38 and 103 printed theorem audits respectively. The current source statements, rather than aggregate counts alone, determine the scope of each prose claim.

## Limits retained in the draft

The exact retained-array entry for every actual step, all assigned credit interpretations, complete potential replay, and both closed reference-catalogue imports remain separate requirements. For general three-window share signatures every compatible eleven-direction realization must be covered; uniqueness is asserted only for the three specified exclusion signatures. Credit bounds concern the same five centres and combine by maximum. No new numerical upper bound, complete graph proof, novelty, or fresh full dependency rebuild is asserted.

This task did not edit either manuscript copy, compile LaTeX, restart a proof process, or alter author or hyperlink settings. The parent task performs integration and the required manuscript compilation.
