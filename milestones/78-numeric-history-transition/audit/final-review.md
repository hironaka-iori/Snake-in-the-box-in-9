# Final interface and evidence review

The four current modules have successful, matching source/object/log receipts: IndexSelector has eight printed audits, NumericTransition eight, CountGeometry five and StateWalk eight, for 29 total. All printed axioms are confined to propositional extensionality, classical choice and quotient soundness. This review found no unintended mathematical premise and no theorem asserting a new numerical snake bound. It did not rerun Lean.

## Selector and history update

[IndexSelector](../lean/IndexSelector.lean) proves the strict scan's range, suffix property and maximum-length property. Its generic selector theorem explicitly requires a nonempty dictionary whose entry zero is empty. These assumptions are discharged for the recorded dictionary. The eligible-slice equivalence covers the nonempty condition, suffix-length guard and final slice exactly.

[NumericTransition](../lean/NumericTransition.lean) proves the numeric update and its application to the actual direction-ID stream. `candidate_tie_unique` supplies index uniqueness from equal-length suffixes in the distinct recorded dictionary. `maximum_index_is_selector` is correctly conditional on a candidate being maximal; `no_candidates_fallback` discharges the empty-candidate case. These auxiliary hypotheses do not remain as assumptions of `numeric_history_update` or `actual_history_update`.

`builderNext` is a total Lean function, including out-of-range input indices interpreted through a fallback. Its range theorem is therefore broader than the Python loop's domain. The actual-snake application obtains valid history and direction IDs from the completed earlier interface. The history update itself is a list identity valid at arbitrary positions; valid-window bounds are required when asserting the accompanying actual direction shape or builder-loop membership.

## Count meaning and state sequence

[CountGeometry](../lean/CountGeometry.lean) proves an explicit identity between the incidence development's singleton-square count and `coreAlpha` at every valid path vertex. The positivity theorem therefore applies to the same count used by the local window code. Its only positional assumption is \(k<m+1\); it does not assume a prescribed count pattern, local certificate, internal-vertex condition or proposed upper bound. Truncation then gives values in \([1,6]\). The stronger internal upper bound and the interpretation of saturated symbol six still come from the existing local-count development.

[StateWalk](../lean/StateWalk.lean) uses these actual truncated counts. Its five-symbol code covers positions \(r+3,\ldots,r+7\), and its six-symbol code additionally covers \(r+8\). The checked split identities identify division by six with the source five-code, reduction modulo 7776 with the next five-code, and the final digit with the entering count.

`actualState` combines the actual shape, numeric history and five-count code. Its range below 1601856 is an encoding bound, not a bound on snake length. `actual_source_state`, `actual_target_state`, `consecutive_endpoints` and `encoded_actual_step` prove that the abstract endpoint formulas assemble into one consistent actual state sequence. For \(m\ge9\), that sequence has \(m-7\) states and \(m-8\) steps, including the terminal state. Small values of \(m\) are handled by the finite-index types and the explicit window bounds; no unsupported endpoint window is used.

`history_filters` establishes exactly the two shape-compatibility conditions: source history is zero or has the source shape, and selected target history is zero or has the target shape. It does not purport to discharge count-exclusion guards. No retained-edge index, credit lower bound or finite potential appears in the statement of `encoded_actual_step`.

## Python comparison and its separate scope

[builder-comparison.json](../data/builder-comparison.json) reports all 37,875 pairs in the finite Python domain: 2,363 nonempty results, 35,512 fallbacks and 791 source-compatible direction/history pairs. The pinned builder, metadata, ordered tables and output byte array match its hashes. The 37,875 output bytes also match the specified row-major layout.

The inspected [comparison script](check_builder.py) extracts the actual three assignments for `hist`, `choices` and `nq` from the builder's syntax tree and executes them. A separate Python strict scan is compared against those outputs, with uniqueness and compatibility checks. This establishes an executable comparison of those exact assignments. It is not a Lean proof of Python evaluation. Conversely, the Lean scan theorem does not depend on this Python result as an axiom. The two pieces connect the intended algorithm and the recorded implementation with explicitly different evidence types.

The comparison does not execute every count guard, reconstruct the complete edge arrays, check weights or replay a potential. Its 791 compatible pairs are direction/history combinations, not graph-edge counts.

## Remaining requirements

1. Show that every actual direction/history/six-count triple survives all reference, recovered, interval and history-conditioned exclusions. Interpret every tested count position and the saturated-symbol guards correctly.
2. Give a retained-edge index in the exact current arrays and prove that its stored direction, history, count code and endpoints equal the values now defined. Consistent endpoint formulas alone do not establish retained-edge membership.
3. Cover every compatible eleven-transition coordinate realization of each recognized three-ID signature; history recognition does not determine forgotten-coordinate returns.
4. Interpret all geometric, count-conditioned and count-independent credits on the same five actual centres. Combine alternative lower bounds by maximum, complete the pending local share premises, and connect the stored edge weight to the actual charge.
5. Check the full potential and range, then compose the walk, overlap and boundary arguments. The historical interval and conditional status of 234 are unchanged by these four modules.

## Exact reviewed evidence

| Module | Source SHA256 | Successful receipt SHA256 |
| --- | --- | --- |
| IndexSelector | `03e46386e9f94723e9c077b7d7b28b81c1436939c97fd2125ee6d672c9644b98` | `84b828ece53801010a3e7d2aa55c5a2b98c257b273d8d5fc85c1369d891de916` |
| NumericTransition | `bd881ec2c2d62501e17c662c16bef46371ad0e0be46ed00ce544f284f36e2960` | `3e998e01df7419623bad9ae69f8d9c738e9040ad19b89f9f34e6a88ba10653da` |
| CountGeometry | `ab0ecb37c727680f676394c895cd09a7f26cd7315ee5286d8893d480a7937747` | `cdae83f461e1e61d22c5f8efad45086ab8d55c38058a437cd589ead861f64991` |
| StateWalk | `f9c477e3271a37ba5735550a87da677205517e5883362403a6fd6bf46e954e56` | `48bd2a78950b5d3e2a3fd2bff026e8b487f0fdff0744368e91fdf3d2cd870363` |

The comparison receipt hash is `e3b00e5aae0f6d9067c05b6b4f88c273529b386b1a0f2d996d36bb587cb668ab`; its script hash is `4d66e6a103854a72c7ea7db3b83f94a9f3918c296ed5e436bfcfb935f863dc64`. The added count-support record, hash `ba0b0a1401b1e88881b7cd58a899f23202fdfafe606bea88876a4c74a32f5888`, matches both the positivity and count-code sources and objects. Existing inherited objects are reused; this review is not an independent rebuild of their complete dependency closure. Only this report was written.
