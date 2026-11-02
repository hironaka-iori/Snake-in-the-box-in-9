# Exact-union reference interface

Current status: the parent compiled the source successfully and audited all five printed theorems. The receipt is `data/ReferenceAssembly105-audit.json`. The source review itself ran no compiler or refutation jobs. The reference union remains an explicit assumption.

## Boundary identified

The actual numeric predicate reads precisely `Snake9.Reference85.referenceKeys`, the 1378-key union. The older route obtains each key's refutation from `AllRefuted6K235` or `AllRefuted236` and then applies `Reference85.refuted_key_retained`. That last theorem already accepts an individual key refutation directly.

Consequently, the exact proposition `AllRefutedList referenceKeys` is sufficient for the actual reference filters. `AllRefutedList.mem` extracts the individual refutation, while the existing `referenceKeys_valid` theorem supplies the symbol and length conditions. Both orientations and every fitting placement remain included.

The file named `ReferenceRetention.lean` is in milestone79; milestone85 imports it through `ReferenceInterface.lean`. The inspected source path was `milestones/79-retained-edge-guards/lean/ReferenceRetention.lean`.

## Minimal theorem chain

The new namespace `Snake9.ReferenceAssembly105` contains five theorems and no definitions or axioms:

1. `actual_reference_filters` derives the unchanged reference-filter proposition from the exact union premise.
2. `actual_numeric_keep` combines those filters with the existing range and history-compatibility facts and all three nonreference filter families. It concludes the original executable `numericKeep` equation.
3. `actual_potential_bound` retains the original row-potential premise and bound on the potential. It replaces only the two old catalogue premises by the exact union premise.
4. `completed235` takes the exact union premise, potential range 551 and the complete graph check for slope 483 and the completed floor. Its conclusion is $m\leq235$.
5. `conditional234` retains all five local share-refutation premises, the exact union premise, potential range 602 and the complete graph check for slope 496 and the conditional floor. Its conclusion is $m\leq234$.

Both upper-bound statements are conditional on their explicit hypotheses. The word “completed” identifies the existing completed floor profile; it does not assert that the reference union or complete graph check has been discharged by this source.

## Full-key coverage and unchanged charge argument

The potential proof applies `defined_graph_covers` with the existing `retained_class_family` and `assignment_checked`. Its retained row is exactly

$$
(\mathrm{directionId}(p,r),\mathrm{actualHistory}(p,r),\mathrm{sixCode}(p,r)).
$$

It then applies the supplied potential inequality to that row, rewrites the same row's source and target using the existing actual-state identities, and invokes the original telescoping theorem. This bypasses the older wrappers that hard-code the two catalogue hypotheses. It does not identify edges solely by endpoint pairs, alter the graph rows, or assume equality with an external numeric array.

The completed and conditional bounds reuse the original total-weight budget. The conditional local caps remain 15, 17, 15, 15, 15 for cases 7301, 7302, 7303, 7307, 7308 respectively. The credited centres, count-symbol semantics, share scale, maxima of alternative credits, boundary charge and potential constants are unchanged.

`graphCheck_sound` supplies the unchanged row-potential premise from the complete graph check in the two final statements. No partial-context certificate substitutes for that complete check.

## Verification and remaining obligation

The source imports `PotentialChecker99` and reuses its established import closure, including the reference interface, numeric retention, complete class coverage, assignment certificate, weight and charge modules. Five axiom-print commands cover the new chain.

All five reports contain only `propext`, `Classical.choice` and `Quot.sound`. No new mathematical premise beyond the explicit union refutation and the unchanged profile/check premises was identified. This source neither proves the union refuted nor derives either larger catalogue proposition from it. Concrete union-refutation certificates remain a separate task.
