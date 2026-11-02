# Context assignment certificate plan

## Recommended certificate

The remaining context assignment can be handled by **one finite certificate independent of the count code**, preceded by a short generic projection from `numericKeep`. No evaluation of the 46,656 count codes is needed for this step.

An independent comparison of all **37,875** bounded direction/history positions found that the source condition

\[
q=0\quad\text{or}\quad
\operatorname{recordedCompatible}(q)=\operatorname{sourceId}(d)
\]

selects exactly the **791** contexts in the saved milestone 87 diagram payload. This matches the context/class maps in milestones 88, 89 and 90. The source IDs and recorded compatibility list were compared directly with the milestone 77 Lean literals, in addition to the generating metadata. No count predicates, raw graph arrays or solvers were evaluated.

Therefore the assignment proof can project the source condition from `rangeCompatibilityKeep` and discard its target condition as an unnecessary conjunct for this particular implication. This does not change `numericKeep` or assert that a source-only predicate equals the full predicate.

A compact deterministic class selector needs **505 history-zero default classes and exactly three overrides**:

| Direction | History | Default class | Assigned class | Base witness job | History head |
| --- | --- | --- | --- | --- | --- |
| 177 | 43 | 84 | 85 | 178 | 0 |
| 177 | 70 | 84 | 85 | 178 | 1 |
| 180 | 68 | 88 | 89 | 182 | 2 |

Apply overrides before the default. The selector matches all 791 saved class assignments. Its full default vector, overrides, per-class pair lists and root table are recorded in the JSON plan. There are 132 source-shape groups containing 206 history indices in total, counting history zero once in each group; this is an available compact representation of the finite domain, not an additional required proof route.

## Authoritative fields

- `87-retained-array-membership/data/coverage-membership-dag.json.gz`: `blocks` contains `[75*direction+history, class_id]`; `roots[class_id]` is the corresponding diagram root. These are the saved accepted-set assignments.
- `88-retention-diagram-certificate/data/box-cover-selected-max-gain.json.gz`: block fields are `[block_id, base_direction, dag_set, history_modification_indices, next_history]`. `dag_set` is the class ID, not a diagram node ID.
- `89-shared-cover-certification/data/context-witnesses.json.gz`: `classes` gives ordered box geometry IDs; `contexts` gives `[block_id, class_id, original_witness_list_id]`.
- `90-context-witness-certificates/data/witness-batch-plan.json`: each context binds the original pair/class/list to its base job and optional history head, preserving the original positions.
- The root's proposed milestone 92 `contextKeys` lists use **(direction, history)**. Their class ordering must agree with the saved class IDs and each corresponding original `rootNNN`.

The stored diagram roots agree with the 127 root values recorded by the earlier shared-cover source review. Exact Lean literal identification with the selected root remains part of the assembly interface; a Python hash comparison is not a replacement for that identification.

## Three proof obligations

1. **Generic source projection.** With `d < 505` and `numericKeep q d code = true`, prove `q < 75`, `code < 46656`, and the source condition above. Unfold `numericKeep` and `wordKeep`, project `rangeCompatibilityKeep`, rewrite the decoded index using `direction_index_getD`, and take the relevant conjunctions. This new projection lemma has not been compiled in this task.

2. **Finite class assignment.** For every `d < 505` and `q < 75` satisfying the source condition, let `c` be the compact selector. Certify simultaneously that `c < 127`, `(d,q)` belongs to the published `contextKeys c`, and the saved block lookup at `75*d+q` returns `some c`. A bounded Boolean check can filter the 37,875 positions by source compatibility and check only the 791 selected membership bodies. Existing `recorded_maps_exact` permits a numeric source-ID table to replace expensive source-shape reconstruction. No `builderNext` evaluation is needed for this coverage implication.

3. **Generic class assembly.** Apply the theorem for the selected class using the membership proof, projected range bounds and the original `numericKeep` hypothesis. Identify that theorem's original root with `roots[c]`. The resulting statement should retain the saved-class lookup equation alongside diagram acceptance, so subsequent saved-array assembly cannot accidentally use an unrelated accepting root.

The finite class assignment should include saved-class coherence directly. Membership in the union of 127 context lists, without identifying the chosen list with the saved class/root, is insufficient for the next array step. The 505-plus-three representation is a compact sufficient representation found here; no claim of globally minimum encoding size is made.

## Existing checked interfaces

`Snake9.Direction77.direction_index_getD`, in milestone 77 `lean/LookupTableCheck.lean`, proves

\[
i<505\;\Longrightarrow\;
\operatorname{extensions.idxOf}(\operatorname{extensions.getD}(i,[]))=i.
\]

Its companion `recorded_maps_exact` identifies the stored source and target IDs with `sourceId` and `targetId` on the same bounded domain. Both are already checked and available for reuse. The source/object/log receipt hashes were verified in this review.

Milestone 78 additionally provides `builderNext_lt`, `selectIndex_eq_history`, `numeric_history_update` and `actual_history_update`. Milestone 77 `compatible_after_append` identifies the target shape of a nonempty resulting history, and `recorded_compatible_exact` connects the stored compatibility field to that shape. These explain the target/history interface, but the recommended source-only assignment certificate does not need a new transition-table proof.

`RetainedEnumeration.RetentionCover` already requires explicit bounds on direction, history and code. `ArrayAssembly.actual_saved_edge` obtains these bounds from the actual snake and separately assumes both reference-refutation catalogues and finite retention coverage. Keeping `d < 505` in the new assignment interface therefore fits the existing assembly.

## Default and scope pitfalls

- `numericKeep` decodes its supplied direction through `extensions.getD` and checks the resulting `idxOf`. Its definition does not directly test the original direction argument. Preserve `d < 505` when using `direction_index_getD`. Removing that hypothesis would require an additional proof excluding the out-of-range default word `[]`; it is unnecessary for the current bounded retention interface.
- Keep `q < 75` before reading compatibility data or interpreting a block index. An unchecked default compatibility value of zero can spuriously match source shape zero. History zero is an intentional exception and must remain admitted even when its placeholder compatibility value differs from the source shape.
- Class zero is valid. Missing context lookup should use `Option`, or have an explicit presence proof, rather than silently treating a missing value as class zero.
- Keep direction/history pair order, the factor 75 in the block ID, and the distinction between class IDs, root node IDs, witness list IDs and base job IDs.
- Do not omit the three history overrides: classes 85 and 89 require their separately checked history heads.
- Completed geometric and witness checks plus this assignment certificate establish acceptance by the appropriate diagram. They do not yet prove that every accepted code occurs in the exact saved full-key row array. That finite diagram-to-row bridge, and the endpoint-column identities, remain necessary for milestone 87 `RetentionCover`/`actual_saved_edge`. The earlier computational DAG roundtrip alone is not a Lean proof of that connection.
- Actual-snake transport still carries the explicit `h235` and `h236` reference-catalogue premises. No unconditional global bound follows from this planning result.

## Evidence and limits

This task read source statements and existing receipts, compared the saved mappings, and wrote only these planning notes. It ran no compiler, generator, solver, count-code enumeration or source-array replay. The proposed three obligations are a plan, not newly checked theorems. Milestone 92's forthcoming per-class context lists were not assumed completed.

- Snapshot: `2026-11-02T14:03:56.529437+00:00`.
- Plan SHA-256: `832d2c1761c16281425b3a6a86842de5e2b41d3f1626751eea6460b99f27aab7`.
- Existing `LookupTableCheck` receipt: `cf301d632638f44d8ce772024ad9d419c9b000fa5693a2aa094f9e37c66dc3eb`.
- Existing `NumericRetention` receipt: `364985551bcfdec435cd08bb258c7bfb705074b996d5384a597da7e6d468e4df`.
- Existing `NumericTransition` receipt: `3e998e01df7419623bad9ae69f8d9c738e9040ad19b89f9f34e6a88ba10653da`.
- The JSON plan contains all input/source/object/log pins, exact per-class contexts, roots, compact assignment data and the proposed statement scopes.
