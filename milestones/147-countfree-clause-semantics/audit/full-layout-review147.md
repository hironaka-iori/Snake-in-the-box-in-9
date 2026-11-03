# Full replay layout review, milestone 147

Status: `PASS_BOUNDED_SOURCE_LAYOUT_AND_CHECKED_HELPER_AUDIT`.

No indexing, omitted-segment, checkpoint-composition or final-empty-clause defect was found in the generated layout. This is a source and existing-evidence review. The complete Lean contradiction remains pending.

The accompanying JSON records exact source pins and the 36 checked pilot receipts. Its SHA256 is `fee08589f9c950bdba0cd4f18f6a629a8b15825d09dcc5557c0bfdc077db10ef`.

## Checks performed

- Rehashed all 1,789 generated sources, totaling 263,586,537 bytes, against the full source plan. Both the source order and the execution order respect every project import. The 36 pilot sources are unchanged. No proof placeholders, added axioms or `native_decide` occur in the generated sources.
- Verified that segments 0 through 5088 partition all 285,541 deductions without gaps or overlaps. Their recorded reference counts sum to 31,017,505. Compared every emitted proof literal, in order, with the saved packed binary and checked every segment's ending byte offset. This comparison did not perform unit propagation.
- Verified all 1,273 checking modules, 160 group compositions and the final composition. Each segment has exactly one closed check. There are 4,929 ordinary `replay_true` transitions, 159 `cp_true` boundary transitions and one `final_false` application.
- Compared all 159 full checkpoint literals and the pilot checkpoint with their pinned compressed data, including all 32,767 entries of each list. Checked checkpoint positions against segment boundaries. The 15-bit tree-key map is injective on all 17,523 allocated slots; initial input slots follow the first 12,977 preorder keys.
- Parsed the current147 concrete CNF. Its 102 raw chunks are exactly the preserved146 compact core, including literal order and multiplicity. The previous preserved146 review supplies the separate original-clause-ID and variable-meaning audit.
- Revalidated all 36 pilot receipt hashes, source/object/log hashes, and 1,086 explicitly pinned dependency references. The 116 recorded axiom reports use only `propext`, `Classical.choice` and `Quot.sound`. These checks inspect existing successful compilations; no compiler was invoked here.

The automated read-only comparisons took 13.640 seconds. They used one source/checkpoint group at a time and did not evaluate the full proof again.

## Composition and soundness

The generated groups explicitly use `Snake9.LratFast147Replay`. Its freshly checked 15-bit `replay_true`, `cp_true` and `final_false` supply the required implications. The older narrow-format operations retained in the base helper are not selected by these groups. The base helper is used for shared clause/tree semantics and `unsat_of_raw`.

At each boundary, `cp_true` first obtains truth of the replayed tree, then requires `cpOk` to validate every non-tautological clause in the next checkpoint. Replacing dead slots with tautologies is sound. No equality between the complete replayed tree and the checkpoint tree is assumed.

Group 159 consists solely of segment 5088. Its check requires both successful replay and an empty clause at key 11657. The last packed deduction independently decodes to that key with an immediate zero literal delimiter. The source then applies `final_false` and closes the 160-group chain.

The final source statement is:

```lean
Snake9.ReplayFull147.unsat :
  Snake9.LocalWindow.Unsat Snake9.LocalWindow.ShareWindow146.cnf
```

Its temporary assumption that the CNF is true is discharged through `unsat_of_raw`; no separate unproved contradiction premise is present. The source hash is `18eba0a7ce29850b4bc8bcdf87b3a4c419947360279d99b96d5fc9033a0c9645`.

## Limits and remaining work

The existing pilot establishes the initial-tree bridge and the first 1,030 deductions with 6,004 references. It does not establish the final contradiction. Every remaining segment check, checkpoint transition, group composition and `ReplayUnsat147` must complete successfully under Lean, with matching source/object/dependency pins and acceptable axiom reports.

This review did not reread the original 233 MB LRAT, recompute last-use allocation, reconstruct live checkpoint databases or repeat RUP propagation. Those transport claims retain their pinned complete Python replay evidence; the pending closed Lean checks provide the decisive logical checks. No Lean, solver or graph job was launched.

The final statement concerns the Boolean CNF. Actual-snake normalization, the forward/reverse share consequence and any graph-derived upper bound require their separate assemblies.

One documentation issue remains: `replay/README.md` still describes full generation as deferred and the pilot as unchecked. The full source plan and pilot completion receipt supersede those historical status paragraphs. No existing file was changed by this review.
