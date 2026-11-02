# Next bridge from diagram acceptance to retained rows

Bounded source and saved-data review, 2026-11-02. No Lean, solver, generator, or array reconstruction was run for this review. Only this report was written. Statements below labelled proposed have not been checked in Lean.

## Recommendation

Prove one-sided diagram-to-saved-block membership, then compose it with milestone 92's context assignment and milestone 87's `covering_row_index`. Equality with `generatedRows retainedKeep` is unnecessary. The remaining substantive data obligation is that each of the 127 saved diagram roots accepts only codes present in its corresponding saved ordered code list, and that the 791 block bindings reconstruct the saved full-key row array in order.

At inspection, `ContextAssignmentChecks.numeric_context_membership` is the existing generic bridge. It still takes `ClassMembershipFamily g` as an explicit premise. The proposed completed name `retained_numeric_diagram` was not present in the inspected milestone 92 Lean sources. This review does not infer completion of the 127-class batch from generated files.

## Existing interfaces and exact missing link

`92/lean/ContextAssignment.lean` defines `Assigned di q` with all four facts: the chosen class is below 127; `(di,q)` belongs to that class's recorded context keys; `savedBlockClass (75*di+q)` equals that class; and `savedRootForBlock (75*di+q)` equals the recorded class root. Missing blocks use `Option.none`, so class zero is not a missing-block sentinel. `numeric_keep_source` retains `di < 505`, derives `q < 75` and `code < 46656`, and projects the source-compatibility conjunct from the original numeric predicate.

`87/lean/RetainedEnumeration.lean:27` requires only:

```lean
RetentionCover keep rows :=
  ∀ d q c, d < 505 → q < 75 → c < 46656 →
    keep d q c = true → (d,q,c) ∈ rows
```

`87/lean/ArrayAssembly.lean:11` sets `retainedKeep d q c := numericKeep q d c`. Preserve this argument reversal when composing the interfaces.

The shortest useful generic statement is the following proposed signature, with names resolved by the indicated imports:

```lean
theorem retention_cover_of_diagram
    (rows : List Row)
    (hdiagram : ∀ di q c, di < 505 → numericKeep q di c = true →
      Assigned di q ∧
      diagramEval retainedDiagram
        (recordedClassRoot (chosenClass di q)) (digits c) = true)
    (hrows : ∀ di q c, di < 505 → q < 75 → c < 46656 →
      Assigned di q →
      diagramEval retainedDiagram
        (recordedClassRoot (chosenClass di q)) (digits c) = true →
      (di,q,c) ∈ rows) :
    RetentionCover retainedKeep rows
```

Its proof is direct composition. It separates the pending class family from the saved-array interpretation and requires no additional geometric exclusions. Dependencies are milestone 92's completed class assembly/context assignment, milestone 88's original `CoverTree`/`GraphData`/`DigitReconstruction`, and milestone 87's `RetainedEnumeration`/`ArrayAssembly`.

## Concrete decomposition of the saved-data obligation

Use 127 ordered code lists, shared by class, and the existing 791 ascending `(block,class)` pairs. Export the code lists independently from the authoritative NPZ count-code slices, preserving their ascending order; do not label a list defined solely by filtering diagram acceptance as an independently saved code list.

The following proposed pieces are sufficient:

1. `class_diagram_to_codes`: for `cls < 127` and `c < 46656`, acceptance at `savedRoots[cls]` implies `c ∈ savedCodes[cls]`. The stronger equivalence is useful for certifying the exact representation, but one direction suffices for coverage. Avoid repeated linear `List.mem` over thousands of entries in a full finite check: a generic radix-six enumerator or bounded bit-mask lookup with a membership theorem can certify this interface. There are 127 masks and 5,925,312 class/code combinations, rather than 36,904,896 compatible context/code combinations.
2. `saved_block_rows`: define each block's rows as `savedCodes[cls].map (fun c => (block/75, block%75, c))`. Prove a matching `savedBlockClass block = some cls` places that block's list in the flattened row representation. A generic `find?` membership lemma handles the current definition. Recover `(di,q)` from `block = 75*di+q` using `q < 75`.
3. `saved_rows_exact`: identify the imported saved row array with the flattening of these 791 block lists. This is an identity of the complete ordered full keys, not only a cardinality or endpoint-set comparison. If the Lean row array is defined by this compressed representation, this equation can be definitional; its agreement with the external NPZ bytes remains a separately stated import/provenance check. To claim kernel-checked equality with separately imported NPZ row literals, those literals and their equality certificate must also be supplied.

A generic `diagramCodes g root := (List.range 46656).filter (fun c => diagramEval g root (digits c))` provides acceptance-to-membership immediately. Defining rows from that list yields a short checked coverage theorem about the diagram-defined rows. It does not by itself discharge `saved_rows_exact` for the external saved array. The existing Python roundtrip is valuable evidence for that import step, and is not a Lean theorem.

For the practical certificate, prefer a depth-recursive suffix enumerator over 127 exhaustive acceptance tables. With zero remaining digits, emit `[0]` exactly when the node is terminal 1. With `k+1` remaining digits, concatenate, in order `j = 0,...,5`, the suffix list for `nextNode g node (j+1)` at depth `k`, mapping each suffix `x` to `j*6^k+x`. Terminal 0 can immediately emit `[]`; terminal 1 can immediately emit `List.range (6^depth)`. These shortcuts require their own generic equality to the recurrence. Recursion decreases depth, so a finite evaluator-equivalence theorem does not require acyclicity or trusting the depth field stored in the graph rows.

Define a width-dependent most-significant-first digit decoder. Prove by induction on remaining depth that membership in the recursive suffix list is equivalent to `c < 6^depth` together with acceptance on that decoder's digit list. At depth six, identify this decoder with existing `digits c`. Then certify, separately for each of the 127 class roots, that the independently exported saved ordered code list equals the recursively expanded list. Ordered six-way concatenation also permits generic range, ascending-order and duplicate-freedom lemmas if a later exact rank theorem needs them. Shared subdiagram expansions can be named for reuse, with correspondence checked, rather than expanding the same suffix repeatedly.

The child argument to `nextNode` must be `j+1`; table position zero contains depth metadata and is not a child. This proposed induction-and-list-equality route avoids requiring a kernel Boolean test for every class/code pair. Its actual compilation cost has not been measured. The 791 block binding and saved-array identity obligations remain separate, including when the recursive lists are generated successfully.

No new proof that numeric retention exactly equals saved retention is needed. One-sided coverage permits extra rows; exact equality is only needed when asserting identity with the existing saved artifact, its ordering, or a previously verified weighted graph.

## Existing indexing and endpoint assembly

After coverage, use `covering_row_index` at `87/lean/RetainedEnumeration.lean:46` to obtain an index satisfying `rows.toList[i]? = some (di,q,c)`. This requires neither a rank calculation nor `Nodup`.

For a specific reproducible index, the existing `prefix_rank_index` and `flattened_block_index` at lines 69 and 77 give prefix length plus the full key's `idxOf` inside its block. Injectivity of `c ↦ (di,q,c)` then identifies this with the accepted-code rank. The saved index is

\[
 i=\sum_{b<75d+q}\lvert C_b\rvert+\operatorname{rank}_{C_{75d+q}}(c),
\]

where the rank counts accepted codes strictly below \(c\). Membership uses zero-based indices. `full_key_index_unique` at line 85 additionally needs `rows.Nodup`; it is optional for constructing a walk.

`actual_saved_edge` and `actual_saved_walk` in `87/lean/ArrayAssembly.lean` already consume `RetentionCover`, together with separate equations `U.toList = rows.toList.map rowSource` and `V.toList = rows.toList.map rowTarget`. They retain `AllRefuted6K235` and `AllRefuted236` as explicit actual-snake premises. This row bridge does not close those reference-catalogue premises, prove a weight column or potential inequality, or improve a numerical bound.

## Data evidence and pitfalls

The authoritative payload is `87/data/coverage-membership-dag.json.gz`: 3,981 nonterminal rows, 127 roots and 791 block/class pairs. The source is `72-four-count-proof-closure/critical-current/build/source-graph.npz`. The saved `coverage-profile.json` reports exact expansion of every root, comparison of every block slice, and a second integer-digit decoder over all 5,925,312 class/code combinations. This review read the source and receipts; it did not repeat those computations.

The source-derived array audit reports 4,947,008 rows in strict `(direction,history,count_code)` order, no repeated full key, 791 nonempty compatible blocks and 37,084 empty incompatible blocks. It separately reports 206,589 repeated endpoint pairs, each of multiplicity two. Deduplicating `(U,V)`, using endpoint equality as row equality, or selecting a weight by endpoint pair alone loses the full-key distinction.

Other boundaries to preserve:

- Lean digits are symbols 1 through 6, most significant first; Python's intermediate radix digits are 0 through 5. A diagram row's column zero stores depth; children occupy columns 1 through 6.
- Terminal 1 accepts every remaining suffix. An enumerator must emit all remaining radix-six suffixes, including when terminal 1 appears before depth zero. Terminal 0 emits none.
- `diagramEval` ignores stored depth and uses total default lookups. A new decoder must agree with these exact semantics, or separately prove bounded well-formedness of the supplied graph. The original DAG is layered, but this property cannot be silently substituted for the existing evaluator.
- `digits` forgets higher digits. Keep `c < 46656`; `digit_reconstruction` uses this bound to recover the original code. Keep `di < 505` for `direction_index_getD`; an out-of-range `getD` default is not a valid decoded direction index.
- Preserve the three history-specific classes: `(177,43)` and `(177,70)` use 85 rather than 84; `(180,68)` uses 89 rather than 88. The existing `Assigned` equations already express the correct saved bindings.
- A compressed rows definition gives a valid mathematical object. Hash agreement and Python export validation establish its relation to external files at an explicit data-import boundary; they must not be described as kernel-checked binary-file parsing.

## Reviewed byte pins

Paths below are relative to `E:/Snake-in-a-box/milestones/`. SHA-256 values were read or recomputed in this bounded review; the NPZ value is from the saved array receipt.

| Artifact | SHA-256 |
|---|---|
| `87-retained-array-membership/lean/RetainedEnumeration.lean` | `de5dc56da9c55f864bcdf692be80ded05199f380b2acd9bda00135ed79cb828e` |
| `87-retained-array-membership/lean/NumericRetention.lean` | `85c8537aedce983be597c7758eb2a2577d126c3328f434f4edc1cb4cb9faa84b` |
| `87-retained-array-membership/lean/ArrayAssembly.lean` | `4ec3ab0d6a0950d77b391acdfb790a8f31b485e4eed8a4bb0aa4e44bfb6fd066` |
| `88-retention-diagram-certificate/lean/CoverTree.lean` | `a965f33fb9cbfa4cde96f4dd4f121ecf356f3e055fbd3cb6d314fd732b18c779` |
| `88-retention-diagram-certificate/lean/DigitReconstruction.lean` | `a8cdbc84ba3a1ac36948a7be279175c64e0f0c7ec54b3de76bd7872072a38410` |
| `88-retention-diagram-certificate/lean/GraphData.lean` | `114c7f9684fbd7fb1e8562fbc73428c79ab5c1c567cd10f7844a536188b9c7b0` |
| `92-full-witness-batch/lean/ContextAssignment.lean` | `059e6cf2bc2167920ec59157c2d7fb261fb30a5134cfae224f9e4993c05ca157` |
| `92-full-witness-batch/lean/ContextAssignmentChecks.lean` | `5b5087357189f5d6f6cdc456187ee4493418b152ee00a494189e8375586d2a2f` |
| `92-full-witness-batch/lean/ContextAssignmentData.lean` | `8fc0a4979dd8d8a1e819d93ba88778b0ff8a8724862afb642a4ef0728c6e7019` |
| `87-retained-array-membership/data/coverage-membership-dag.json.gz` | `5ded4dbe27d3ba795e57e241289facce6444789e30edb9531a312fab58818823` |
| `87-retained-array-membership/data/coverage-profile.json` | `fce631ddf8176d293f3eadeafa56ef1eb966d12cd4b0c4aab343b3b6117d3566` |
| `87-retained-array-membership/data/array-order-audit.json` | `e3096ad1e30227d992ab5c4fd926a114208455a1eb71b1c353c1ea05bb8c4cdf` |
| `72-four-count-proof-closure/critical-current/build/source-graph.npz` | `b40f1ca44ad8f3269f890efe8decc60f19dabd647f11255c05df3727341c2c34` |

The DAG pins the source arrays individually: direction `e0e598fa564c6474be6ef98215886248bfca188f3eb47c59b2d9e96ea20b8705`, history `23eb7524f277153fc0ca23ce4cdf005e28c8091f7993b44bfa34812a5adb57d7`, and count code `1917e3700ccdee418c22f29829b309775f9212f026e55e394038c1ddfa25210e`.

Verdict: the route is a precise finite representation bridge with reusable generic indexing lemmas. No completed saved-row Lean certificate or numerical improvement is asserted by this review.
