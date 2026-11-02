# Independent plain-count review

The key `012340 / [5,5,2,4,5]` and its reversed-count counterpart are absent from the saved reference catalogues. The existing reference, short-rule and interval filters do not reject the full graph key `(352,16,29434)`. A checked refutation of this five-count window would therefore provide an additional exclusion that removes the indicated edge of the completed mean 483 cycle.

This review inspected sources and performed small scalar comparisons only. No Lean compiler, SAT solver or graph-wide enumeration was run. The new refutation was still being prepared by the parent during this inspection.

## Current probe and its precise claim

`data/plain-probes/edge3534483-plain.json` records directions `[0,1,2,3,4,0]`, counts `[5,5,2,4,5]`, no share cap, no cycle cuts, 3484 variables and 59251 clauses. Its status is `UNSAT_UNCERTIFIED`. All seven plain-probe JSON records have that same status. These are solver observations; their proof and semantic checking are separate obligations.

The intended theorem is

```lean
Refuted (winOf [0,1,2,3,4,0]) (boundsOf [5,5,2,4,5])
```

`LocalWindowDirModel.lean:27–29` maps a symbol below 6 to its singleton interval and symbol 6 to $[6,21]$. Thus the bounds here are exactly

$$[(5,5),(5,5),(2,2),(4,4),(5,5)].$$

This does not exclude all tuples bounded above by $(5,5,2,4,5)$. A stronger upper-bound-only claim would need its own checked semantics. `LocalWindowModel.lean:102` defines `Refuted` as impossibility for every assignment satisfying the local axioms for the specified window and centre bounds. A plain-count theorem must be obtained at that type, rather than a share-cap refutation.

## Comparison with existing exclusions

Canonical reversal fixes the shape `012340`, while reversing the tuple gives `[5,4,2,5,5]`. Both direction/count pairs were checked.

| Inspected source | Number of keys or rules | Result for this full edge |
| --- | ---: | --- |
|85 `data/reference-union.json`|1378|Neither full tuple occurs; no eligible reference subwindow matches|
|85 `upstream/LocalWindowDirKeys6K235.lean`|1287|Neither tuple occurs; 127 entries have the same shape|
|85 `upstream/LocalWindowDirKeysR4.lean`|732|Neither tuple occurs; 67 entries have the same shape|
|107 `upstream/work/final_lean/LocalWindowDirKeys.lean`|145|No eligible matching subwindow|
|107 `upstream/work/final_lean/LocalWindowDirKeys5.lean`|175|No eligible matching subwindow|
|81 `lean/CapCatalogue.lean` and `SumCatalogue.lean`|37 cap rules and 3 sum rules|No hit at any fitting offset in either orientation|
|79 `lean/IntervalCatalogue.lean`|10 interval rules|No hit at any of the three fitting offsets in either orientation|

For the 1378-key union, the same subwindow comparison was also performed on the six-direction target in isolation. It has no hit. The comparison is exact because every count under consideration is below 6; no threshold ambiguity is involved.

Some checked rules have the same shape without covering these counts. For example, milestone 81's four `012340` cap rules require small pairs at positions $(1,2)$, $(1,5)$ or $(4,5)$. The sum rule `safe501` excludes a sum of at most 12 at positions $(1,4,5)$. The target gives 14 in the forward orientation and 15 in the reversed orientation. Consequently that sum rule does not imply this exclusion.

The individually recovered reference entries in milestones 107–109 are drawn from the union already checked above. The broader relaxed rules of 108 and 109 also do not cover this edge: the 108 rule requires two distinct counts at most 2, whereas this six-count code has only one such count; the 109 rule requires a count at most 1, whereas all six counts are at least 2.

These checks establish noncoverage by the specified catalogues and retained filters. They do not prove that no other argument elsewhere in the repository could imply the result. The older catalogue lists are evidence of their exact content; this review does not upgrade their previously explicit collective refutation premises to completed proofs.

## Actual-snake transfer

The existing checked generic theorem is `Snake9.Reference85.refuted_key_retained`, in `85-reference-catalogue-union/lean/ReferenceInterface.lean:51`. Given a key $k$, $r+9\leq m$, $s+|k_2|\leq6$, `keyValid k = true`, and the individual `Refuted` theorem for $k$, it excludes both `forwardHit p r s k` and `reverseHit p r s k`. It requires neither global reference-catalogue premise and does not require membership in the existing union.

For the new key, `keyValid` reduces to the five-symbol length, six-direction length and symbol bounds. The count width is 5, so the two eligible offsets are $s=0,1$. At each offset, the shape uses

$$\operatorname{canon}\bigl(D[s+2:s+8]\bigr),$$

and the five counts come from positions $s,\ldots,s+4$ of the six-symbol code. In an actual snake these are centres $r+s+3,\ldots,r+s+7$.

The underlying source statements are `encoded_forward_exclusion` and `encoded_reverse_exclusion` in `79-retained-edge-guards/lean/ReferenceRetention.lean:37,50`. They decode the base-six slice, identify the actual canonical subwindow, and use `canonical_symbol_exclusion` or `reversed_symbol_exclusion` from `CanonicalExclusions.lean:66,83`. The reversed theorem reverses both the direction slice and its counts. There is no assumption that a graph cycle can be realized as a snake.

## Exact full-edge hit

For edge 3534483 the complete saved key and data are

$$d=352,\qquad q=16,\qquad c=29434,$$

$$D=(0,1,2,3,4,2,1,5,3),\qquad
(a_0,\ldots,a_5)=(4,5,5,2,4,5).$$

At $s=1$, canonicalizing $D[3:9]=(3,4,2,1,5,3)$ gives `012340`, and

$$29434\bmod6^5=6106
=\operatorname{encodeCounts}([5,5,2,4,5],0).$$

Thus `referenceForwardB D 29434 1 k = true` for the new key, using the existing executable definition in `87-retained-array-membership/lean/NumericRetention.lean:11`. The matching actual share-independent window starts at $r+3$ and has centres $r+4,\ldots,r+8$.

The reverse count encoding is 5896. Although the reversed direction shape is also `012340`, the reverse hit requires that distinct encoding. For this edge, the new key matches only the forward orientation at offset 1. Both orientations at offset 0 and the reverse orientation at offset 1 fail.

The existing retained diagram accepts this full key. A direct scalar evaluation of the source literals gives class 124 and node trace

$$3970\to3963\to2205\to1140\to127\to10\to1.$$

The literals came from `88-retention-diagram-certificate/lean/GraphData.lean`, `92-full-witness-batch/lean/BatchContextData.lean`, and `92-full-witness-batch/lean/ContextAssignmentData.lean`; the direction word came from `77-direction-state-coverage/lean/DirectionTables.lean`. This independently confirms that the intended new filter changes the existing accepted graph at this key. It is a Python scalar check, not a new Lean theorem.

After the individual refutation is checked, a strengthened graph can exclude this key and any other full key meeting the same two orientation tests at either eligible offset. The filter need not restrict history: the count-window theorem is independent of $q$. Existing actual-walk theorems preserve the complete direction/history/count key and common edge index, including `ActualGraphKeys98.defined_actual_edge_key`; the exact-union variant is supplied by milestone 105. A new filtered-graph assembly must retain those keys and source/target identities. Merely deleting an endpoint pair is insufficient when parallel edges have different keys.

Removing this edge breaks the displayed completed mean 483 cycle. It does not establish a larger minimum mean, a smaller potential range, or a new snake bound. The revised graph and potential certificate still require evaluation and proof. The original 1378-key reference-union obligation is also unchanged merely by proving a key outside that union.

## Source verification and pins

The inherited `ReferenceRetention-audit.json` and `ReferenceInterface-audit.json` both report `PASS_LEAN_MODULE`; their recorded source hashes match the source bytes inspected in this review. No existing proof was recompiled.

| Artifact | SHA256 |
| --- | --- |
|110 `data/plain-probes/edge3534483-plain.json`|`6df98fb4c17e69cc7a2197e17891209236acd4a7916924f07765d3809bf1fc15`|
|85 `data/reference-union.json`|`dea948631bbccd4c81a1b590dfeeb7f606bd44fc664861f7667b6d041e267289`|
|79 `lean/ReferenceRetention.lean`|`41d620dbcea53c346adda0423c3b919a4ae4feb449d5a5219a57c4d5eaabcb50`|
|85 `lean/ReferenceInterface.lean`|`8fd1fbdf232457a880186d921a56e77a7b914c28f950400e9a512a86f5399599`|

The new theorem and fresh LRAT replay are outside this review's checked evidence. Their successful completion must be established by their own receipts.
