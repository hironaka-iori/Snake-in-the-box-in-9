# Review of the count-excess route

The repository already contains this method: a necessary local count inequality can force excess above the clipped value six, and an overlap bound converts that excess into additional charge. The present saturated completed-profile cycle is a plausible place to test those existing interfaces. No new local exclusion or improved graph bound is established by this review.

This was a bounded source and saved-evidence inspection. No solver, Lean compiler, graph modification or potential search was run. Only this report was written.

## Existing results and exact interfaces

Write $b_i=\min(6,\alpha_i)$ and $e_i=\alpha_i-b_i$, using the clipping and excess already defined in the project. The identity $b_i+e_i=\alpha_i$ is the central accounting fact.

| Existing source | Reusable statement | Relevant limitation |
| --- | --- | --- |
|31 `lean/WeightedExcess.lean:13`, `Snake9.JointExcess.weighted_overlap`|If each demand is bounded by the excess on its support, and each position belongs to at most $K$ supports, total demand is at most $K\sum_i e_i$.|Both the local lower bound and support multiplicity are explicit premises.|
|41 `lean/JointExcess.lean:12`, `JointInterveningAccounting.shifted_sum_le`|A fixed shifted sum over a finite occurrence set is bounded by the whole-path excess sum.|The shifted positions must lie inside the whole-path range.|
|41 `lean/JointExcess.lean:27,40`, `occurrence_excess`, `charge_bonus`|Two fixed positions give overlap at most two; this converts occurrence count into additional charge.|The concrete occurrence lemma uses offsets 3 and 6, so it needs reindexing or the underlying generic shifted lemma for the current offsets.|
|50 `lean/TripleDemand.lean:11,23`|`decomposition` gives clipped count plus excess equals the original count; `clipped_exact` identifies every count whose symbol is below 6.|These arithmetic facts supply no new local geometric restriction.|
|50 `lean/TripleDemand.lean:16,43`|A checked three-count lower bound gives a joint excess demand; `snake_demand` transfers it to the specified snake shape.|For the present tuple, the old lower bound 13 on positions 1, 4, 5 gives zero demand because the clipped sum is 17.|
|42 `lean/CommonBudget.lean`, `seven_window_budget`, `maximum_demand`|Bounds common-window demand and combines alternatives by maximum.|The seven-position multiplicity belongs to that old window layout.|
|51 `lean/JointChargeBudget.lean:7,14,21` and `WindowShareBudget.lean`|Combine separately justified excess and share charges, retaining overlap factors; alternative bounds on the same resource combine by maximum.|The old coefficients 168/336 and the seven-centre layout cannot be copied directly into the current graph.|
|73 `bridge/lean/FiveCentreOverlap.lean:15`, `CountFreeBridge.shifted_prefix_sum_le`|For a nonnegative function, $\sum_{r<n}f(r+a)\leq\sum_{i<N}f(i)$ when $a+n\leq N$.|This is already in the current charge environment and is sufficient for the proposed two-position calculation.|
|98 `lean/GlobalCharge98.lean:21`, `discarded_counts`|A generic boundary argument gives a loss of at least 21 under endpoint, positivity and adjacent-pair hypotheses.|It must be instantiated on clipped counts for the proposed strengthened budget.|

The saved logs for 31's `weighted_overlap` and 41's shifted/occurrence/charge lemmas contain only standard axioms. Milestones 50 and 51 have successful verification records listing the cited arithmetic and budget theorems; their recorded source hashes match the inspected files. `GlobalCharge98-audit.json` records six successful standard-axiom checks and its source hash also matches. No historical object closure was rebuilt here.

The existing experiment `51/scripts/pressure.py` explicitly collects positions with symbol 6 and tests an upper bound on the sum of their true counts. It converts an UNSAT excess cap $d$ into demand $d+1$, and takes a maximum when several demands charge the same common window. Thus the proposed mechanism is already part of the project. A narrow comparison of 425 saved query records under milestone 51's six passes found no exact match to `012340 / [6,3,2,5,6]`, including simultaneous reversal. This is a bounded search, not a claim of novelty.

## What an exact-six exclusion would establish

For the shape `012340`, consider the explicit interval theorem

```lean
Refuted (winOf [0,1,2,3,4,0])
  [(6,6),(3,3),(2,2),(5,5),(6,6)]
```

The singleton bounds on the two sixes are essential. `boundsOf [6,3,2,5,6]` instead means $[6,21]$ at both outer centres; refuting that stronger local model would justify deleting the entire lumped window. Refuting only the displayed exact-six case would justify excess demand.

Assume the displayed theorem has been checked and the actual window has clipped counts $(6,3,2,5,6)$. Its middle three counts are exact, while its first and fifth counts are at least 6. If both outer excesses were zero, both true counts would equal 6, contradicting the theorem. Hence

$$1\leq e_{t+1}+e_{t+5}.$$

The same conclusion holds for the reversed occurrence: the direction shape remains `012340`, the count tuple reverses, and the two potentially nonzero excess positions remain the two outer centres. `Guards79.canonical_interval_exclusion` provides the actual-snake transfer for the explicit bounds. The arithmetic conclusion then uses the existing clipped-count facts; a separate new framework is unnecessary.

The proposed relaxation of the already checked 110 proof to bounds $[(0,5),(0,5),(2,2),(0,4),(0,5)]$ does not establish this exact-six theorem. The tuple $(6,3,2,5,6)$ lies outside those bounds. Its excess claim needs a separate justified local restriction. At the time of this inspection, neither that relaxed theorem nor the new exact-six theorem was assumed proved.

## A two-position bonus at the current scale

Restrict the first test to the last-six-directions suffix of each current graph edge. The suffix starts at $t=r+3$, so its outer centres are $r+4$ and $r+8$. Let $D_r$ be 1 when that suffix matches either permitted orientation of the clipped tuple, and 0 otherwise. This is only notation for the occurrence indicator; no implementation definition is proposed here.

Under the exact-six exclusion,

$$D_r\leq e_{r+4}+e_{r+8}.$$

For $0\leq r<m-8$, the two fixed shifts lie on the path. Applying `shifted_prefix_sum_le` separately with offsets 4 and 8 gives

$$\sum_{r<m-8}D_r\leq2\sum_{i=0}^{m}e_i.$$

Therefore, at the current coefficient 120 on counts, a bonus of 60 per matching suffix occurrence has a valid candidate accounting:

$$60\sum_rD_r\leq120\sum_i e_i.$$

The coefficient 60 uses the two-position support. Charging an arbitrary five-position support would give the weaker coefficient 24. If both possible five-count placements within a nine-transition edge are credited, their outer positions are $r+3,r+7$ and $r+4,r+8$; the unrestricted union has four shifts. The simple overlap bound then supports coefficient 30, not 60. The proposed first experiment should keep the suffix placement only. Multiple descriptions or orientations of one occurrence must not be counted repeatedly without an additional multiplicity argument.

## Boundary accounting must preserve the excess

The existing `Weights98.actual_weight_bound` replaces the entering clipped count by the true count immediately. That estimate loses the distinction needed to add a window excess bonus. Reuse its share-credit inequality while keeping its count term exactly $120b_{r+8}$.

The boundary loss 21 survives clipping at 6. Both endpoint lower bounds 4 remain valid; positivity remains valid; and an adjacent-pair lower bound $\alpha_i+\alpha_{i+1}\geq4$ implies $b_i+b_{i+1}\geq4$. Thus the existing generic `GlobalCharge98.discarded_counts`, instantiated with clipped counts, yields

$$\sum_{r<m-8}b_{r+8}+21\leq\sum_{i=0}^{m}b_i.$$

Write $C_r$ for the existing maximum of applicable share credits. Its proved bound gives $\sum_rC_r\leq5\sum_i\sigma_{12}(x_i)$. Combining that bound, the clipped boundary inequality, and the two-position excess inequality gives

$$\sum_{r<m-8}\bigl(120b_{r+8}+C_r+60D_r\bigr)+2520
\leq120\sum_i\alpha_i+5\sum_i\sigma_{12}(x_i).$$

The existing global charge theorem then yields the same total constant as the current model:

$$\sum_{r<m-8}\bigl(w_r+60D_r\bigr)+4200m\leq1098960.$$

This derivation is conditional on the new local excess inequality and the unchanged per-window floor premises. It is an algebraic proof outline, not a newly compiled Lean result. The concrete missing integration is short: the clipped-count instance of `discarded_counts`, two shifted excess sums, and reassembly with the existing share maximum. Prefer the already imported 73/98 generic lemmas over importing an entire older seven-centre proof environment.

An excess bonus may be added to the existing share maximum because the above argument budgets it from omitted true counts. It cannot be justified by merely appending a term to the old `actual_weight_bound`, nor by adding several share alternatives that charge the same five shares.

## Shortest useful next test and limitations

First evaluate, as an explicitly conditional finite experiment, bonus 60 on only the full keys whose last six directions and last five symbols match this tuple or its reversal. Use the current retained full direction/history/count keys and preserve the current weights elsewhere. Check both profiles before investing in a proof. If even this optimistic conditional credit leaves the completed comparison unchanged, certifying this isolated excess rule has low immediate value for the bound.

If the conditional finite experiment improves the completed comparison, the next local test is the explicit exact-six model above. An UNSAT result must acquire a checked contradiction and semantic transfer before the bonus becomes a theorem. A SAT result would give a zero-excess model of those local constraints, so that encoding would not establish the proposed inference. It would not produce a full snake.

Milestone 82's old obstruction applied to an attaining cycle whose six stored symbols were all below 6. Milestone 110 removed one of its edges. The surviving completed-profile cycle now has saturated symbols, so the old displayed witness does not automatically obstruct this experiment. However, the current conditional-profile replacement cycle still has every symbol below 6. An excess-only bonus vanishes on that cycle and cannot raise its minimum mean on the otherwise unchanged graph. Other completed-profile cycles may also remain limiting. Both limitations must be checked before claiming useful global pressure.

## Selected source pins

| Source | SHA 256 |
| --- | --- |
|50 `lean/TripleDemand.lean`|`2f9d9db03dea4fc8aadc4e97bbdcd72fdccea08be34d4f697e6e6f033f4a3400`|
|41 `lean/JointExcess.lean`|`5f0c52c2931ed35fa8e48456f56773a289f2b61556902e3cc1a64a7bd83a8b2a`|
|31 `lean/WeightedExcess.lean`|`8000fdf350a473e7710bfb08d77892018406fae13e61f69373ca5abf5ca6d922`|
|51 `lean/JointChargeBudget.lean`|`e71b022eed40a98c492cd49b21dde593b4ce4df285038c0370498e0900cbc59d`|
|73 `bridge/lean/FiveCentreOverlap.lean`|`c52008307937d17905342de3d7a7f7f6515243f7ec225d0ca2cb1fc1810e54a8`|
|98 `lean/GlobalCharge98.lean`|`3bce11e1fcbb19c51385c0def17617f3ffc87ea4c23ed16c95fef3fee10cdc29`|
