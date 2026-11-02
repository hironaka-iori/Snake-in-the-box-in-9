# Shared budget for outer-four and total-five deficits

`lean/SumBudget112.lean` passed Lean 4.19.0 on its first attempt in 13.469 seconds. All seven printed theorems use only `propext`, `Classical.choice`, and `Quot.sound`. The module imports only `Mathlib.Tactic`, introduces no definitions or types, and contains no proof placeholders or native decision shortcuts. Local count-sum inequalities remain explicit hypotheses throughout.

## Existing interfaces inspected

The inspected sources were milestone 31's `WeightedExcess.lean`, milestone 41's `JointExcess.lean` and `SumExcess.lean`, milestone 42's `CommonBudget.lean`, milestone 51's `JointChargeBudget.lean` and `WindowShareBudget.lean`, milestone 73's `FiveCentreOverlap.lean`, and milestone 98's `GlobalCharge98.lean`.

They already establish weighted support overlap, fixed shifted-sum bounds, maximum combination for alternatives, and the boundary loss of 21. None directly states the requested combination of four outer positions and one middle position with capacities $a,b$. Importing the older seven-position charge interfaces would also introduce unnecessary legacy dependencies. The new module therefore reuses the short shifted-sum argument from milestone 41 in its own namespace and adapts the generic milestone 98 boundary proof directly to clipped counts. Both source hashes are pinned in the receipt.

## Checked statements

Use the existing notation $c_i=\min(6,\alpha_i)$ and $e_i=\alpha_i-c_i$. These are explanatory abbreviations only; no new Lean definitions were added. At suffix position $r$, the four outer positions are $r+4,r+5,r+7,r+8$, and the middle position is $r+6$.

The namespace is `Snake9.SumBudget112`.

1. `weighted_max` proves that, if $d_4\le E_4$ and $d_5\le E_4+E_1$, then

   $$\max(a d_4,\min(a,b)d_5)\le aE_4+bE_1.$$

2. `local_deficits` derives these deficit premises from explicit actual-count lower bounds $L_4$ on the outer four counts and $L_5$ on all five counts. The deficits use natural subtraction from the corresponding clipped-count sums. The result bounds their weighted maximum by

   $$a(e_{r+4}+e_{r+5}+e_{r+7}+e_{r+8})+b e_{r+6}.$$

3. `shifted_sum_le` bounds a sum over an arbitrary finite set of shifted positions by the total nonnegative sum, provided all shifted indices lie in that range. Its argument is the existing injective-image proof from milestone 41.

4. `weighted_window_budget` applies that lemma separately at the five fixed offsets. For arbitrary nonnegative credit satisfying the preceding pointwise weighted bound, and $4a+b\le120$, it proves

   $$\sum_{r<m-8}\mathrm{credit}_r\le120\sum_{i=0}^{m}e_i.$$

   Its range statement also covers $m<9$, when the window range is empty. It charges each of the four outer shifts once and the middle shift once, with their respective coefficients.

5. `combined_deficit_budget` composes the local and summed statements. Its two lower-bound functions may vary with $r$, but every selected bound is an explicit premise at every fitting window. Inapplicable bounds may be zero. Multiple valid alternatives within a category may first be combined by maximum, using the usual `max_le` fact; the theorem does not add alternative deficits together.

6. `clipped_boundary` proves

   $$\sum_{r<m-8}c_{r+8}+21\le\sum_{i=0}^{m}c_i$$

   from $m\ge8$, endpoint bounds $\alpha_0,\alpha_m\ge4$, internal positivity, and adjacent internal count sums at least 4. Clipping at 6 preserves these assumptions. The proof keeps the discarded first eight positions and final endpoint exactly as in milestone 98.

7. `clipped_charge_budget` combines that boundary with any credit satisfying the total excess budget:

   $$120\sum_{r<m-8}c_{r+8}+\sum_{r<m-8}\mathrm{credit}_r+2520
   \le120\sum_{i=0}^{m}\alpha_i.$$

   The identity $c_i+e_i=\alpha_i$ is proved inside the argument. This preserves the excess needed for the new credit instead of first replacing each entering clipped count by its full count.

## Coefficients and limits

The coefficients are fixed natural numbers. For example, $(a,b)=(24,24)$ permits coefficient 24 on both deficit types; $(27,12)$ permits outer coefficient 27 and total coefficient 12; $(30,0)$ recovers the outer-only coefficient 30 and permits no total-five credit. The condition $4a+b\le120$ prevents using both unrestricted coefficients 30 and 24 from the same excess budget.

These theorems concern the suffix placement only. Crediting both placements requires a new overlap calculation. They combine excess alternatives by maximum and leave the existing share contribution separate. They contain no graph direction matching, certificate lookup, count-sum refutation, or actual-snake geometry. Instantiation with actual counts must supply the local lower bounds, existing endpoint and pair bounds, and the independent share-credit premises. No new total constant or upper bound for snakes is asserted by this module alone.

## Check and provenance

The checker is `scripts/check_budget.py`. It took a fresh process snapshot immediately before launch. The recorded snapshot contained one other Lean process, milestone 104 PID 31308, with 186,597,376 bytes of private memory, below the 8 GiB gate. An earlier read-only observation had seen its predecessor; the receipt contains the launch-time observation. The checker used no unsupported memory-limit flag, imposed a 120-second timeout, and launched only this module. No failure or retry occurred. Milestone 104 was not altered or interrupted.

The receipt pins the direct Mathlib source and object, package manifest, Lean and Lake executables, both reused proof sources, the checker, and the immutable source/checker snapshots. It is not a rebuild or hash audit of every transitive Mathlib dependency.

| Artifact | SHA-256 |
|---|---|
|`lean/SumBudget112.lean`|`1581ec791726928ff778d491a31dd0e5c8e219d57f07683d289c3913ce8a9d64`|
|`build/SumBudget112.olean`|`b497839ee963f4104431d549e1d57dd300b5d53b5a88ebd5e754e8330cdf9199`|
|`scripts/check_budget.py`|`fdb0b1d8e1b0a4182d3ee03867de2d70f6044f37592652ffa49c7b44e04b0f86`|
|`logs/SumBudget112-1793658663317802500.log`|`04ba58149c7867a38100baee815f57978bbae091de39e858649e60a7d7d74225`|
|`data/SumBudget112-audit.json`|`e889af4429c8de2b5534dc6c79eed99f105c79cbdecf80981d164c93884af13e`|

The exact theorem signatures and all hypotheses are in the source; the seven axiom reports and execution details are preserved in the log and receipt.
