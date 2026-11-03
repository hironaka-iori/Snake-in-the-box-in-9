# Checked pair-sum geometric transfer

`Snake9.PairGeometry113.actual_pair_sum` passed Lean 4.19.0 on its first attempt in approximately 12.766 seconds. The module introduces no definitions or types and contains no `sorry`, `admit` or `native_decide`.

For a snake $p$ with $m$ transitions, it assumes a fitting six-transition window beginning at $r$, with $r+6\le m$ and canonical directions $012034$. The actual count hypotheses are

$$\alpha_{r+2}\le5,\qquad\alpha_{r+3}\le4,\qquad\alpha_{r+4}\le5.$$

Its conclusion is

$$9\le\alpha_{r+1}+\alpha_{r+5}.$$

The theorem retains an explicit local contradiction argument `hlocal`. This argument must exclude local assignments satisfying the existing `Axioms` for the normalized window $[0,1,3,7,6,14,30]$, centre bounds

$$[(0,21),(0,5),(0,4),(0,5),(0,21)],$$

and the inequality

$$\operatorname{absentCorners}(S,1,0,1)+\operatorname{absentCorners}(S,14,3,4)\le8.$$

No concrete SAT contradiction is imported or claimed by this helper. The two counted centres are the first and fifth internal centres of the window, not endpoints of the complete snake.

The proof follows the checked normalization argument in milestone 112. `actual_canonical_frame` and `mkPerm_spec` supply a coordinate permutation matching the canonical word. The three supplied caps and universal bound $21$ instantiate `frame_axioms`. Two uses of `JointTags.frame_count`, at internal indices $0$ and $4$, identify the local absent-corner counts with actual counts at $r+1$ and $r+5$. The computed normalized vertices and step directions are checked by kernel reduction. Assuming the desired lower bound fails gives a sum at most $8$, contradicting `hlocal`.

The checker uses milestone 112's audited environment and pins its inherited receipt hashes. It separately verifies the direct `CanonicalExclusions`, `JointCountBridge` and resolved `LocalWindowTags` objects against existing source/object/log evidence. The compiler gate permits at most one other Lean process with aggregate private memory below 8 GiB. It started one compiler only, recorded immutable source/checker snapshots and the process inventory, and released its slot after the successful terminal result. Milestone 104 and all prior sources were preserved.

The single printed audit is `Snake9.PairGeometry113.actual_pair_sum`, using only `propext`, `Classical.choice` and `Quot.sound`.

| Artifact | SHA256 |
|---|---|
|`lean/PairGeometry113.lean`|`91242537197f531629b1a3d144770e6234363561b530ccff1e41926fdb78fdb5`|
|`build-pair-geometry/PairGeometry113.olean`|`15a21d75bdc45e9255cb4ab332befcf56e097e0662dd4354c5979bb537766d6c`|
|Successful log|`2b7dd9b4614a48e7e1d00b59556c15035e2e90e8e4c017c9b8adc24d46e1e97d`|
|`data/PairGeometry113-audit.json`|`4f9693eea6ee0b5c444bea836fe9118db7f6ced8c8a9b5912a6f1c33aab12a22`|

This transfer becomes a concrete actual-snake inequality once the exact `hlocal` argument is supplied by the parent certificate. It does not establish a reversed numeric guard, graph deletion, additional excess charge or global upper bound.
