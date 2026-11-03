# Prior inspection for the all-four count test

This is a bounded read-only inspection of archived evidence and the saved milestone112 cycles. No solver or Lean compiler was run. The search covered the relevant milestone72 critical-window/probe records, milestone73 and97 share-catalogue records, the exact milestone85 reference union, milestone107's older-root map, and the count probes in milestones110–112. It does not establish absence from every historical branch or archive.

## Exact targets and cycle alignment

The canonical direction word $012034$ has vertices

$$[0,1,3,7,6,14,30].$$

The all-four target is $(4,4,4,4,4)$, with total $20$, middle $4$ and outer sum $16$. A box in which all five counts are at most $4$ contains this exact target, so refuting the box is a stronger exclusion. Neither conclusion follows from a bound that the total is at least $20$: equality remains possible.

The conditional four-cycle in `112/data/expanded24/results.json` has a different equality tuple. Both of its $012034$ suffixes normalize to

$$ (4,3,4,5,4),\qquad \alpha_{\mathrm{middle}}=4,\qquad
\alpha_{\mathrm{outer},1}+\alpha_{\mathrm{outer},2}+\alpha_{\mathrm{outer},3}+\alpha_{\mathrm{outer},4}=16.$$

| Original edge | Direction/history/code | Raw six-transition suffix | Orientation to $012034$ | Normalized counts |
|---|---|---|---|---|
|1817939|$(179,68,20427)$|$(3,1,0,4,5,0)$|Reverse; forward canonical word is $012342$|$(4,3,4,5,4)$|
|4453322|$(460,0,35559)$|$(3,4,5,3,2,0)$|Forward|$(4,3,4,5,4)$|

For edge1817939, the forward counts are $(4,5,4,3,4)$; reversing the directions requires reversing these counts as well. The identical normalized tuple also occurs at the first fitting placement on edge734051, reversed, and edge3409325, forward. Thus all four edges contain this target window, although only two contain it at the suffix placement where excess credit is awarded.

These calculations decode the six symbols in most-significant-digit order. A placement $s\in\{0,1\}$ takes directions $D[s+2:s+8]$ and count symbols $b[s:s+5]$. Both displayed tuples contain only symbols below $6$, so all their counts are exact. An all-counts-at-most-$4$ exclusion misses the conditional tuple because it contains a $5$. The broader test with middle at most $4$ and outer sum at most $16$ covers both cycle targets.

## Archived occurrence and exclusion evidence

Milestone72 already records both tuples in its abstract critical-graph window census:

| Zero-based row in `critical-current/data/windows.json` | Counts | Recorded occurrences | Component identifier |
|---:|---|---:|---:|
|42|$(4,4,4,4,4)$|80|223218|
|66|$(3,4,4,4,4)$|72|223218|
|72|$(4,4,4,4,3)$|70|223218|
|91|$(3,4,4,4,3)$|62|223218|
|116|$(4,3,4,5,4)$|54|174146|

These entries are extracted from finite graph components by `critical.py`. They are not selected vertex sets, local SAT witnesses or complete snakes. The saved probe target list did not include rows42 or116, and the inspected probe directory has no matching positive witness.

The exact1378-key reference union contains122 entries with this six-transition shape. Neither target tuple is among them. A direct finite scan also found no matching shorter reference key at any fitting subwindow of either target, in either orientation. The nearest displayed entry to the conditional target is index281, with exact tuple $(4,3,4,5,3)$; this does not exclude $(4,3,4,5,4)$. Exact count exclusions cannot be extended to larger count values without a new argument. The small older-root alternatives recorded in milestone107 contain no root for the full $012034$ shape. Consequently that143-key alternative map supplies no direct reusable full-window core for either target.

The more recent relevant count probes are:

| Saved test | Status | Consequence for this task |
|---|---|---|
|112: unrestricted total at most19 on $012034$|Native UNSAT, zero cycle cuts, 7.25 seconds|Supports a candidate total lower bound20; both target tuples attain equality. No checked certificate is recorded for this sum test.|
|112: unrestricted total at most20|UNKNOWN, zero cycle cuts|Would cover both target tuples if eventually refuted.|
|112: middle at most4 and outer sum at most16|UNKNOWN, zero cycle cuts, about15 seconds|The narrow common sum test covering both targets.|
|110: exact $(4,5,5,2,4)$ and $(5,5,4,2,5)$|Native UNSAT, zero cuts|Different count cells; no direct implication for the targets.|
|111: exact $(3,6,5,2,3)$, $(5,6,3,2,5)$, $(3,4,4,5,3)$ and $(4,4,3,5,4)$|Native UNSAT, zero cuts|Related cells, with no recorded implication for all-four or $(4,3,4,5,4)$.|

No matching positive selected-set witness was found in these inspected records. This limited search does not prove that either target is locally impossible.

## Related proof infrastructure and important distinctions

The milestone72 `pysat2-cap19` certificate and milestone73 case7302 concern a **share** lower bound20 on the same shape. Its extra clauses include empty-edge and share-cap constraints. It is not the newer total-of-five-counts test with the same number19 in its filename. Replaying that share certificate would not directly refute an all-four count tuple. The archived countfree completed catalogue does not supply a completed $012034$ count exclusion, and the milestone97 floor-sensitivity files are graph-weight calculations rather than local counterexamples.

The directly reusable proof infrastructure is milestone112's ordinary-counter soundness and multiplicity-preserving sum-counter adapter. The six-transition window here has the same length as the certified $012314$ example, but its coordinate word and corner lists differ. A fresh semantic check must use $[0,1,3,7,6,14,30]$ and its own counter metadata. The specialized `SumGeometry112.actual_outer_sum` theorem is for $012314$ and cannot be reused unchanged as a theorem about $012034$; its normalization/count-equality proof pattern can be adapted after obtaining the exact local contradiction.

## Bounded recommendation

Keep the parent-planned exact-all-four and all-upper-four tests separate, preserving their different scopes. If either succeeds, it attacks the completed six-cycle. To test the conditional cycle within the same route, the smallest additional cell is exact $012034/(4,3,4,5,4)$, including the corresponding reversed representation. A successful exact-cell result would justify revisiting the already saved middle-at-most-$4$, outer-at-most-$16$ family, which could remove both types of equality window with one count-sum statement.

There is also a conditional arithmetic reduction: if a checked total lower bound20 and an exact-all-four exclusion are both available, then all-five-counts-at-most-$4$ is impossible. Indeed, its total is at most20, and equality forces every count to equal4. The currently saved total19 probe is native evidence only, so this reduction cannot yet replace the missing checked premises. No related archived core found in this inspection permits skipping a new exact semantic or contradiction check.

## Evidence pins

| Evidence | SHA256 |
|---|---|
|112 expanded profile/cycles|`b43006b67b1faea4b0c0c93cabe156641d4857ae1836aab81259519c695508d5`|
|59 direction model|`2334325d650cc9b71c0c6ab836183cecd4f1fc4d8b6555f63211592a22a0e2bf`|
|72 critical windows|`26a26cc441c0f24eff1e7440d6af79ecaad5f2acf37fadefa5726eebac450b8a`|
|85 reference union|`dea948631bbccd4c81a1b590dfeeb7f606bd44fc664861f7667b6d041e267289`|
|107 older alternatives|`553f52717a9a30741fc1a655bd4c9046450a0ffae44f1c2f3d06471c96f14d00`|
|112 total19 count probe|`58279638ad42b6a828d8df3da4f6434eb2fc481197ef08fd9058c5a25a32d7ed`|
|112 total20 count probe|`da4199fe0d5a8b89226bb92eb930c93d931ec71c4e2a54ada8357b5108e1f8e0`|
|112 middle4/outer16 probe|`77bd9a83cc185852cd79c715fd787b6d6f21f682d3bc98671120fdb496c4ba84`|
|72 cap19 **share** certificate metadata|`9078c80d966f475a947971368e48989124ba939343e77c09fde115f1e323f179`|

This inspection establishes the identities and scopes of the archived records. It supplies no new local exclusion, solver result, Lean theorem or global upper bound.
